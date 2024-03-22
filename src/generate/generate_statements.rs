/*
    cc6502 - a subset of C compiler for the 6502 processor
    Copyright (C) 2023 Bruno STEUX

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.

    Contact info: bruno.steux@gmail.com
*/

use log::debug;

use crate::assemble::AsmMnemonic::*;
use crate::compile::*;
use crate::error::Error;

use super::{ExprType, FlagsState, GeneratorState};

impl<'a> GeneratorState<'a> {
    fn purge_deferred_plusplus_and_savey(&mut self) -> Result<(), Error> {
        if self.saved_y {
            self.asm_restore_y();
            self.saved_y = false;
            self.tmp_in_use = false;
            self.flags = FlagsState::Y;
            self.carry_flag_ok = false;
        }

        let def = self.deferred_plusplus.clone();
        self.deferred_plusplus.clear();
        for d in def {
            self.generate_plusplus(&d.0, d.1, d.2)?;
        }
        Ok(())
    }

    fn generate_included_source_code_line(&mut self, loc: usize) -> Option<&'a str> {
        let mut start_of_line = self.last_included_char.clone();
        let mut start_of_line_pos = self.last_included_position;
        if self.last_included_position < loc {
            // Let's find the line including loc
            while self.last_included_position < loc {
                let c = self.last_included_char.next();
                c?;
                let c = c.unwrap();
                self.last_included_position += 1;
                if c == '\n' {
                    self.last_included_line_number += 1;
                    start_of_line = self.last_included_char.clone();
                    start_of_line_pos = self.last_included_position;
                }
            }
            // Ok, we have found loc. Let's go to the end of line
            loop {
                let c = self.last_included_char.next();
                if c.is_none() {
                    return Some(start_of_line.as_str());
                }
                let c = c.unwrap();
                self.last_included_position += 1;
                if c == '\n' {
                    self.last_included_line_number += 1;
                    return Some(
                        &start_of_line.as_str()
                            [0..(self.last_included_position - start_of_line_pos)],
                    );
                }
            }
        }
        None
    }

    fn generate_function_call(
        &mut self,
        expr: &Expr,
        params: &Expr,
        pos: usize,
    ) -> Result<ExprType, Error> {
        match expr {
            Expr::Identifier(var, sub) => {
                match sub.as_ref() {
                    Expr::Nothing => {
                        match self.compiler_state.functions.get(var) {
                            None => Err(self
                                .compiler_state
                                .syntax_error("Unknown function identifier", pos)),
                            Some(f) => {
                                if self.acc_in_use {
                                    self.sasm(PHA)?;
                                }
                                if self.tmp_in_use {
                                    self.asm(LDA, &ExprType::Tmp(false), pos, false)?;
                                    self.sasm(PHA)?;
                                }

                                // It's not necessary anymore to push anythign on the stack for
                                // saving (due to the use ot the calling tree for variables
                                // declarations non overlap). It can be even faulty in case of
                                // parameter overwritting (use of &)
                                /*
                                // Push all necessary local variables onto stack
                                let mut nb_to_push = 0;
                                {
                                    let fx = &self.current_function;
                                    if let Some(fxx) = fx {
                                        if let Some(f) = self.compiler_state.functions.get(fxx) {
                                            nb_to_push = f.stack_frame_size;
                                        }
                                    }
                                }
                                if f.stack_frame_size < nb_to_push {
                                    nb_to_push = f.stack_frame_size;
                                }
                                for i in 0..nb_to_push {
                                    self.generate_asm_statement(&format!("LDA LOCAL_VARIABLES+{}", i), Some(2))?;
                                    self.sasm(PHA)?;
                                }
                                */

                                // Load parameters
                                {
                                    let mut p = params.clone();
                                    let mut param_iter = f.parameters.iter();
                                    loop {
                                        let param: &Expr;
                                        let next: Option<&Expr>;
                                        if let Expr::BinOp { lhs, op, rhs } = &p {
                                            if *op == Operation::Comma {
                                                param = &*lhs;
                                                next = Some(&*rhs);
                                            } else {
                                                param = &p;
                                                next = None;
                                            }
                                        } else {
                                            param = &p;
                                            next = None;
                                        }
                                        if let Expr::Nothing = *param {
                                            break;
                                        }
                                        // Well, there is ACTUALLY a parameter provided
                                        // Let's see what is the requested parameter
                                        if let Some(requested_param) = param_iter.next() {
                                            let s = format!("{var}_{requested_param}");
                                            let ex = Expr::BinOp {
                                                lhs: Box::new(Expr::Identifier(
                                                    s,
                                                    Box::new(Expr::Nothing),
                                                )),
                                                op: Operation::Assign,
                                                rhs: Box::new(param.clone()),
                                            };
                                            debug!("Parameter: {:?}", ex);
                                            self.generate_expr(&ex, pos, false, false)?;
                                        } else {
                                            return Err(self.compiler_state.syntax_error(
                                                "Too many parameters provided in function call",
                                                pos,
                                            ));
                                        }
                                        if let Some(x) = next {
                                            p = x.clone();
                                        } else {
                                            break;
                                        }
                                    }
                                    if let Some(_) = param_iter.next() {
                                        return Err(self.compiler_state.syntax_error(
                                            "Not enough parameters provided in function call",
                                            pos,
                                        ));
                                    }
                                }

                                debug!("Function call from bank #{}; {}", self.current_bank, var);
                                if f.interrupt {
                                    return Err(self
                                        .compiler_state
                                        .syntax_error("Can't call an interrupt routine", pos));
                                }
                                if f.inline {
                                    if f.code.is_some() {
                                        self.push_code(var, pos)?;
                                    } else {
                                        return Err(self
                                            .compiler_state
                                            .syntax_error("Undefined function", pos));
                                    }
                                } else if f.bank == self.current_bank
                                    || self.bankswitching_scheme == "3EP"
                                    || (self.bankswitching_scheme == "SuperGame" && f.bank == 0)
                                {
                                    self.asm(JSR, &ExprType::Label(var.clone()), pos, false)?;
                                } else if self.bankswitching_scheme == "3E" {
                                    if self.current_bank == 0 {
                                        // Generate bankswitching call
                                        self.asm(
                                            LDA,
                                            &ExprType::Immediate((f.bank - 1) as i32),
                                            pos,
                                            false,
                                        )?;
                                        self.asm(
                                            STA,
                                            &ExprType::Absolute("ROM_SELECT".into(), true, 0),
                                            pos,
                                            false,
                                        )?;
                                        self.asm(JSR, &ExprType::Label(var.clone()), pos, false)?;
                                    } else {
                                        return Err(self.compiler_state.syntax_error("Banked code can only be called from bank 0 or same bank", pos));
                                    }
                                } else if self.current_bank == 0 {
                                    // Generate bankswitching call
                                    if self.bankswitching_scheme == "SuperGame" {
                                        self.asm(
                                            LDA,
                                            &ExprType::Immediate((f.bank - 1) as i32),
                                            pos,
                                            false,
                                        )?;
                                        self.asm(
                                            STA,
                                            &ExprType::Absolute("ROM_SELECT".into(), true, 0),
                                            pos,
                                            false,
                                        )?;
                                        self.asm(JSR, &ExprType::Label(var.clone()), pos, false)?;
                                    } else {
                                        self.asm(
                                            JSR,
                                            &ExprType::Label(format!("Call{}", *var)),
                                            pos,
                                            false,
                                        )?;
                                    }
                                } else {
                                    return Err(self.compiler_state.syntax_error(
                                        "Banked code can only be called from bank 0 or same bank",
                                        pos,
                                    ));
                                }

                                // Note this function in the call tree
                                let fx = &self.current_function;
                                if let Some(f) = fx {
                                    if let Some(v) = self.functions_call_tree.get_mut(f) {
                                        v.push(var.to_string());
                                    } else {
                                        let mut v = Vec::new();
                                        v.push(var.to_string());
                                        self.functions_call_tree.insert(f.clone(), v);
                                    }
                                }

                                self.flags = FlagsState::Unknown;
                                // Manage return value
                                let mut return_tmp = false;
                                if f.return_type.is_some() {
                                    if self.tmp_in_use {
                                        return Err(self.compiler_state.syntax_error(
                                            "Code too complex for the compiler",
                                            pos,
                                        ));
                                    }
                                    if self.acc_in_use
                                    /*|| nb_to_push != 0*/
                                    {
                                        self.asm(STA, &ExprType::Tmp(f.return_signed), pos, false)?;
                                        if self.acc_in_use {
                                            self.sasm(PLA)?;
                                        }
                                        self.tmp_in_use = true;
                                        return_tmp = true;
                                    }
                                }

                                // It's also not necessary to pull any variable from stack
                                /*
                                // Pop local variables from stack
                                for i in 0..nb_to_push {
                                    self.sasm(PLA)?;
                                    self.generate_asm_statement(&format!("STA LOCAL_VARIABLES+{}", nb_to_push - 1 - i), Some(2))?;
                                }
                                */

                                if f.return_type.is_some() {
                                    return if return_tmp {
                                        Ok(ExprType::Tmp(f.return_signed))
                                    } else {
                                        Ok(ExprType::A(f.return_signed))
                                    };
                                }
                                if self.tmp_in_use {
                                    self.sasm(PLA)?;
                                    self.asm(STA, &ExprType::Tmp(false), pos, false)?;
                                }
                                if self.acc_in_use {
                                    self.sasm(PLA)?;
                                }
                                Ok(ExprType::Nothing)
                            }
                        }
                    }
                    _ => Err(self
                        .compiler_state
                        .syntax_error("No subscript allowed here", pos)),
                }
            }
            _ => Err(self
                .compiler_state
                .syntax_error("Function call on something else than a function", pos)),
        }
    }

    fn generate_deref(&mut self, expr: &Expr, pos: usize) -> Result<ExprType, Error> {
        match expr {
            Expr::Identifier(var, sub) => {
                let v = self.compiler_state.get_variable(var);
                if v.var_type == VariableType::CharPtr {
                    let sub_output = self.generate_expr(sub, pos, false, false)?;
                    match sub_output {
                        ExprType::Nothing => {
                            if v.var_const {
                                Ok(ExprType::Absolute(var.clone(), true, 0))
                            } else {
                                // We have to use indirect addressing for this deref
                                if self.tmp_in_use {
                                    Err(self
                                        .compiler_state
                                        .syntax_error("Code too complex for the compiler", pos))
                                } else {
                                    if !self.saved_y {
                                        if self.warnings.iter().any(|s| s == "all" || s == "perf") {
                                            self.compiler_state
                                                .warning("Performance hit. Y has to be saved", pos);
                                        }
                                        self.asm(STY, &ExprType::Tmp(false), pos, false)?;
                                        self.saved_y = true;
                                        self.tmp_in_use = true;
                                    }
                                    self.asm(LDY, &ExprType::Immediate(0), pos, false)?;
                                    Ok(ExprType::AbsoluteY(var.into()))
                                }
                            }
                        }
                        _ => Err(self
                            .compiler_state
                            .syntax_error("No subscript is allowed in this context", pos)),
                    }
                } else {
                    Err(self
                        .compiler_state
                        .syntax_error("Deref on something else than a pointer", pos))
                }
            }
            _ => Err(self
                .compiler_state
                .syntax_error("Deref only works on pointers", pos)),
        }
    }

    fn generate_addr(&mut self, expr: &Expr, pos: usize) -> Result<ExprType, Error> {
        match expr {
            Expr::Identifier(var, sub) => {
                let v = self.compiler_state.get_variable(var);
                if v.var_type == VariableType::Char {
                    let sub_output = self.generate_expr(sub, pos, false, false)?;
                    match sub_output {
                        ExprType::Nothing => Ok(ExprType::Absolute(var.clone(), false, 0)),
                        _ => Err(self
                            .compiler_state
                            .syntax_error("No subscript is allowed in this context", pos)),
                    }
                } else {
                    Err(self
                        .compiler_state
                        .syntax_error("& only works on char (8 bits) variables", pos))
                }
            }
            _ => Err(self
                .compiler_state
                .syntax_error("& only works on char (8 bits) variables", pos)),
        }
    }

    fn generate_sizeof(&mut self, expr: &Expr, pos: usize) -> Result<ExprType, Error> {
        match expr {
            Expr::Type(s) => {
                if s.contains("*") {
                    Ok(ExprType::Immediate(2))
                } else if s == "char" {
                    Ok(ExprType::Immediate(1))
                } else if s == "short" || s == "short int" || s == "int" {
                    Ok(ExprType::Immediate(2))
                } else {
                    Err(self
                        .compiler_state
                        .syntax_error("Sizeof only works on variables and simple types", pos))
                }
            }
            Expr::Identifier(var, _) => {
                let v = self.compiler_state.get_variable(var);
                match v.var_type {
                    VariableType::CharPtr => {
                        if v.var_const {
                            Ok(ExprType::Immediate(v.size as i32))
                        } else {
                            Ok(ExprType::Immediate(2))
                        }
                    }
                    VariableType::ShortPtr | VariableType::CharPtrPtr => {
                        Ok(ExprType::Immediate((v.size * 2) as i32))
                    }
                    VariableType::Char => Ok(ExprType::Immediate(1)),
                    VariableType::Short => Ok(ExprType::Immediate(2)),
                }
            }
            _ => Err(self
                .compiler_state
                .syntax_error("Sizeof only works on variables and simple types", pos)),
        }
    }

    pub(crate) fn generate_expr(
        &mut self,
        expr: &Expr,
        pos: usize,
        high_byte: bool,
        second_time: bool,
    ) -> Result<ExprType, Error> {
        debug!("Expression: {:?}, high_byte: {}", expr, high_byte);
        match expr {
            Expr::Integer(i) => Ok(ExprType::Immediate(*i)),
            Expr::BinOp { lhs, op, rhs } => match op {
                Operation::Assign => {
                    let left = self.generate_expr(lhs, pos, high_byte, high_byte)?;
                    let right = self.generate_expr(rhs, pos, high_byte, high_byte)?;
                    let ret = self.generate_assign(&left, &right, pos, high_byte);
                    if self.saved_y {
                        self.asm_restore_y();
                        self.saved_y = false;
                        self.tmp_in_use = false;
                        self.flags = FlagsState::Y;
                        self.carry_flag_ok = false;
                    }
                    if !high_byte {
                        match left {
                            ExprType::Absolute(_, eight_bits, _) => {
                                if !eight_bits {
                                    let left = self.generate_expr(lhs, pos, true, true)?;
                                    let right = self.generate_expr(rhs, pos, true, true)?;
                                    self.generate_assign(&left, &right, pos, true)?;
                                }
                            }
                            ExprType::AbsoluteX(variable) | ExprType::AbsoluteY(variable) => {
                                let v = self.compiler_state.get_variable(&variable);
                                if v.var_type == VariableType::ShortPtr
                                    || v.var_type == VariableType::CharPtrPtr
                                {
                                    let left = self.generate_expr(lhs, pos, true, true)?;
                                    let right = self.generate_expr(rhs, pos, true, true)?;
                                    self.generate_assign(&left, &right, pos, true)?;
                                }
                            }
                            _ => (),
                        };
                    }
                    ret
                }
                Operation::Add(false)
                | Operation::Sub(false)
                | Operation::And(false)
                | Operation::Or(false)
                | Operation::Xor(false)
                | Operation::Mul(false)
                | Operation::Div(false) => {
                    let left = self.generate_expr(lhs, pos, high_byte, high_byte)?;
                    let right = self.generate_expr(rhs, pos, high_byte, high_byte)?;
                    self.generate_arithm(&left, op, &right, pos, high_byte)
                }
                Operation::Add(true)
                | Operation::Sub(true)
                | Operation::And(true)
                | Operation::Or(true)
                | Operation::Xor(true)
                | Operation::Mul(true)
                | Operation::Div(true) => {
                    let left = self.generate_expr(lhs, pos, high_byte, high_byte)?;
                    let right = self.generate_expr(rhs, pos, high_byte, high_byte)?;
                    let newright = self.generate_arithm(&left, op, &right, pos, high_byte)?;
                    let ret = self.generate_assign(&left, &newright, pos, high_byte);
                    if !high_byte {
                        match left {
                            ExprType::Absolute(variable, eight_bits, _) => {
                                let v = self.compiler_state.get_variable(&variable);
                                if v.var_type == VariableType::Short
                                    || v.var_type == VariableType::ShortPtr
                                    || (v.var_type == VariableType::CharPtr && !eight_bits)
                                {
                                    let left = self.generate_expr(lhs, pos, true, true)?;
                                    let right = self.generate_expr(rhs, pos, true, true)?;
                                    let newright =
                                        self.generate_arithm(&left, op, &right, pos, true)?;
                                    self.generate_assign(&left, &newright, pos, true)?;
                                }
                            }
                            ExprType::AbsoluteX(variable) | ExprType::AbsoluteY(variable) => {
                                let v = self.compiler_state.get_variable(&variable);
                                if v.var_type == VariableType::ShortPtr
                                    || v.var_type == VariableType::CharPtrPtr
                                {
                                    let left = self.generate_expr(lhs, pos, true, true)?;
                                    let right = self.generate_expr(rhs, pos, true, true)?;
                                    let newright =
                                        self.generate_arithm(&left, op, &right, pos, true)?;
                                    self.generate_assign(&left, &newright, pos, true)?;
                                }
                            }
                            _ => (),
                        };
                    }
                    ret
                }
                Operation::Eq
                | Operation::Neq
                | Operation::Gt
                | Operation::Gte
                | Operation::Lt
                | Operation::Lte
                | Operation::Land
                | Operation::Lor => self.generate_expr_cond(expr, pos),
                Operation::Bls(true) | Operation::Brs(true) => {
                    let left = self.generate_expr(lhs, pos, false, second_time)?;
                    let right = self.generate_expr(rhs, pos, false, second_time)?;
                    if !high_byte {
                        if let ExprType::Absolute(varname, eight_bits, _) = &left {
                            let v = self.compiler_state.get_variable(varname);
                            if v.var_type == VariableType::Short && !eight_bits {
                                if let ExprType::Immediate(value) = right {
                                    if value < 8 {
                                        return self.generate_shift_16bits(&left, op, &right, pos);
                                    }
                                }
                            }
                        }
                        if let ExprType::AbsoluteX(varname) = &left {
                            let v = self.compiler_state.get_variable(varname);
                            if v.var_type == VariableType::ShortPtr {
                                if let ExprType::Immediate(value) = right {
                                    if value < 8 {
                                        return self.generate_shift_16bits(&left, op, &right, pos);
                                    }
                                }
                            }
                        }
                    }
                    let newright = self.generate_shift(&left, op, &right, pos, high_byte)?;
                    self.generate_assign(&left, &newright, pos, false)
                }
                Operation::Bls(false) | Operation::Brs(false) => {
                    let left = self.generate_expr(lhs, pos, false, second_time)?;
                    let right = self.generate_expr(rhs, pos, false, second_time)?;
                    self.generate_shift(&left, op, &right, pos, high_byte)
                }
                Operation::TernaryCond1 => self.generate_ternary(lhs, rhs, pos),
                Operation::TernaryCond2 => Err(self
                    .compiler_state
                    .syntax_error("Unexpected ':'. Probably a ';' typo", pos)),
                Operation::Comma => {
                    self.generate_expr(lhs, pos, false, false)?;
                    self.purge_deferred_plusplus_and_savey()?;
                    self.acc_in_use = false;
                    self.tmp_in_use = false;
                    self.generate_expr(rhs, pos, false, false)
                }
            },
            Expr::Identifier(var, sub) => match var.as_str() {
                "X" => {
                    if high_byte {
                        Ok(ExprType::Immediate(0))
                    } else {
                        Ok(ExprType::X)
                    }
                }
                "Y" => {
                    if high_byte {
                        Ok(ExprType::Immediate(0))
                    } else {
                        Ok(ExprType::Y)
                    }
                }
                variable => {
                    let v = self.compiler_state.get_variable(variable);
                    let dummy = if let Expr::Nothing = **sub {
                        None
                    } else {
                        self.dummy()
                    };
                    let tmp_in_use = self.tmp_in_use;
                    let sub_output = self.generate_expr(sub, pos, false, second_time)?;
                    match sub_output {
                        ExprType::Nothing => {
                            if let VariableDefinition::Value(VariableValue::Int(val)) = &v.def {
                                Ok(ExprType::Immediate(*val))
                            } else if high_byte && v.var_type == VariableType::Char && v.signed {
                                self.generate_sign_extend(
                                    ExprType::Absolute(
                                        variable.into(),
                                        v.var_type == VariableType::Char,
                                        0,
                                    ),
                                    pos,
                                )
                            } else {
                                Ok(ExprType::Absolute(
                                    variable.into(),
                                    v.var_type == VariableType::Char,
                                    0,
                                ))
                            }
                        }
                        ExprType::X => {
                            if v.var_type != VariableType::Char && v.var_type != VariableType::Short
                            {
                                if high_byte && v.var_type == VariableType::CharPtr && v.signed {
                                    self.generate_sign_extend(
                                        ExprType::AbsoluteX(variable.into()),
                                        pos,
                                    )
                                } else {
                                    Ok(ExprType::AbsoluteX(variable.into()))
                                }
                            } else {
                                Err(self
                                    .compiler_state
                                    .syntax_error("Subscript not allowed on variables", pos))
                            }
                        }
                        ExprType::Y => {
                            if v.var_type != VariableType::Char && v.var_type != VariableType::Short
                            {
                                if high_byte && v.var_type == VariableType::CharPtr && v.signed {
                                    self.generate_sign_extend(
                                        ExprType::AbsoluteY(variable.into()),
                                        pos,
                                    )
                                } else {
                                    Ok(ExprType::AbsoluteY(variable.into()))
                                }
                            } else {
                                Err(self
                                    .compiler_state
                                    .syntax_error("Subscript not allowed on variables", pos))
                            }
                        }
                        ExprType::Immediate(val) => {
                            if v.var_type != VariableType::Char
                                && v.var_type != VariableType::Short
                                && v.var_const
                            {
                                if high_byte && v.var_type == VariableType::CharPtr && v.signed {
                                    self.generate_sign_extend(
                                        ExprType::Absolute(variable.into(), true, val),
                                        pos,
                                    )
                                } else {
                                    Ok(ExprType::Absolute(
                                        variable.into(),
                                        v.var_type != VariableType::CharPtrPtr
                                            && v.var_type != VariableType::ShortPtr,
                                        val,
                                    ))
                                }
                            } else {
                                if tmp_in_use || self.tmp_in_use || self.saved_y {
                                    Err(self
                                        .compiler_state
                                        .syntax_error("Code too complex for the compiler", pos))
                                } else if let Some(dummy_pos) = dummy {
                                    self.tmp_in_use = true;
                                    if self.warnings.iter().any(|s| s == "all" || s == "perf") {
                                        self.compiler_state
                                            .warning("Performance hit. Y has to be saved", pos);
                                    }
                                    self.asm_save_y(dummy_pos);
                                    self.asm(LDY, &sub_output, pos, false)?;
                                    self.saved_y = true;
                                    Ok(ExprType::AbsoluteY(variable.into()))
                                } else {
                                    Err(self
                                        .compiler_state
                                        .syntax_error("Code too complex for the compiler", pos))
                                }
                            }
                        }
                        _ => {
                            if tmp_in_use || self.tmp_in_use || self.saved_y {
                                Err(self
                                    .compiler_state
                                    .syntax_error("Code too complex for the compiler", pos))
                            } else if let Some(dummy_pos) = dummy {
                                self.tmp_in_use = true;
                                if self.warnings.iter().any(|s| s == "all" || s == "perf") {
                                    self.compiler_state
                                        .warning("Performance hit. Y has to be saved", pos);
                                }
                                self.asm_save_y(dummy_pos);
                                self.asm(LDY, &sub_output, pos, false)?;
                                self.saved_y = true;
                                Ok(ExprType::AbsoluteY(variable.into()))
                            } else {
                                Err(self
                                    .compiler_state
                                    .syntax_error("Code too complex for the compiler", pos))
                            }
                        }
                    }
                }
            },
            Expr::FunctionCall(expr, params) => self.generate_function_call(expr, params, pos),
            Expr::MinusMinus(expr, false) => {
                let expr_type = self.generate_expr(expr, pos, high_byte, high_byte)?;
                if !second_time {
                    self.generate_plusplus(&expr_type, pos, false)?;
                }
                Ok(expr_type)
            }
            Expr::PlusPlus(expr, false) => {
                let expr_type = self.generate_expr(expr, pos, high_byte, high_byte)?;
                if !second_time {
                    self.generate_plusplus(&expr_type, pos, true)?;
                }
                Ok(expr_type)
            }
            Expr::MinusMinus(expr, true) => {
                let expr_type = self.generate_expr(expr, pos, high_byte, high_byte)?;
                if !second_time {
                    self.deferred_plusplus.push((expr_type.clone(), pos, false));
                }
                Ok(expr_type)
            }
            Expr::PlusPlus(expr, true) => {
                let expr_type = self.generate_expr(expr, pos, high_byte, high_byte)?;
                if !second_time {
                    self.deferred_plusplus.push((expr_type.clone(), pos, true));
                }
                Ok(expr_type)
            }
            Expr::Neg(v) => self.generate_neg(v, pos, high_byte),
            Expr::Not(v) => self.generate_not(v, pos),
            Expr::BNot(v) => self.generate_bnot(v, pos),
            Expr::Deref(v) => self.generate_deref(v, pos),
            Expr::Addr(v) => self.generate_addr(v, pos),
            Expr::Sizeof(v) => self.generate_sizeof(v, pos),
            Expr::Nothing => Ok(ExprType::Nothing),
            Expr::TmpId(s) => Ok(ExprType::Absolute(s.clone(), false, 0)),
            Expr::Type(_) => Err(self
                .compiler_state
                .syntax_error("Misplaced variable type", pos)),
        }
    }

    fn generate_for_loop(
        &mut self,
        init: &'a Expr,
        condition: &Expr,
        update: &'a Expr,
        body: &'a StatementLoc<'a>,
        pos: usize,
    ) -> Result<(), Error> {
        self.local_label_counter_for += 1;
        let for_label = format!(".for{}", self.local_label_counter_for);
        let forupdate_label = format!(".forupdate{}", self.local_label_counter_for);
        let forend_label = format!(".forend{}", self.local_label_counter_for);
        self.generate_expr(init, pos, false, false)?;
        self.purge_deferred_plusplus_and_savey()?;
        self.loops
            .push((forupdate_label.clone(), forend_label.clone(), false));
        self.generate_condition(condition, pos, true, &forend_label, false)?;
        self.label(&for_label)?;
        self.generate_statement(body)?;
        self.label(&forupdate_label)?;
        self.generate_expr(update, pos, false, false)?;
        self.purge_deferred_plusplus_and_savey()?;
        self.generate_condition(condition, pos, false, &for_label, false)?;
        self.label(&forend_label)?;
        self.loops.pop();
        Ok(())
    }

    fn generate_while(
        &mut self,
        condition: &Expr,
        body: &'a StatementLoc<'a>,
        pos: usize,
    ) -> Result<(), Error> {
        if let Statement::Expression(Expr::Nothing) = body.statement {
            self.generate_do_while(body, condition, pos)
        } else {
            self.local_label_counter_while += 1;
            let while_label = format!(".while{}", self.local_label_counter_while);
            let whileend_label = format!(".whileend{}", self.local_label_counter_while);
            self.loops
                .push((while_label.clone(), whileend_label.clone(), false));
            self.label(&while_label)?;
            self.generate_condition(condition, pos, true, &whileend_label, false)?;
            self.generate_statement(body)?;
            self.asm(JMP, &ExprType::Label(while_label), pos, false)?;
            self.label(&whileend_label)?;
            self.loops.pop();
            Ok(())
        }
    }

    fn generate_do_while(
        &mut self,
        body: &'a StatementLoc<'a>,
        condition: &Expr,
        pos: usize,
    ) -> Result<(), Error> {
        self.local_label_counter_while += 1;
        let dowhile_label = format!(".dowhile{}", self.local_label_counter_while);
        let dowhilecondition_label = format!(".dowhilecondition{}", self.local_label_counter_while);
        let dowhileend_label = format!(".dowhileend{}", self.local_label_counter_while);
        self.loops.push((
            dowhilecondition_label.clone(),
            dowhileend_label.clone(),
            false,
        ));
        self.label(&dowhile_label)?;
        self.generate_statement(body)?;
        if self.loops.last().unwrap().2 {
            self.label(&dowhilecondition_label)?;
        }
        self.generate_condition(condition, pos, false, &dowhile_label, false)?;
        self.label(&dowhileend_label)?;
        self.loops.pop();
        Ok(())
    }

    fn generate_break(&mut self, pos: usize) -> Result<(), Error> {
        let brk_label;
        {
            brk_label = match self.loops.last() {
                None => {
                    return Err(self
                        .compiler_state
                        .syntax_error("Break statement outside loop", pos))
                }
                Some((_, bl, _)) => bl.clone(),
            };
        }
        self.asm(JMP, &ExprType::Label(brk_label), pos, false)?;
        Ok(())
    }

    fn generate_continue(&mut self, pos: usize) -> Result<(), Error> {
        let cont_label = match self.loops.last() {
            None => {
                return Err(self
                    .compiler_state
                    .syntax_error("Continue statement outside loop", pos))
            }
            Some((cl, _, _)) => {
                if cl.is_empty() {
                    return Err(self
                        .compiler_state
                        .syntax_error("Continue statement outside loop", pos));
                } else {
                    cl.clone()
                }
            }
        };
        self.asm(JMP, &ExprType::Label(cont_label), pos, false)?;
        self.loops.last_mut().unwrap().2 = true;
        Ok(())
    }

    pub fn generate_return(&mut self, expr: &Expr, pos: usize) -> Result<(), Error> {
        if let Some(s) = &self.current_function {
            let f = self.compiler_state.functions.get(s).unwrap();
            if f.interrupt {
                self.sasm(RTI)?;
                return Ok(());
            } else {
                let e = self.generate_expr(expr, pos, false, false)?;
                if f.return_type.is_some() {
                    if e == ExprType::Nothing {
                        return Err(self
                            .compiler_state
                            .syntax_error("Function must return a value", pos));
                    } else {
                        self.generate_assign(&ExprType::A(f.return_signed), &e, pos, false)?;
                    }
                } else {
                    if e != ExprType::Nothing {
                        return Err(self
                            .compiler_state
                            .syntax_error("void function can't return a value", pos));
                    }
                }
            }
            if f.inline {
                self.asm(JMP, &ExprType::Label(".endof".into()), 0, false)?;
            } else {
                self.sasm(RTS)?;
            }
            self.acc_in_use = false;
            self.tmp_in_use = false;
        } else {
            unreachable!();
        }

        Ok(())
    }

    fn generate_asm_statement(&mut self, s: &str, size: Option<u32>) -> Result<(), Error> {
        self.inline(s, size)?;
        Ok(())
    }

    fn generate_goto_statement(&mut self, s: &str) -> Result<(), Error> {
        self.asm(JMP, &ExprType::Label(format!(".{}", s)), 0, false)?;
        Ok(())
    }

    fn generate_strobe_statement(&mut self, expr: &Expr, pos: usize) -> Result<(), Error> {
        match expr {
            Expr::Identifier(name, _) => {
                let v = self.compiler_state.get_variable(name);
                match v.var_type {
                    VariableType::CharPtr => {
                        self.asm(STA, &ExprType::Absolute(name.clone(), true, 0), pos, false)?;
                        Ok(())
                    }
                    _ => Err(self
                        .compiler_state
                        .syntax_error("Strobe only works on memory pointers", pos)),
                }
            }
            _ => Err(self
                .compiler_state
                .syntax_error("Strobe only works on memory pointers", pos)),
        }
    }

    fn generate_csleep_statement(&mut self, cycles: i32, pos: usize) -> Result<(), Error> {
        match cycles {
            2 => self.sasm_protected(NOP)?,
            3 => self.asm(
                STA,
                &ExprType::Absolute("DUMMY".into(), true, 0),
                pos,
                false,
            )?,
            4 => {
                self.sasm_protected(NOP)?;
                self.sasm_protected(NOP)?
            }
            5 => self.asm(
                DEC,
                &ExprType::Absolute("DUMMY".into(), true, 0),
                pos,
                false,
            )?,
            6 => {
                self.sasm_protected(NOP)?;
                self.sasm_protected(NOP)?;
                self.sasm_protected(NOP)?
            }
            7 => {
                self.sasm_protected(PHA)?;
                self.sasm_protected(PLA)?
            }
            8 => {
                self.sasm_protected(NOP)?;
                self.sasm_protected(NOP)?;
                self.sasm_protected(NOP)?;
                self.sasm_protected(NOP)?
            }
            9 => {
                self.asm(
                    DEC,
                    &ExprType::Absolute("DUMMY".into(), true, 0),
                    pos,
                    false,
                )?;
                self.sasm_protected(NOP)?;
                self.sasm_protected(NOP)?
            }
            10 => {
                self.asm(
                    DEC,
                    &ExprType::Absolute("DUMMY".into(), true, 0),
                    pos,
                    false,
                )?;
                self.asm(
                    DEC,
                    &ExprType::Absolute("DUMMY".into(), true, 0),
                    pos,
                    false,
                )?
            }
            _ => {
                return Err(self
                    .compiler_state
                    .syntax_error("Unsupported cycle sleep value", pos))
            }
        };
        Ok(())
    }

    // Load/Store statements are protected, and thus cannot be optmized out
    fn generate_load_store_statement(
        &mut self,
        expr: &ExprType,
        pos: usize,
        load: bool,
    ) -> Result<(), Error> {
        self.protected = true;
        match expr {
            ExprType::X => {
                self.asm(if load { TXA } else { TAX }, &ExprType::Nothing, pos, false)?
            }
            ExprType::Y => {
                self.asm(if load { TYA } else { TAY }, &ExprType::Nothing, pos, false)?
            }
            _ => self.asm(if load { LDA } else { STA }, expr, pos, false)?,
        };
        self.protected = false;
        Ok(())
    }

    pub fn generate_statement(&mut self, code: &'a StatementLoc<'a>) -> Result<(), Error> {
        // Include C source code into generated asm
        // debug!("{:?}, {}, {}, {}", expr, pos, self.last_included_position, self.last_included_line_number);
        if self.insert_code {
            let included_source_code = self.generate_included_source_code_line(code.pos);
            let line_number =
                self.compiler_state.mapped_lines[self.last_included_line_number].1 - 1;
            let line_to_be_written =
                included_source_code.map(|line| format!("(l.{line_number}) {line}"));
            // debug!("{:?}, {}, {}", line_to_be_written, self.last_included_position, self.last_included_line_number);
            if let Some(l) = line_to_be_written {
                // Replace series of whitespaces by a single whitespace
                let mut lx = self.whitespaces_regex.replace_all(&l, " ");
                if lx.len() > 256 {
                    let lxx = lx.to_mut();
                    lxx.truncate(256);
                    lxx.push_str("...\n");
                    self.comment(&lxx)?; // Should include the '\n'
                } else {
                    self.comment(&lx)?; // Should include the '\n'
                }
            }
        }

        self.purge_deferred_plusplus_and_savey()?;

        self.acc_in_use = false;
        self.tmp_in_use = false;

        if let Some(label) = &code.label {
            self.label(&format!(".{}", label))?;
        }

        // Generate different kind of statements
        match &code.statement {
            Statement::Expression(expr) => {
                self.generate_expr(expr, code.pos, false, false)?;
            }
            Statement::Block(statements) => {
                for code in statements {
                    self.generate_statement(code)?;
                }
            }
            Statement::For {
                init,
                condition,
                update,
                body,
            } => {
                self.generate_for_loop(init, condition, update, body.as_ref(), code.pos)?;
            }
            Statement::If {
                condition,
                body,
                else_body,
            } => {
                match else_body {
                    None => self.generate_if(condition, body.as_ref(), None, code.pos)?,
                    Some(ebody) => {
                        self.generate_if(condition, body.as_ref(), Some(ebody.as_ref()), code.pos)?
                    }
                };
            }
            Statement::While { condition, body } => {
                self.generate_while(condition, body.as_ref(), code.pos)?;
            }
            Statement::DoWhile { body, condition } => {
                self.generate_do_while(body.as_ref(), condition, code.pos)?;
            }
            Statement::Switch { expr, cases } => {
                self.generate_switch(expr, cases, code.pos)?;
            }
            Statement::Break => {
                self.generate_break(code.pos)?;
            }
            Statement::Continue => {
                self.generate_continue(code.pos)?;
            }
            Statement::Return(e) => {
                self.generate_return(e, code.pos)?;
            }
            Statement::Asm(s, size) => {
                self.generate_asm_statement(s, *size)?;
            }
            Statement::Strobe(s) => {
                self.generate_strobe_statement(s, code.pos)?;
            }
            Statement::Store(e) => {
                let param = self.generate_expr(e, code.pos, false, false)?;
                self.generate_load_store_statement(&param, code.pos, false)?;
            }
            Statement::Load(e) => {
                let param = self.generate_expr(e, code.pos, false, false)?;
                self.generate_load_store_statement(&param, code.pos, true)?;
            }
            Statement::CSleep(s) => {
                self.generate_csleep_statement(*s, code.pos)?;
            }
            Statement::Goto(s) => {
                self.generate_goto_statement(s)?;
            }
            Statement::LocalVarDecl => (),
        }

        self.purge_deferred_plusplus_and_savey()?;
        Ok(())
    }
}
