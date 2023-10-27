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

use crate::error::Error;
use crate::compile::*;
use crate::assemble::AsmMnemonic::*;

use super::{GeneratorState, ExprType, FlagsState};

impl<'a> GeneratorState<'a> {
    pub(crate) fn generate_arithm(&mut self, l: &ExprType, op: &Operation, r: &ExprType,  pos: usize, high_byte: bool) -> Result<ExprType, Error>
    {
        let mut acc_in_use = self.acc_in_use;
        debug!("Arithm: {:?},{:?},{:?}", l, op, r);    
        let left;
        let right;

        match op {
            Operation::Sub(_) | Operation::Div(_) => {
                left = l; right = r;
            },
            _ => {
                match r {
                    ExprType::A(_) => {
                        left = r; right = l;
                    },
                    _ => {
                        left = l; right = r;
                    }
                }
            }
        }

        let x;
        let right2 = match right {
            ExprType::A(s) => {
                if self.tmp_in_use {
                    return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                }
                self.asm(STA, &ExprType::Tmp(*s), pos, false)?;
                acc_in_use = false;
                self.tmp_in_use = true;
                x = ExprType::Tmp(*s);
                &x
            },
            _ => {
                right
            }
        };

        let signed;
        match left {
            ExprType::Immediate(l) => {
                match right {
                    ExprType::Immediate(r) => {
                        match op {
                            Operation::Add(_) => return Ok(ExprType::Immediate(l + r)),
                            Operation::Sub(_) => return Ok(ExprType::Immediate(l - r)),
                            Operation::And(_) => return Ok(ExprType::Immediate(l & r)),
                            Operation::Or(_) => return Ok(ExprType::Immediate(l | r)),
                            Operation::Xor(_) => return Ok(ExprType::Immediate(l ^ r)),
                            Operation::Mul(_) => return Ok(ExprType::Immediate(l * r)),
                            Operation::Div(_) => return Ok(ExprType::Immediate(l / r)),
                            _ => { return Err(Error::Unimplemented { feature: "arithmetics is partially implemented" }); },
                        } 
                    },
                    _ => {
                        if acc_in_use { self.sasm(PHA)?; }
                        self.asm(LDA, left, pos, high_byte)?;
                        signed = false;
                    }
                };
            },
            ExprType::Absolute(variable, eight_bits, off) => {
                let v = self.compiler_state.get_variable(variable);
                if let ExprType::Immediate(r) = right2 {
                    if v.var_type == VariableType::CharPtr && !*eight_bits && v.var_const {
                        match op {
                            Operation::Add(_) => return Ok(ExprType::Absolute(variable.clone(), *eight_bits, *off + *r)),
                            Operation::Sub(_) => return Ok(ExprType::Absolute(variable.clone(), *eight_bits, *off - *r)),
                            Operation::And(_) => if *r == 255 {
                                if high_byte {
                                    return Ok(ExprType::Immediate(0));
                                } else {
                                    return Ok(ExprType::Absolute(variable.clone(), true, *off));
                                }
                            },
                            _ => (),
                        } 
                    } else if v.var_type == VariableType::Short && !*eight_bits {
                        match op {
                            Operation::And(_) => if *r == 255 {
                                if high_byte {
                                    return Ok(ExprType::Immediate(0));
                                } else {
                                    return Ok(ExprType::Absolute(variable.clone(), true, *off));
                                }
                            },
                            _ => (),
                        } 
                    }
                }
                if acc_in_use { self.sasm(PHA)?; }
                self.asm(LDA, left, pos, high_byte)?;
                signed = v.signed;
            },
            ExprType::AbsoluteX(s) | ExprType::AbsoluteY(s) => {
                let v = self.compiler_state.get_variable(s);
                signed = v.signed;
                if acc_in_use { self.sasm(PHA)?; }
                self.asm(LDA, left, pos, high_byte)?;
            },
            ExprType::Tmp(s) => {
                if acc_in_use { self.sasm(PHA)?; }
                self.asm(LDA, left, pos, high_byte)?;
                self.tmp_in_use = false;
                signed = *s;
            },
            ExprType::X => {
                if acc_in_use { self.sasm(PHA)?; }
                self.sasm(TXA)?;
                signed = false;
            },
            ExprType::Y => {
                if acc_in_use { self.sasm(PHA)?; }
                self.sasm(TYA)?;
                signed = false;
            },
            ExprType::A(s) => {
                acc_in_use = false;
                signed = *s;
            },
            _ => { return Err(Error::Unimplemented { feature: "arithmetics is partially implemented" }); },
        }
        self.acc_in_use = true;
        let operation = match op {
            Operation::Add(_) => {
                if !high_byte {
                    self.sasm(CLC)?;
                }
                self.carry_flag_ok = false;
                // Carry propagation error detection
                if self.carry_propagation_error && high_byte {
                    return Err(self.compiler_state.syntax_error("Carry propagation too complex for the compiler. Please introduce temp variables to simplify your calculations", pos))
                }
                self.carry_propagation_error = high_byte;
                ADC
            },
            Operation::Sub(_) => {
                if !high_byte {
                    self.sasm(SEC)?;
                }
                self.carry_flag_ok = true;
                // Carry propagation error detection
                if self.carry_propagation_error && high_byte {
                    return Err(self.compiler_state.syntax_error("Carry propagation too complex for the compiler. Please introduce temp variables to simplify your calculations", pos))
                }
                self.carry_propagation_error = high_byte;
                SBC
            },
            Operation::And(_) => {
                AND
            },
            Operation::Or(_) => {
                ORA
            },
            Operation::Xor(_) => {
                EOR
            },
            Operation::Mul(_) => { return Err(self.compiler_state.syntax_error("Operation not possible. 6502 doesn't implement a multiplier.", pos)) },
            Operation::Div(_) => { return Err(self.compiler_state.syntax_error("Operation not possible. 6502 doesn't implement a divider.", pos)) },
            _ => { return Err(Error::Unimplemented { feature: "arithmetics is partially implemented" }); },
        };
        match right2 {
            ExprType::Immediate(v) => {
                if high_byte || operation != AND || *v != 0xff {
                    if *v != 0 || operation == AND || high_byte { 
                        self.asm(operation, right2, pos, high_byte)?; 
                    };
                }
            },
            ExprType::Absolute(_, _, _) | ExprType::AbsoluteX(_) | ExprType::AbsoluteY(_) => {
                self.asm(operation, right2, pos, high_byte)?;
            },
            ExprType::X => {
                if self.tmp_in_use {
                    return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                }
                self.asm(STX, &ExprType::Tmp(false), pos, high_byte)?;
                self.asm(operation, &ExprType::Tmp(false), pos, high_byte)?;
            },
            ExprType::Y => {
                if self.tmp_in_use {
                    return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                }
                self.asm(STY, &ExprType::Tmp(false), pos, high_byte)?;
                self.asm(operation, &ExprType::Tmp(false), pos, high_byte)?;
            },
            ExprType::Tmp(_) => {
                self.asm(operation, right2, pos, high_byte)?;
                self.tmp_in_use = false;
            },
            _ => { return Err(Error::Unimplemented { feature: "arithmetics is partially implemented" }); },
        };
        if acc_in_use {
            self.asm(STA, &ExprType::Tmp(false), pos, high_byte)?;
            self.sasm(PLA)?;
            if self.tmp_in_use {
                return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
            }
            self.tmp_in_use = true;
            self.flags = FlagsState::Unknown;
            self.carry_flag_ok = false;
            Ok(ExprType::Tmp(signed))
        } else {
            self.acc_in_use = true;
            self.flags = FlagsState::A;
            Ok(ExprType::A(signed))
        }
    }

    pub(crate) fn generate_shift(&mut self, left: &ExprType, op: &Operation, right: &ExprType, pos: usize, high_byte: bool) -> Result<ExprType, Error>
    {
        let mut acc_in_use = self.acc_in_use;
        let signed;
        match left {
            ExprType::Immediate(l) => {
                match right {
                    ExprType::Immediate(r) => {
                        match op {
                            Operation::Brs(_) => return Ok(ExprType::Immediate(l >> r)),
                            Operation::Bls(_) => return Ok(ExprType::Immediate(l << r)),
                            _ => unreachable!(),
                        } 
                    },
                    _ => return Err(self.compiler_state.syntax_error("Incorrect right value for shift operation (constants only)", pos))
                };
            },
            ExprType::Absolute(varname, eight_bits, offset) => {
                let v = self.compiler_state.get_variable(varname);
                if (v.var_type == VariableType::Short || v.var_type == VariableType::ShortPtr || v.var_type == VariableType::CharPtr || v.var_type == VariableType::CharPtrPtr) && *op == Operation::Brs(false) && !eight_bits {
                    // Special shift 8 case for extracting higher byte
                    match right {
                        ExprType::Immediate(value) => {
                            if *value == 8 {
                                if v.var_type == VariableType::CharPtr && !eight_bits {
                                    if acc_in_use { self.sasm(PHA)?; }
                                    signed = self.asm(LDA, left, pos, true)?;
                                    self.flags = FlagsState::Unknown;
                                    if acc_in_use {
                                        self.asm(STA, &ExprType::Tmp(signed), pos, false)?;
                                        self.sasm(PLA)?;
                                        if self.tmp_in_use {
                                            return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                                        }
                                        self.tmp_in_use = true;
                                        return Ok(ExprType::Tmp(signed));
                                    } else {
                                        self.acc_in_use = true;
                                        return Ok(ExprType::A(signed));
                                    }
                                } else {
                                    return Ok(ExprType::Absolute(varname.clone(), true, offset + v.size as i32));
                                }
                            } else {
                                return Err(self.compiler_state.syntax_error("Incorrect right value for right shift operation on short (constant 8 only supported)", pos));
                            } 
                        },
                        _ => return Err(self.compiler_state.syntax_error("Incorrect right value for right shift operation on short (constant 8 only supported)", pos))
                    };
                } else {
                    if let ExprType::Immediate(value) = right {
                        if *value == 8 && *op == Operation::Bls(false) {
                            if high_byte {
                                if acc_in_use { self.sasm(PHA)?; }
                                signed = self.asm(LDA, left, pos, false)?;
                                self.flags = FlagsState::Unknown;
                                if acc_in_use {
                                    self.asm(STA, &ExprType::Tmp(signed), pos, false)?;
                                    self.sasm(PLA)?;
                                    if self.tmp_in_use {
                                        return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                                    }
                                    self.tmp_in_use = true;
                                    return Ok(ExprType::Tmp(signed));
                                } else {
                                    self.acc_in_use = true;
                                    return Ok(ExprType::A(signed));
                                }
                            } else {
                                return Ok(ExprType::Immediate(0));
                            }
                        }
                    }
                    if acc_in_use { self.sasm(PHA)?; }
                    signed = self.asm(LDA, left, pos, false)?;
                }
            },
            ExprType::AbsoluteX(varname) | ExprType::AbsoluteY(varname) => {
                let v = self.compiler_state.get_variable(varname);
                if (v.var_type == VariableType::ShortPtr || v.var_type == VariableType::CharPtrPtr) && *op == Operation::Brs(false) {
                    // Special shift 8 case for extracting higher byte
                    match right {
                        ExprType::Immediate(value) => {
                            if *value == 8 {
                                if acc_in_use { self.sasm(PHA)?; }
                                signed = self.asm(LDA, left, pos, true)?;
                                self.flags = FlagsState::Unknown;
                                if acc_in_use {
                                    self.asm(STA, &ExprType::Tmp(signed), pos, false)?;
                                    self.sasm(PLA)?;
                                    if self.tmp_in_use {
                                        return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                                    }
                                    self.tmp_in_use = true;
                                    return Ok(ExprType::Tmp(signed));
                                } else {
                                    self.acc_in_use = true;
                                    return Ok(ExprType::A(signed));
                                }
                            } else {
                                return Err(self.compiler_state.syntax_error("Incorrect right value for right shift operation on short (constant 8 only supported)", pos));
                            } 
                        },
                        _ => return Err(self.compiler_state.syntax_error("Incorrect right value for right shift operation on short (constant 8 only supported)", pos))
                    };
                } else {
                    if let ExprType::Immediate(value) = right {
                        if *value == 8 && *op == Operation::Bls(false) {
                            if high_byte {
                                if acc_in_use { self.sasm(PHA)?; }
                                signed = self.asm(LDA, left, pos, false)?;
                                self.flags = FlagsState::Unknown;
                                if acc_in_use {
                                    self.asm(STA, &ExprType::Tmp(signed), pos, false)?;
                                    self.sasm(PLA)?;
                                    if self.tmp_in_use {
                                        return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                                    }
                                    self.tmp_in_use = true;
                                    return Ok(ExprType::Tmp(signed));
                                } else {
                                    self.acc_in_use = true;
                                    return Ok(ExprType::A(signed));
                                }
                            } else {
                                return Ok(ExprType::Immediate(0));
                            }
                        }
                    }
                    if acc_in_use { self.sasm(PHA)?; }
                    signed = self.asm(LDA, left, pos, false)?;
                }
            },
            ExprType::X => {
                if acc_in_use { self.sasm(PHA)?; }
                signed = false;
                self.sasm(TXA)?;
            },
            ExprType::Y => {
                if acc_in_use { self.sasm(PHA)?; }
                signed = false;
                self.sasm(TYA)?;
            },
            ExprType::A(s) => { 
                acc_in_use = false;
                signed = *s; 
            },
            ExprType::Tmp(s) => {
                if acc_in_use { self.sasm(PHA)?; }
                signed = *s;
                self.tmp_in_use = false;
                self.asm(LDA, left, pos, false)?;
            },
            _ => return Err(self.compiler_state.syntax_error("Bad left value for shift operation", pos))
        }
        self.acc_in_use = true;
        let operation = match op {
            Operation::Brs(_) => {
                LSR
            },
            Operation::Bls(_) => {
                ASL
            },
            _ => unreachable!(),
        };
        match right {
            ExprType::Immediate(v) => {
                if *v >= 0 && *v <= 7 {
                    if signed && operation == LSR {
                        if *v == 1 {
                            self.asm(CMP, &ExprType::Immediate(0x80), pos, false)?;
                            self.sasm(ROR)?;
                        } else {
                            for _ in 0..*v {
                                self.sasm(LSR)?;
                            }
                            self.sasm(CLC)?;
                            let mask = -128 >> *v;
                            self.asm(ADC, &ExprType::Immediate(mask), pos, false)?;
                            self.asm(EOR, &ExprType::Immediate(mask), pos, false)?;
                        }
                    } else {
                        for _ in 0..*v {
                            self.sasm(operation)?;
                        }
                    }
                } else if *v < 0 {
                    return Err(self.compiler_state.syntax_error("Negative shift operation not allowed", pos));
                } else if *v == 8 {
                    return Err(self.compiler_state.syntax_error("Operation too complex for the compiler. Please use an intermediate variable", pos));
                } else {
                    return Ok(ExprType::Immediate(0));
                }
            },
            _ => return Err(self.compiler_state.syntax_error("Incorrect right value for shift operation (positive constants only)", pos))
        };
        self.flags = FlagsState::Unknown;
        if acc_in_use {
            self.asm(STA, &ExprType::Tmp(signed), pos, false)?;
            self.sasm(PLA)?;
            if self.tmp_in_use {
                return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
            }
            self.tmp_in_use = true;
            Ok(ExprType::Tmp(signed))
        } else {
            self.acc_in_use = true;
            Ok(ExprType::A(signed))
        }
    }

    pub(crate) fn generate_plusplus(&mut self, expr_type: &ExprType, pos: usize, plusplus: bool) -> Result<ExprType, Error>
    {
        let operation = if plusplus { INC } else { DEC };
        match expr_type {
            ExprType::X => {
                if plusplus {
                    self.sasm(INX)?;
                } else {
                    self.sasm(DEX)?;
                }
                self.flags = FlagsState::X;
                Ok(ExprType::X)
            },
            ExprType::Y => {
                if plusplus {
                    self.sasm(INY)?;
                } else {
                    self.sasm(DEY)?;
                }
                self.flags = FlagsState::Y;
                Ok(ExprType::Y)
            },
            ExprType::Absolute(variable, eight_bits, offset) => {
                let v = self.compiler_state.get_variable(variable);
                let use_inc = match v.memory {
#[cfg(feature = "atari2600")]
                    VariableMemory::Superchip | VariableMemory::MemoryOnChip(_) => false,
                    _ => *eight_bits,
                }; 
                if use_inc {
                    self.asm(operation, expr_type, pos, false)?;
                    self.flags = FlagsState::Absolute(variable.clone(), *eight_bits, *offset);
                    self.carry_flag_ok = false;
                    Ok(ExprType::Absolute(variable.clone(), *eight_bits, *offset))
                } else {
                    // Implment optimization for inc on pointers
                    if v.var_type == VariableType::Short || (v.var_type == VariableType::CharPtr && !eight_bits) {
// Implement optimized 16 bits increment:
//        inc     ptr
//        bne     :+
//        inc     ptr+1
//+       rts
                        if plusplus {
                            self.local_label_counter_if += 1;
                            let ifend_label = format!(".ifend{}", self.local_label_counter_if);
                            self.asm(INC, expr_type, pos, false)?;
                            self.asm(BNE, &ExprType::Label(ifend_label.clone()), 0, false)?;
                            self.asm(INC, expr_type, pos, true)?;
                            self.label(&ifend_label)?;
                            self.flags = FlagsState::Absolute(variable.clone(), *eight_bits, *offset);
                            self.carry_flag_ok = false;
                        } else {
// Decrement :
//      LDA NUML
//      BNE LABEL
//      DEC NUMH
//LABEL DEC NUML 
                            self.local_label_counter_if += 1;
                            let ifend_label = format!(".ifend{}", self.local_label_counter_if);
                            if self.acc_in_use {
                                self.sasm(PHA)?; 
                            }
                            self.asm(LDA, expr_type, pos, false)?;
                            self.asm(BNE, &ExprType::Label(ifend_label.clone()), 0, false)?;
                            self.asm(DEC, expr_type, pos, true)?;
                            self.label(&ifend_label)?;
                            self.asm(DEC, expr_type, pos, false)?;
                            self.flags = FlagsState::Unknown;
                            self.carry_flag_ok = false;
                            if self.acc_in_use {
                                self.sasm(PLA)?; 
                            }
                        }
                        Ok(ExprType::Absolute(variable.clone(), *eight_bits, *offset))
                    } else {
                        let op = if plusplus { Operation::Add(false) } else { Operation::Sub(false) };
                        let right = ExprType::Immediate(1);
                        let newright = self.generate_arithm(expr_type, &op, &right, pos, false)?;
                        let ret = self.generate_assign(expr_type, &newright, pos, false);
                        if v.var_type == VariableType::Short || (v.var_type == VariableType::CharPtr && !eight_bits) {
                            let newright = self.generate_arithm(expr_type, &op, &right, pos, true)?;
                            self.generate_assign(expr_type, &newright, pos, true)?;
                        }
                        ret
                    }
                }
            },
            ExprType::AbsoluteX(variable) => {
                self.asm(operation, expr_type, pos, false)?;
                self.flags = FlagsState::AbsoluteX(variable.clone());
                Ok(ExprType::AbsoluteX(variable.clone()))
            },
            ExprType::AbsoluteY(_) => {
                let op = if plusplus { Operation::Add(false) } else { Operation::Sub(false) };
                let right = ExprType::Immediate(1);
                let newright = self.generate_arithm(expr_type, &op, &right, pos, false)?;
                self.generate_assign(expr_type, &newright, pos, false)
            },
            _ => {
                if plusplus {
                    Err(self.compiler_state.syntax_error("Bad left value used with ++ operator", pos))
                } else {
                    Err(self.compiler_state.syntax_error("Bad left value used with -- operator", pos))
                }
            },
        }
    }

    pub(crate) fn generate_neg(&mut self, expr: &Expr, pos: usize, high_byte: bool) -> Result<ExprType, Error>
    {
        match expr {
            Expr::Integer(i) => Ok(ExprType::Immediate(-*i)),
            _ => {
                let left = ExprType::Immediate(0);
                let right = self.generate_expr(expr, pos, high_byte, false)?;
                self.generate_arithm(&left, &Operation::Sub(false), &right, pos, high_byte) 
            }
        }
    }

    pub(crate) fn generate_not(&mut self, expr: &Expr, pos: usize) -> Result<ExprType, Error>
    {
        match expr {
            Expr::Integer(i) => if *i != 0 {
                Ok(ExprType::Immediate(0))
            } else {
                Ok(ExprType::Immediate(1))
            },
            _ => {
                if self.acc_in_use {
                    if self.tmp_in_use {
                        return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                    }
                    self.sasm(PHA)?; 
                    self.local_label_counter_if += 1;
                    let ifend_label = format!(".ifend{}", self.local_label_counter_if);
                    let else_label = format!(".else{}", self.local_label_counter_if);
                    self.generate_condition(expr, pos, false, &else_label, false)?;
                    self.asm(LDA, &ExprType::Immediate(1), pos, false)?;
                    self.asm(JMP, &ExprType::Label(ifend_label.clone()), pos, false)?;
                    self.label(&else_label)?;
                    self.asm(LDA, &ExprType::Immediate(0), pos, false)?;
                    self.label(&ifend_label)?;
                    self.asm(STA, &ExprType::Tmp(false), pos, false)?;
                    self.sasm(PLA)?;
                    Ok(ExprType::Tmp(false))
                } else {
                    self.local_label_counter_if += 1;
                    let ifend_label = format!(".ifend{}", self.local_label_counter_if);
                    let else_label = format!(".else{}", self.local_label_counter_if);
                    let cond = self.generate_condition(expr, pos, false, &else_label, true)?;
                    if let Some(b) = cond {
                        Ok(ExprType::Immediate(if b {0} else {1}))
                    } else {
                        self.asm(LDA, &ExprType::Immediate(1), pos, false)?;
                        self.asm(JMP, &ExprType::Label(ifend_label.clone()), pos, false)?;
                        self.label(&else_label)?;
                        self.asm(LDA, &ExprType::Immediate(0), pos, false)?;
                        self.label(&ifend_label)?;
                        self.acc_in_use = true;
                        Ok(ExprType::A(false))
                    }
                }
            }
        }
    }

    pub(crate) fn generate_bnot(&mut self, expr: &Expr, pos: usize) -> Result<ExprType, Error>
    {
        match expr {
            Expr::Integer(i) => Ok(ExprType::Immediate(!*i)),
            _ => { 
                let left = self.generate_expr(expr, pos, false, false)?;
                let right = ExprType::Immediate(0xff);
                self.generate_arithm(&left, &Operation::Xor(false), &right, pos, false)
            },
        }
    }

    pub(crate) fn generate_sign_extend(&mut self, expr: ExprType, pos: usize) -> Result<ExprType, Error>
    {
        if self.acc_in_use { self.sasm(PHA)?; }
        #[cfg(constant_time)]
        {
            self.sasm(PHP)?;
            self.asm(LDA, &expr, pos, false)?;
            self.asm(ASL, &ExprType::Nothing, pos, false)?;  
            self.asm(LDA, &ExprType::Immediate(0), pos, false)?;
            self.asm(ADC, &ExprType::Immediate(0xFF), pos, false)?;
            self.asm(EOR, &ExprType::Immediate(0xff), pos, false)?;
            self.sasm(PLP)?;
        }
        #[cfg(not(constant_time))]
        {
            self.asm(LDA, &expr, pos, false)?;
            self.local_label_counter_if += 1;
            let ifneg_label = format!(".ifneg{}", self.local_label_counter_if);
            self.asm(ORA, &ExprType::Immediate(0x7F), pos, false)?;
            self.asm(BMI, &ExprType::Label(ifneg_label.clone()), 0, false)?;
            self.asm(LDA, &ExprType::Immediate(0), pos, false)?;
            self.label(&ifneg_label)?;
        }
        self.flags = FlagsState::Unknown;
        if self.acc_in_use {
            self.asm(STA, &ExprType::Tmp(false), pos, false)?;
            self.sasm(PLA)?;
            if self.tmp_in_use {
                return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
            }
            self.tmp_in_use = true;
            Ok(ExprType::Tmp(true))
        } else {
            self.acc_in_use = true;
            Ok(ExprType::A(true))
        }
    }

}
