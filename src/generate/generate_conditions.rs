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

impl<'a, 'b> GeneratorState<'a> {
    pub fn generate_ternary(&mut self, condition: &Expr, alternatives: &Expr, pos: usize) -> Result<ExprType, Error>
    {
        match alternatives {
            Expr::BinOp {lhs, op, rhs} => {
                if *op == Operation::TernaryCond2 {
                    if self.acc_in_use {
                        self.sasm(PHA)?; 
                        if self.tmp_in_use {
                            return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                        }
                        self.local_label_counter_if += 1;
                        let ifend_label = format!(".ifend{}", self.local_label_counter_if);
                        let else_label = format!(".else{}", self.local_label_counter_if);
                        self.generate_condition(condition, pos, true, &else_label, false)?;
                        let left = self.generate_expr(lhs, pos, false, false)?;
                        let la = self.generate_assign(&ExprType::A(false), &left, pos, false)?;
                        self.asm(JMP, &ExprType::Label(ifend_label.clone()), pos, false)?;
                        self.label(&else_label)?;
                        self.acc_in_use = false;
                        let right = self.generate_expr(rhs, pos, false, false)?;
                        let ra = self.generate_assign(&ExprType::A(false), &right, pos, false)?;
                        self.label(&ifend_label)?;
                        self.asm(STA, &ExprType::Tmp(false), pos, false)?;
                        self.tmp_in_use = true;
                        self.sasm(PLA)?;
                        if la != ra {
                            return Err(self.compiler_state.syntax_error("Different alternative types in ?: expression", pos))
                        }
                        Ok(ExprType::Tmp(false))
                    } else {
                        self.local_label_counter_if += 1;
                        let ifend_label = format!(".ifend{}", self.local_label_counter_if);
                        let else_label = format!(".else{}", self.local_label_counter_if);
                        let cond = self.generate_condition(condition, pos, true, &else_label, true)?;
                        if let Some(b) = cond {
                            if b {
                                return Ok(self.generate_expr(rhs, pos, false, false)?);
                            } else {
                                return Ok(self.generate_expr(lhs, pos, false, false)?);
                            }
                        } else {
                            let left = self.generate_expr(lhs, pos, false, false)?;
                            let la = self.generate_assign(&ExprType::A(false), &left, pos, false)?;
                            self.asm(JMP, &ExprType::Label(ifend_label.clone()), pos, false)?;
                            self.label(&else_label)?;
                            self.acc_in_use = false;
                            let right = self.generate_expr(rhs, pos, false, false)?;
                            let ra = self.generate_assign(&ExprType::A(false), &right, pos, false)?;
                            self.label(&ifend_label)?;
                            self.acc_in_use = true;
                            if la != ra {
                                return Err(self.compiler_state.syntax_error("Different alternative types in ?: expression", pos))
                            }
                            Ok(la)
                        }
                    }
                } else {
                    Err(self.compiler_state.syntax_error("Missing alternatives in ?: expression", pos))
                }
            },
            _ => Err(self.compiler_state.syntax_error("Missing alternatives in ?: expression", pos))
        }
    }

    pub fn generate_expr_cond(&mut self, expr: &Expr, pos: usize) -> Result<ExprType, Error>
    {
        if self.acc_in_use {
            self.sasm(PHA)?; 
            if self.tmp_in_use {
                return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
            }
            self.local_label_counter_if += 1;
            let ifend_label = format!(".ifend{}", self.local_label_counter_if);
            let else_label = format!(".else{}", self.local_label_counter_if);
            self.generate_condition(expr, pos, false, &else_label, false)?;
            self.asm(LDA, &ExprType::Immediate(0), pos, false)?;
            self.asm(JMP, &ExprType::Label(ifend_label.clone()), pos, false)?;
            self.label(&else_label)?;
            self.asm(LDA, &ExprType::Immediate(1), pos, false)?;
            self.label(&ifend_label)?;
            self.asm(STA, &ExprType::Tmp(false), pos, false)?;
            self.tmp_in_use = true;
            self.sasm(PLA)?;
            Ok(ExprType::Tmp(false))
        } else {
            self.local_label_counter_if += 1;
            let ifend_label = format!(".ifend{}", self.local_label_counter_if);
            let else_label = format!(".else{}", self.local_label_counter_if);
            let cond = self.generate_condition(expr, pos, false, &else_label, true)?;
            if let Some(b) = cond {
                Ok(ExprType::Immediate(if b {1} else {0}))
            } else {
                self.asm(LDA, &ExprType::Immediate(0), pos, false)?;
                self.asm(JMP, &ExprType::Label(ifend_label.clone()), pos, false)?;
                self.label(&else_label)?;
                self.asm(LDA, &ExprType::Immediate(1), pos, false)?;
                self.label(&ifend_label)?;
                self.acc_in_use = true;
                Ok(ExprType::A(false))
            }
        }
    }

    fn generate_branch_instruction(&mut self, op: &Operation, signed: bool, label: &str) -> Result<(), Error>
    {
        // Branch instruction
        match op {
            Operation::Neq => {
                self.asm(BNE, &ExprType::Label(label.into()), 0, false)?;
                Ok(())
            },
            Operation::Eq => {
                self.asm(BEQ, &ExprType::Label(label.into()), 0, false)?;
                Ok(())
            },
            Operation::Lt => {
                if signed {
                    self.asm(BMI, &ExprType::Label(label.into()), 0, false)?;
                } else {
                    self.asm(BCC, &ExprType::Label(label.into()), 0, false)?;
                } 
                Ok(())
            },
            Operation::Gt => {
                self.local_label_counter_if += 1;
                let label_here = format!(".ifhere{}", self.local_label_counter_if);
                self.asm(BEQ, &ExprType::Label(label_here.clone()), 0, false)?;
                if signed {
                    self.asm(BPL, &ExprType::Label(label.into()), 0, false)?;
                } else {
                    self.asm(BCS, &ExprType::Label(label.into()), 0, false)?;
                }
                self.label(&label_here)?;
                Ok(())
            },
            Operation::Lte => {
                if signed {
                    self.asm(BMI, &ExprType::Label(label.into()), 0, false)?;
                } else {
                    self.asm(BCC, &ExprType::Label(label.into()), 0, false)?;
                } 
                self.asm(BEQ, &ExprType::Label(label.into()), 0, false)?;
                Ok(())
            },
            Operation::Gte => {
                if signed {
                    self.asm(BPL, &ExprType::Label(label.into()), 0, false)?;
                } else {
                    self.asm(BCS, &ExprType::Label(label.into()), 0, false)?;
                } 
                Ok(())
            },
            _ => Err(Error::Unimplemented { feature: "condition statement is partially implemented" })
        }
    }

    // Alternate compare when CMP is avoided (comparison with 0)
    // In thase case, never use the carry flag : it's probably incorrectly set
    fn generate_branch_instruction_alt(&mut self, op: &Operation, signed: bool, label: &str) -> Result<(), Error>
    {
        // Branch instruction
        match op {
            Operation::Neq => {
                self.asm(BNE, &ExprType::Label(label.into()), 0, false)?;
                Ok(())
            },
            Operation::Eq => {
                self.asm(BEQ, &ExprType::Label(label.into()), 0, false)?;
                Ok(())
            },
            Operation::Lt => {
                self.asm(BMI, &ExprType::Label(label.into()), 0, false)?;
                Ok(())
            },
            Operation::Gt => {
                self.local_label_counter_if += 1;
                let label_here = format!(".ifhere{}", self.local_label_counter_if);
                self.asm(BEQ, &ExprType::Label(label_here.clone()), 0, false)?;
                if signed {
                    self.asm(BPL, &ExprType::Label(label.into()), 0, false)?;
                }
                self.label(&label_here)?;
                Ok(())
            },
            Operation::Lte => {
                if signed {
                    self.asm(BMI, &ExprType::Label(label.into()), 0, false)?;
                }
                self.asm(BEQ, &ExprType::Label(label.into()), 0, false)?;
                Ok(())
            },
            Operation::Gte => {
                self.asm(BPL, &ExprType::Label(label.into()), 0, false)?;
                Ok(())
            },
            _ => Err(Error::Unimplemented { feature: "condition statement is partially implemented" })
        }
    }

    fn generate_condition_16bits(&mut self, l: &ExprType, op: &Operation, r: &ExprType, pos: usize, label: &str) -> Result<(), Error>
    {
        let mut f = ExprType::Nothing;
        let compute_subtraction = if let ExprType::Immediate(v) = r {
            if *v == 0 {
                if *op != Operation::Gte && *op != Operation::Lt {
                    self.generate_assign(&ExprType::Tmp(false), l, pos, false)?;
                }
                f = self.generate_assign(&ExprType::A(true), l, pos, true)?;
                false
            } else { true }
        } else { true };
        if compute_subtraction {
            let e = self.generate_arithm(l, &Operation::Sub(false), r, pos, false)?;
            if e != ExprType::Tmp(false) {
                self.generate_assign(&ExprType::Tmp(false), &e, pos, false)?;
            }
            f = self.generate_arithm(l, &Operation::Sub(false), r, pos, true)?;
        }
        let res = match op {
            Operation::Eq => {
                let ifstart_label = format!(".ifstart{}", self.local_label_counter_if);
                self.local_label_counter_if += 1;
                self.generate_condition_ex(&f, &op, &ExprType::Immediate(0), pos, true, &ifstart_label)?;
                self.generate_condition_ex(&ExprType::Tmp(false), op, &ExprType::Immediate(0), pos, false, label)?;
                self.label(&ifstart_label)
            },
            Operation::Neq => {
                self.generate_condition_ex(&f, &op, &ExprType::Immediate(0), pos, false, label)?;
                self.generate_condition_ex(&ExprType::Tmp(false), op, &ExprType::Immediate(0), pos, false, label)
            },
            Operation::Gt => {
                self.generate_condition_ex(&f, &op, &ExprType::Immediate(0), pos, false, label)?;
                let ifstart_label = format!(".ifstart{}", self.local_label_counter_if);
                self.local_label_counter_if += 1;
                self.generate_condition_ex(&f, &Operation::Eq, &ExprType::Immediate(0), pos, true, &ifstart_label)?;
                self.generate_condition_ex(&ExprType::Tmp(false), &Operation::Neq, &ExprType::Immediate(0), pos, false, label)?;
                self.label(&ifstart_label)
            },
            Operation::Gte | Operation::Lt => {
                self.generate_condition_ex(&f, &op, &ExprType::Immediate(0), pos, false, label)
            },
            Operation::Lte => {
                self.generate_condition_ex(&f, &Operation::Lt, &ExprType::Immediate(0), pos, false, label)?;
                let ifstart_label = format!(".ifstart{}", self.local_label_counter_if);
                self.local_label_counter_if += 1;
                self.generate_condition_ex(&f, &Operation::Eq, &ExprType::Immediate(0), pos, true, &ifstart_label)?;
                self.generate_condition_ex(&ExprType::Tmp(false), &Operation::Eq, &ExprType::Immediate(0), pos, false, label)?;
                self.label(&ifstart_label)
            },
            _ => unreachable!()
        };
        self.tmp_in_use = false;
        res
    }
    
    fn generate_condition_ex(&mut self, l: &ExprType, op: &Operation, r: &ExprType, pos: usize, negate: bool, label: &str) -> Result<(), Error>
    {
        let left;
        let right;

        let switch = match &l {
            ExprType::X | ExprType::Y => {
                left = l; right = r;
                false
            }, 
            _ => match &r {
                ExprType::A(_) | ExprType::X | ExprType::Y => {
                    left = r; right = l;
                    true 
                },
                _ => {
                    left = l; right = r;
                    false
                }
            }
        };

        let opx = if negate {
            match op {
                Operation::Eq => Operation::Neq,
                Operation::Neq => Operation::Eq,
                Operation::Gt => Operation::Lte,
                Operation::Gte => Operation::Lt,
                Operation::Lt => Operation::Gte,
                Operation::Lte => Operation::Gt,
                _ => unreachable!()
            }
        } else { *op };

        let operator = if switch {
            match opx {
                Operation::Eq => Operation::Eq,
                Operation::Neq => Operation::Neq,
                Operation::Gt => Operation::Lt,
                Operation::Gte => Operation::Lte,
                Operation::Lt => Operation::Gt,
                Operation::Lte => Operation::Gte,
                _ => unreachable!()
            }
        } else { opx };

        if let ExprType::Immediate(v) = *right {
            if v == 0 {
                // Let's see if we can shortcut compare instruction 
                if flags_ok(&self.flags, left) {
                    match operator {
                        Operation::Neq => {
                            self.asm(BNE, &ExprType::Label(label.into()), pos, false)?;
                            match left {
                                ExprType::A(_) => self.acc_in_use = false,
                                ExprType::Tmp(_) => self.tmp_in_use = false,
                                _ => (),
                            }
                            return Ok(());
                        },
                        Operation::Eq => {
                            self.asm(BEQ, &ExprType::Label(label.into()), pos, false)?;
                            match left {
                                ExprType::A(_) => self.acc_in_use = false,
                                ExprType::Tmp(_) => self.tmp_in_use = false,
                                _ => (),
                            }
                            return Ok(());
                        },
                        _ => {
                            // Special case : deterministic condition
                            if let ExprType::Immediate(v) = left {
                                if (operator == Operation::Neq && *v != 0) || (operator == Operation::Eq && *v == 0) {
                                    self.asm(JMP, &ExprType::Label(label.into()), pos, false)?;
                                }
                                return Ok(());
                            }
                            let signed = match left {
                                ExprType::X | ExprType::Y => false,
                                ExprType::A(s) => {
                                    self.acc_in_use = false;
                                    *s
                                },
                                ExprType::Tmp(s) => {
                                    self.tmp_in_use = false;
                                    *s
                                },
                                ExprType::AbsoluteX(s) | ExprType::AbsoluteY(s) | ExprType::Absolute(s, _, _) => {
                                    let v = self.compiler_state.get_variable(s);
                                    v.signed
                                },
                                _ => unreachable!(),
                            };
                            if self.carry_flag_ok {
                                return self.generate_branch_instruction(&operator, signed, label);
                            } else {
                                return self.generate_branch_instruction_alt(&operator, signed, label);
                            }
                        } 
                    }
                } 
            }
        }

        // Compare instruction
        let signed;
        let cmp;
        self.carry_flag_ok = false;
        match left {
            ExprType::Absolute(a, eight_bits, b) => {
                if self.acc_in_use { return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos)); }
                if !eight_bits {
                    return self.generate_condition_16bits(left, &operator, right, pos, label);
                }
                signed = self.asm(LDA, left, pos, false)?;
                cmp = true;
                self.flags = FlagsState::Absolute((*a).clone(), *eight_bits, *b);
            },
            ExprType::AbsoluteX(s) => {
                if self.acc_in_use { return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos)); }
                signed = self.asm(LDA, left, pos, false)?;
                cmp = true;
                self.flags = FlagsState::AbsoluteX((*s).clone());
            },
            ExprType::AbsoluteY(s) => {
                if self.acc_in_use { return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos)); }
                signed = self.asm(LDA, left, pos, false)?;
                cmp = true;
                self.flags = FlagsState::AbsoluteY((*s).clone());
            },
            ExprType::A(sign) => {
                cmp = true;
                signed = *sign;
                self.acc_in_use = false;
                self.flags = FlagsState::A;
            },
            ExprType::Tmp(sign) => {
                if self.acc_in_use { return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos)); }
                signed = *sign;
                self.asm(LDA, left, pos, false)?;
                self.tmp_in_use = false;
                self.flags = FlagsState::Unknown;
                cmp = true;
            },
            ExprType::Y => {
                signed = false;
                self.flags = FlagsState::Unknown;
                match right {
                    ExprType::Immediate(_) => {
                        self.asm(CPY, right, pos, false)?;
                        cmp = false;
                    },
                    ExprType::Absolute(_, eight_bits, _) => {
                        if !eight_bits {
                            return Err(self.compiler_state.syntax_error("Comparison is only partially implemented on 16 bits data", pos));
                        }
                        self.asm(CPY, right, pos, false)?;
                        cmp = false;
                    },
                    ExprType::A(s) => {
                        if self.tmp_in_use {
                            return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                        }
                        self.asm(STA, &ExprType::Tmp(*s), pos, false)?;
                        self.asm(CPY, &ExprType::Tmp(*s), pos, false)?;
                        cmp = false;
                        self.acc_in_use = false;
                    },
                    ExprType::Tmp(_) => {
                        self.asm(CPY, right, pos, false)?;
                        cmp = false;
                        self.tmp_in_use = false;
                    },
                    _ => {
                        if self.acc_in_use {
                            return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                        }
                        self.sasm(TYA)?;
                        self.acc_in_use = true;
                        return self.generate_condition_ex(&ExprType::A(false), op, r, pos, negate, label);
                    }
                } 
            },
            ExprType::X => {
                signed = false;
                self.flags = FlagsState::Unknown;
                match right {
                    ExprType::Immediate(_) => {
                        self.asm(CPX, right, pos, false)?;
                        cmp = false;
                    },
                    ExprType::Absolute(_, eight_bits, _) => {
                        if !eight_bits {
                            return Err(self.compiler_state.syntax_error("Comparison is only partially implemented on 16 bits data", pos));
                        }
                        self.asm(CPX, right, pos, false)?;
                        cmp = false;
                    },
                    ExprType::A(s) => {
                        if self.tmp_in_use {
                            return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                        }
                        self.asm(STA, &ExprType::Tmp(*s), pos, false)?;
                        self.asm(CPX, &ExprType::Tmp(*s), pos, false)?;
                        cmp = false;
                        self.acc_in_use = false;
                    },
                    ExprType::Tmp(_) => {
                        self.asm(CPX, right, pos, false)?;
                        cmp = false;
                        self.tmp_in_use = false;
                    },
                    _ => {
                        if self.acc_in_use {
                            return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                        }
                        self.sasm(TXA)?;
                        self.acc_in_use = true;
                        return self.generate_condition_ex(&ExprType::A(false), op, r, pos, negate, label);
                    }
                } 
            },
            _ => { return Err(Error::Unimplemented { feature: "condition statement is partially implemented" }); },
        }

        if cmp {
            match right {
                ExprType::Immediate(v) => {
                    if *v != 0 {
                        self.asm(CMP, right, pos, false)?;
                        self.flags = FlagsState::Unknown;
                    } else {
                        // No CMP
                        return self.generate_branch_instruction_alt(&operator, signed, label)
                    }
                },
                ExprType::Absolute(_, eight_bits, _) => {
                    if !eight_bits {
                        return Err(self.compiler_state.syntax_error("Comparison is only partially implemented on 16 bits data", pos));
                    }
                    self.asm(CMP, right, pos, false)?;
                    self.flags = FlagsState::Unknown;
                },
                ExprType::AbsoluteX(_) | ExprType::AbsoluteY(_) => {
                    self.asm(CMP, right, pos, false)?;
                    self.flags = FlagsState::Unknown;
                },
                ExprType::Tmp(_) => {
                    self.asm(CMP, right, pos, false)?;
                    self.flags = FlagsState::Unknown;
                    self.tmp_in_use = false;
                },
                _ => return Err(self.compiler_state.syntax_error("Operation too complex for this compiler. Please introduce intermediate variables", pos))
            } 
        }

        self.generate_branch_instruction(&operator, signed, label)
    }

    pub fn generate_condition(&mut self, condition: &Expr, pos: usize, negate: bool, label: &str, immediate_special: bool) -> Result<Option<bool>, Error>
    {
        //debug!("Condition: {:?}", condition);
        match condition {
            Expr::BinOp {lhs, op, rhs} => {
                if match op {
                    Operation::Eq => true,
                        Operation::Neq => true,
                        Operation::Gt => true,
                        Operation::Gte => true,
                        Operation::Lt => true,
                        Operation::Lte => true,
                        Operation::Land => {
                            if negate {
                                let cond = self.generate_condition(lhs, pos, true, label, immediate_special)?;
                                if let Some(a) = cond {
                                    if a { return Ok(Some(true)) }
                                    return self.generate_condition(rhs, pos, true, label, immediate_special);
                                }
                                return self.generate_condition(rhs, pos, true, label, false);
                            } else {
                                let ifstart_label = format!(".ifstart{}", self.local_label_counter_if);
                                self.local_label_counter_if += 1;
                                let cond = self.generate_condition(lhs, pos, true, &ifstart_label, immediate_special)?;
                                //debug!("left = {:?}", cond);
                                if let Some(a) = cond {
                                    if a { return Ok(Some(false)) }
                                    return self.generate_condition(rhs, pos, false, label, immediate_special);
                                }
                                self.generate_condition(rhs, pos, false, label, false)?;
                                self.label(&ifstart_label)?;
                                return Ok(None);
                            }
                        },
                        Operation::Lor => {
                            if negate {
                                let ifstart_label = format!(".ifstart{}", self.local_label_counter_if);
                                self.local_label_counter_if += 1;
                                let cond = self.generate_condition(lhs, pos, false, &ifstart_label, immediate_special)?;
                                //debug!("left = {:?}", cond);
                                if let Some(a) = cond {
                                    if a { return Ok(Some(false)); }
                                    return self.generate_condition(rhs, pos, true, label, immediate_special);
                                }
                                self.generate_condition(rhs, pos, true, label, false)?;
                                self.label(&ifstart_label)?;
                                return Ok(None);
                            } else {
                                let cond = self.generate_condition(lhs, pos, false, label, immediate_special)?;
                                if let Some(a) = cond {
                                    if a { return Ok(Some(true)) }
                                    return self.generate_condition(rhs, pos, false, label, immediate_special);
                                }
                                return self.generate_condition(rhs, pos, false, label, false);
                            }
                        },
                        _ => false,
                } {
                    let l = self.generate_expr(lhs, pos, false, false)?;
                    let r = self.generate_expr(rhs, pos, false, false)?;
                    if immediate_special {
                        if let ExprType::Immediate(a) = l {
                            if let ExprType::Immediate(b) = r {
                                match op {
                                    Operation::Eq => return Ok(Some(if a == b { !negate } else { negate })),
                                    Operation::Neq => return Ok(Some(if a != b { !negate } else { negate })),
                                    Operation::Gt => return Ok(Some(if a > b { !negate } else { negate })),
                                    Operation::Gte => return Ok(Some(if a >= b { !negate } else { negate })),
                                    Operation::Lt => return Ok(Some(if a < b { !negate } else { negate })),
                                    Operation::Lte => return Ok(Some(if a <= b { !negate } else { negate })),
                                    _ => unreachable!()

                                }
                            }
                        }
                    }
                    self.generate_condition_ex(&l, op, &r, pos, negate, label)?;
                    return Ok(None);
                }
            },
            Expr::Not(expr) => {
                return self.generate_condition(expr, pos, !negate, label, immediate_special); 
            },
            _ => ()
        };

        let expr = self.generate_expr(condition, pos, false, false)?;
        if flags_ok(&self.flags, &expr) {
            if let ExprType::A(_) = expr {
                self.acc_in_use = false;
            }
            if let ExprType::Tmp(_) = expr {
                self.tmp_in_use = false;
            }
            if negate {
                self.asm(BEQ, &ExprType::Label(label.into()), pos, false)?;
            } else {
                self.asm(BNE, &ExprType::Label(label.into()), pos, false)?;
            }
            Ok(None)
        } else {
            self.flags = FlagsState::Unknown;
            match &expr {
                ExprType::Immediate(v) => {
                    if immediate_special {
                        return Ok(Some(if *v != 0 { !negate } else { negate }));
                    }
                    if *v != 0 {
                        if !negate {
                            self.asm(JMP, &ExprType::Label(label.into()), pos, false)?;
                        }
                    } else if negate {
                        self.asm(JMP, &ExprType::Label(label.into()), pos, false)?;
                    }
                    self.flags = FlagsState::Unknown;
                    return Ok(None);
                },
                ExprType::Absolute(a, eight_bits, b) => {
                    if self.acc_in_use { self.sasm(PHA)?; }
                    if !eight_bits {
                        self.generate_condition_16bits(&expr, if negate { &Operation::Eq } else { &Operation::Neq }, &ExprType::Immediate(0), pos, label)?; 
                        return Ok(None);
                    }
                    self.asm(LDA, &expr, pos, false)?;
                    self.flags = FlagsState::Absolute(a.clone(), *eight_bits, *b);
                },
                ExprType::AbsoluteX(s) => {
                    if self.acc_in_use { self.sasm(PHA)?; }
                    self.asm(LDA, &expr, pos, false)?;
                    self.flags = FlagsState::AbsoluteX(s.clone());
                },
                ExprType::AbsoluteY(s) => {
                    if self.acc_in_use { self.sasm(PHA)?; }
                    self.asm(LDA, &expr, pos, false)?;
                    self.flags = FlagsState::AbsoluteY(s.clone());
                },
                ExprType::A(_) => {
                    self.acc_in_use = false;
                },
                ExprType::Y => {
                    self.asm(CPY, &ExprType::Immediate(0), pos, false)?;
                    self.flags = FlagsState::Y;
                },
                ExprType::X => {
                    self.asm(CPX, &ExprType::Immediate(0), pos, false)?;
                    self.flags = FlagsState::X;
                }
                ExprType::Tmp(_) => {
                    if self.acc_in_use { self.sasm(PHA)?; }
                    self.asm(LDA, &expr, pos, false)?;
                    self.tmp_in_use = false;
                },
                _ => return Err(Error::Unimplemented { feature: "condition statement is partially implemented" })
            }

            if negate {
                self.asm(BEQ, &ExprType::Label(label.into()), 0, false)?;
            } else {
                self.asm(BNE, &ExprType::Label(label.into()), 0, false)?;
            }
            Ok(None)
        }
    }

    pub fn generate_if(&mut self, condition: &'a Expr, body: &'a StatementLoc<'a>, else_body: Option<&'a StatementLoc<'a>>, pos: usize) -> Result<(), Error>
    {
        self.local_label_counter_if += 1;
        let ifend_label = format!(".ifend{}", self.local_label_counter_if);
        match else_body {
            None => {
                match body.statement {
                    Statement::Break => {
                        let brk_label = {
                            match self.loops.last() {
                                None => return Err(self.compiler_state.syntax_error("Break statement outside loop", pos)),
                                Some((_, bl, _)) => bl.clone(),
                            }
                        };
                        self.generate_condition(condition, pos, false, &brk_label, false)?;
                    },
                    Statement::Continue => {
                        let cont_label = {
                            match self.loops.last() {
                                None => return Err(self.compiler_state.syntax_error("Break statement outside loop", pos)),
                                Some((cl, _, _)) => cl.clone(),
                            }
                        };
                        self.generate_condition(condition, pos, false, &cont_label, false)?;
                        self.loops.last_mut().unwrap().2 = true;
                    },
                    _ => {
                        self.generate_condition(condition, pos, true, &ifend_label, false)?;
                        self.generate_statement(body)?;
                        self.label(&ifend_label)?;
                    }

                }
            },
            Some(else_statement) => {
                let else_label = format!(".else{}", self.local_label_counter_if);
                self.generate_condition(condition, pos, true, &else_label, false)?;
                let saved_flags = self.flags.clone();
                self.generate_statement(body)?;
                self.asm(JMP, &ExprType::Label(ifend_label.clone()), 0, false)?;
                self.label(&else_label)?;
                self.flags = saved_flags;
                self.generate_statement(else_statement)?;
                self.label(&ifend_label)?;
            }
        };
        Ok(())
    }

    pub fn generate_switch(&mut self, expr: &'a Expr, cases: &'a Vec<(Vec<i32>, Vec<StatementLoc<'a>>)>, pos: usize) -> Result<(), Error>
    {
        let e = self.generate_expr(expr, pos, false, false)?;
        self.local_label_counter_if += 1;
        let switchend_label = format!(".switchend{}", self.local_label_counter_if);
        match self.loops.last() {
            Some(l) => self.loops.push((l.0.clone(), switchend_label.clone(), false)),
            None => self.loops.push(("".to_string(), switchend_label.clone(), false))
        }
        self.local_label_counter_if += 1;
        let mut switchnextstatement_label = format!(".switchnextstatement{}", self.local_label_counter_if);
        debug!("Cases : {:?}", cases);
        for (case, is_last_element) in cases.iter().enumerate().map(|(i,c)| (c, i == cases.len() - 1)) {
            self.local_label_counter_if += 1;
            let switchnextcase_label = format!(".switchnextcase{}", self.local_label_counter_if);
            let mut jmp_to_next_case = false;
            match case.0.len() {
                0 => (),
                1 => {
                    self.generate_condition_ex(&e, &Operation::Eq, &ExprType::Immediate(case.0[0]), pos, true, &switchnextcase_label)?;
                    jmp_to_next_case = true;
                },
                _ => {
                    for i in &case.0 {
                        self.generate_condition_ex(&e, &Operation::Eq, &ExprType::Immediate(*i), pos, false, &switchnextstatement_label)?;
                    }
                    self.asm(JMP, &ExprType::Label(switchnextcase_label.clone()), 0, false)?;
                    jmp_to_next_case = true;
                }
            }
            self.label(&switchnextstatement_label)?;
            for code in &case.1 {
                self.generate_statement(code)?;
            }
            self.local_label_counter_if += 1;
            switchnextstatement_label = format!(".switchnextstatement{}", self.local_label_counter_if);
            // If this is not the last case...
            if !is_last_element {
                self.asm(JMP, &ExprType::Label(switchnextstatement_label.clone()), 0, false)?;
            }
            if jmp_to_next_case {
                self.label(&switchnextcase_label)?;
            }
        }
        self.label(&switchend_label)?;
        self.loops.pop();
        Ok(())
    }
}

fn flags_ok(flags: &FlagsState, expr_type: &ExprType) -> bool
{
    match flags {
        FlagsState::X => *expr_type == ExprType::X,
        FlagsState::Y => *expr_type == ExprType::Y,
        FlagsState::A => if let ExprType::A(_) = *expr_type { true } else { false },
        FlagsState::AbsoluteX(s) => *expr_type == ExprType::AbsoluteX(s.clone()),
        FlagsState::AbsoluteY(s) => *expr_type == ExprType::AbsoluteY(s.clone()),
        FlagsState::Absolute(var, eight_bits, offset) => *expr_type == ExprType::Absolute(var.clone(), *eight_bits, *offset),
        _ => false
    }
}

