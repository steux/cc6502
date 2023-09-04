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

use crate::error::Error;
use crate::compile::*;
use crate::assemble::AsmMnemonic::*;

use super::{GeneratorState, ExprType, FlagsState};

impl<'a> GeneratorState<'a> {

    pub(crate) fn generate_assign(&mut self, left: &ExprType, right: &ExprType, pos: usize, high_byte: bool) -> Result<ExprType, Error>
    {
        match left {
            ExprType::X => {
                match right {
                    ExprType::Immediate(_) => {
                        self.asm(LDX, right, pos, high_byte)?;
                        self.flags = FlagsState::X; 
                        self.carry_flag_ok = false;
                        Ok(ExprType::X) 
                    },
                    ExprType::Tmp(_) => {
                        self.asm(LDX, right, pos, high_byte)?;
                        self.flags = FlagsState::X; 
                        self.tmp_in_use = false;
                        self.carry_flag_ok = false;
                        Ok(ExprType::X) 
                    },
                    ExprType::Absolute(_, _, _) => {
                        self.asm(LDX, right, pos, high_byte)?;
                        self.flags = FlagsState::X;
                        self.carry_flag_ok = false;
                        Ok(ExprType::X)
                    },
                    ExprType::AbsoluteX(_) => {
                        if self.acc_in_use { self.sasm(PHA)?; }
                        self.asm(LDA, right, pos, high_byte)?;
                        self.sasm(TAX)?;
                        if self.acc_in_use { 
                            self.sasm(PLA)?;
                            self.flags = FlagsState::Unknown;
                        } else {
                            self.flags = FlagsState::X;
                        }
                        self.carry_flag_ok = false;
                        Ok(ExprType::X)
                    },
                    ExprType::AbsoluteY(variable) => {
                        let v = self.compiler_state.get_variable(variable);
                        if v.var_type == VariableType::CharPtr && !v.var_const && v.size == 1 {
                            if self.acc_in_use { self.sasm(PHA)?; }
                            self.asm(LDA, right, pos, high_byte)?;
                            self.sasm(TAX)?;
                            if self.acc_in_use { 
                                self.sasm(PLA)?;
                                self.flags = FlagsState::Unknown;
                            } else {
                                self.flags = FlagsState::X;
                            }
                        } else {
                            self.asm(LDX, right, pos, high_byte)?;
                            self.flags = FlagsState::X; 
                        }
                        self.carry_flag_ok = false;
                        Ok(ExprType::X)
                    },
                    ExprType::A(_) => {
                        self.sasm(TAX)?;
                        self.flags = FlagsState::X;
                        self.acc_in_use = false;
                        Ok(ExprType::X)
                    },
                    ExprType::X => {
                        Ok(ExprType::X)
                    },
                    ExprType::Y => {
                        if self.acc_in_use { self.sasm(PHA)?; }
                        self.sasm(TYA)?;
                        self.sasm(TAX)?;
                        if self.acc_in_use { 
                            self.sasm(PLA)?;
                            self.flags = FlagsState::Unknown;
                        } else {
                            self.flags = FlagsState::X;
                        }
                        self.carry_flag_ok = false;
                        Ok(ExprType::X)
                    },
                    ExprType::Nothing => unreachable!(),
                    ExprType::Label(_) => unreachable!(),
                }
            },
            ExprType::Y => {
                if self.saved_y {
                    return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                }
                match right {
                    ExprType::Immediate(_) | ExprType::AbsoluteX(_) => {
                        self.asm(LDY, right, pos, high_byte)?;
                        self.flags = FlagsState::Y; 
                        self.carry_flag_ok = false;
                        Ok(ExprType::Y) 
                    },
                    ExprType::Tmp(_) => {
                        self.asm(LDY, right, pos, high_byte)?;
                        self.flags = FlagsState::Y; 
                        self.tmp_in_use = false;
                        self.carry_flag_ok = false;
                        Ok(ExprType::Y) 
                    },
                    ExprType::Absolute(_, _ , _) => {
                        self.asm(LDY, right, pos, high_byte)?;
                        self.flags = FlagsState::Y;
                        self.carry_flag_ok = false;
                        Ok(ExprType::Y)
                    },
                    ExprType::AbsoluteY(_) => {
                        if self.acc_in_use { self.sasm(PHA)?; }
                        self.asm(LDA, right, pos, high_byte)?;
                        self.sasm(TAY)?;
                        if self.acc_in_use { 
                            self.sasm(PLA)?;
                            self.flags = FlagsState::Unknown;
                        } else {
                            self.flags = FlagsState::Y;
                        }
                        self.carry_flag_ok = false;
                        Ok(ExprType::Y)
                    },
                    ExprType::A(_)=> {
                        self.sasm(TAY)?;
                        self.acc_in_use = false;
                        self.flags = FlagsState::Y;
                        Ok(ExprType::Y)
                    },
                    ExprType::X => {
                        if self.acc_in_use { self.sasm(PHA)?; }
                        self.sasm(TXA)?;
                        self.sasm(TAY)?;
                        if self.acc_in_use { 
                            self.sasm(PLA)?;
                            self.flags = FlagsState::Unknown;
                        } else {
                            self.flags = FlagsState::Y;
                        }
                        self.carry_flag_ok = false;
                        Ok(ExprType::Y)
                    },
                    ExprType::Y => {
                        self.flags = FlagsState::Y;
                        self.carry_flag_ok = false;
                        Ok(ExprType::Y)
                    },
                    ExprType::Nothing => unreachable!(),
                    ExprType::Label(_) => unreachable!(),
                }
            },
            _ => {
                match right {
                    ExprType::X => {
                        match left {
                            ExprType::Absolute(_, eight_bits, offset) => {
                                self.asm(STX, left, pos, high_byte)?;
                                if !eight_bits {
                                    if *offset == 0 {
                                        // Set high byte of this 16 bits variable to 0 (since X is unsigned)
                                        if self.acc_in_use { self.sasm(PHA)?; }
                                        self.asm(LDA, &ExprType::Immediate(0), pos, false)?;
                                        self.asm(STA, left, pos, true)?;
                                        if self.acc_in_use { 
                                            self.sasm(PLA)?;
                                        }
                                    } else {
                                        unreachable!(); 
                                    }
                                    self.flags = FlagsState::Unknown;
                                }
                                self.carry_flag_ok = false;
                                Ok(ExprType::X)
                            },
                            ExprType::AbsoluteX(_) => {
                                if self.acc_in_use { self.sasm(PHA)?; }
                                self.sasm(TXA)?;
                                self.asm(STA, left, pos, high_byte)?;
                                if self.acc_in_use {
                                    self.sasm(PLA)?;
                                    self.flags = FlagsState::Unknown;
                                } else {
                                    self.flags = FlagsState::X;
                                }
                                self.carry_flag_ok = false;
                                Ok(ExprType::X)
                            },
                            ExprType::AbsoluteY(variable) => {
                                let v = self.compiler_state.get_variable(variable);
                                if v.memory == VariableMemory::Zeropage && v.var_type != VariableType::CharPtr {
                                    self.asm(STX, left, pos, high_byte)?;
                                } else {
                                    if self.acc_in_use { self.sasm(PHA)?; }
                                    self.sasm(TXA)?;
                                    self.asm(STA, left, pos, high_byte)?;
                                    if self.acc_in_use {
                                        self.sasm(PLA)?;
                                        self.flags = FlagsState::Unknown;
                                    } else {
                                        self.flags = FlagsState::X;
                                    }
                                }
                                self.carry_flag_ok = false;
                                Ok(ExprType::X)
                            },
                            ExprType::A(_) => {
                                if self.acc_in_use {
                                    return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                                }
                                self.sasm(TXA)?;
                                self.acc_in_use = true;
                                return Ok(ExprType::A(false));
                            },
                            ExprType::Tmp(_) => {
                                if self.tmp_in_use {
                                    return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                                }
                                self.asm(STX, left, pos, high_byte)?;
                                self.tmp_in_use = true;
                                return Ok(ExprType::Tmp(false));
                            },
                            _ => Err(self.compiler_state.syntax_error("Bad left value in assignement", pos)),
                        }
                    },
                    ExprType::Y => {
                        match left {
                            ExprType::Absolute(_, eight_bits, offset) => {
                                self.asm(STY, left, pos, high_byte)?;
                                if !eight_bits {
                                    if *offset == 0 {
                                        if self.acc_in_use { self.sasm(PHA)?; }
                                        self.asm(LDA, &ExprType::Immediate(0), pos, false)?;
                                        self.asm(STA, left, pos, true)?;
                                        if self.acc_in_use { 
                                            self.sasm(PLA)?;
                                        }
                                    } else {
                                        unreachable!(); 
                                    }
                                    self.flags = FlagsState::Unknown;
                                }
                                self.carry_flag_ok = false;
                                Ok(ExprType::Y)
                            },
                            ExprType::AbsoluteY(_) => {
                                if self.acc_in_use { self.sasm(PHA)?; }
                                self.sasm(TYA)?;
                                self.asm(STA, left, pos, high_byte)?;
                                if self.acc_in_use {
                                    self.sasm(PLA)?;
                                    self.flags = FlagsState::Unknown;
                                } else {
                                    self.flags = FlagsState::Y;
                                }
                                self.carry_flag_ok = false;
                                Ok(ExprType::Y)
                            },
                            ExprType::AbsoluteX(variable) => {
                                let v = self.compiler_state.get_variable(variable);
                                if v.memory == VariableMemory::Zeropage {
                                    self.asm(STY, left, pos, high_byte)?;
                                } else {
                                    if self.acc_in_use { self.sasm(PHA)?; }
                                    self.sasm(TYA)?;
                                    self.asm(STA, left, pos, high_byte)?;
                                    if self.acc_in_use {
                                        self.sasm(PLA)?;
                                        self.flags = FlagsState::Unknown;
                                    } else {
                                        self.flags = FlagsState::Y;
                                    }
                                }
                                self.carry_flag_ok = false;
                                Ok(ExprType::Y)
                            },
                            ExprType::A(_) => {
                                if self.acc_in_use {
                                    return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                                }
                                self.sasm(TYA)?;
                                self.acc_in_use = true;
                                return Ok(ExprType::A(false));
                            },
                            ExprType::Tmp(_) => {
                                if self.tmp_in_use {
                                    return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                                }
                                self.asm(STY, left, pos, high_byte)?;
                                self.tmp_in_use = true;
                                return Ok(ExprType::Tmp(false));
                            },
                            _ => Err(self.compiler_state.syntax_error("Bad left value in assignement", pos)),
                        }
                    },
                    _ => {
                        let mut acc_in_use = self.acc_in_use;
                        let signed;
                        match right {
                            ExprType::Absolute(_, _, _) | ExprType::AbsoluteX(_) | ExprType::AbsoluteY(_) | ExprType::Immediate(_) | ExprType::Tmp(_) => {
                                if self.acc_in_use { self.sasm(PHA)?; }
                                signed = self.asm(LDA, right, pos, high_byte)?;
                                self.carry_flag_ok = false;
                            },
                            ExprType::A(s) => {
                                signed = *s;
                                acc_in_use = false;
                                self.acc_in_use = false;
                            },
                            _ => unreachable!()
                        };
                        match left {
                            ExprType::Absolute(a, b, c) => {
                                self.asm(STA, left, pos, high_byte)?;
                                self.flags = if high_byte { FlagsState::Unknown } else { FlagsState::Absolute(a.clone(), *b, *c) }
                            },
                            ExprType::AbsoluteX(s) => {
                                self.asm(STA, left, pos, high_byte)?;
                                self.flags = if high_byte { FlagsState::Unknown } else { FlagsState::AbsoluteX(s.clone()) }
                            },
                            ExprType::AbsoluteY(s) => {
                                self.asm(STA, left, pos, high_byte)?;
                                self.flags = if high_byte { FlagsState::Unknown } else { FlagsState::AbsoluteY(s.clone()) }
                            },
                            ExprType::A(_) => {
                                if acc_in_use {
                                    return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                                }
                                self.acc_in_use = true;
                                self.flags = FlagsState::A;
                                return Ok(ExprType::A(signed));
                            },
                            ExprType::Tmp(_) => {
                                if self.tmp_in_use {
                                    return Err(self.compiler_state.syntax_error("Code too complex for the compiler", pos))
                                }
                                self.tmp_in_use = true;
                                self.asm(STA, left, pos, high_byte)?;
                                return Ok(ExprType::Tmp(signed));
                            },
                            _ => return Err(self.compiler_state.syntax_error("Bad left value in assignement", pos)),
                        };
                        if acc_in_use {
                            self.sasm(PLA)?;
                            self.flags = FlagsState::Unknown;
                            self.carry_flag_ok = false;
                        }
                        Ok(left.clone())
                    }
                }
            }
        }
    }
}
