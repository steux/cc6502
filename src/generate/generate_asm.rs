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

use std::collections::{HashMap, HashSet};
use log::{debug, info};
use std::io::Write;
use regex::Regex;

use crate::error::Error;
use crate::compile::*;
use crate::assemble::{AssemblyCode, AsmMnemonic, AsmMnemonic::*, AsmInstruction};

use super::{GeneratorState, ExprType, FlagsState};

impl<'a> GeneratorState<'a> {
    pub fn new(compiler_state: &'a CompilerState, writer: &'a mut dyn Write, insert_code: bool, warnings: Vec<String>, bankswitching_scheme: &'a str) -> GeneratorState<'a> {
        GeneratorState {
            compiler_state,
            insert_code,
            warnings,
            last_included_line_number: 0,
            last_included_position: 0,
            last_included_char: compiler_state.preprocessed_utf8.chars(),
            writer,
            local_label_counter_for: 0,
            local_label_counter_if: 0,
            local_label_counter_while: 0,
            inline_label_counter: 0,
            loops: Vec::new(),
            flags: FlagsState::Unknown,
            carry_flag_ok: false,
            acc_in_use: false,
            tmp_in_use: false,
            whitespaces_regex: Regex::new(r"\s+").unwrap(),
            deferred_plusplus: Vec::new(),
            current_bank: 0,
            functions_code: HashMap::new(),
            functions_call_tree: HashMap::new(),
            functions_actually_in_use: HashSet::new(),
            current_function: None,
            bankswitching_scheme,
            protected: false,
            carry_propagation_error: false,
            saved_y: false,
        }
    }
    
    pub(crate) fn sasm(&mut self, mnemonic: AsmMnemonic) -> Result<bool, Error>
    {
        self.asm(mnemonic, &ExprType::Nothing, 0, false)
    }

    pub(crate) fn sasm_protected(&mut self, mnemonic: AsmMnemonic) -> Result<bool, Error>
    {
        self.protected = true;
        let ret = self.asm(mnemonic, &ExprType::Nothing, 0, false);
        self.protected = false;
        ret
    }

    pub(crate) fn asm(&mut self, mnemonic: AsmMnemonic, operand: &ExprType, pos: usize, high_byte: bool) -> Result<bool, Error>
    {
        let dasm_operand: String;
        let signed;
        let nb_bytes;

        let mut cycles = match mnemonic {
            PHA | PLA => 3,
            INC | DEC => 4,
            RTS => 6,
            _ => 2 
        };
        let mut cycles_alt = None;

        match operand {
            ExprType::Label(l) => {
                nb_bytes = match mnemonic {
                    JMP | JSR => 3,
                    _ => 2,
                };
                cycles = match mnemonic {
                    JMP => 3,
                    JSR => 6,
                    _ => { cycles_alt = Some(3); 2},
                };
                signed = false;
                dasm_operand = (*l).to_string();
            },
            ExprType::Immediate(v) => {
                nb_bytes = 2;
                let vx = match high_byte {
                    false => v & 0xff,
                    true => (v >> 8) & 0xff,
                };
                signed = false;
                dasm_operand = format!("#{}", vx);
            },
            ExprType::Tmp(s) => {
                dasm_operand = "cctmp".to_string();
                cycles += 1;
                nb_bytes = 2;
                signed = *s;
            },
            ExprType::A(s) => {
                if mnemonic == LDA { return Ok(*s); }
                if mnemonic == LDX {
                    return self.asm(TAX, &ExprType::Nothing, pos, high_byte);
                }
                if mnemonic == LDY {
                    return self.asm(TAY, &ExprType::Nothing, pos, high_byte);
                }
                return Err(self.compiler_state.syntax_error("Unexpected expression type", pos));           
            },
            ExprType::Absolute(variable, eight_bits, off) => {
                let v = self.compiler_state.get_variable(variable);
                signed = v.signed;
                let offset = if v.memory == VariableMemory::Superchip {
                    match mnemonic {
                        STA | STX | STY => *off,
                        _ => off + 0x80
                    }
                } else if let VariableMemory::MemoryOnChip(_) = v.memory {
                    if self.bankswitching_scheme == "3E" {
                        match mnemonic {
                            STA | STX | STY => off + 0x400,
                            _ => *off
                        }
                    } else if self.bankswitching_scheme == "3EP" {
                        match mnemonic {
                            STA | STX | STY => off + 0x200,
                            _ => *off
                        }
                    } else { *off }
                } else { *off };
                match v.var_type {
                    VariableType::Char => if !*eight_bits {
                        if high_byte {
                            if offset != 0 {
                                dasm_operand = format!("#>({}+{})", variable, offset);
                            } else {
                                dasm_operand = format!("#>{}", variable);
                            }
                        } else if offset != 0 {
                            dasm_operand = format!("#<({}+{})", variable, offset);
                        } else {
                            dasm_operand = format!("#<{}", variable);
                        }
                        nb_bytes = 2;
                    } else if high_byte {
                        dasm_operand = "#0".to_string();
                        nb_bytes = 2;
                    } else {
                        if offset > 0 {
                            dasm_operand = format!("{}+{}", variable, offset);
                        } else {
                            dasm_operand = variable.to_string();
                        }
                        if v.memory == VariableMemory::Zeropage {
                            cycles += 1;
                            nb_bytes = 2;
                        } else {
                            cycles += 2;
                            nb_bytes = 3;
                        }
                    },
                    VariableType::Short => {
                        if *eight_bits && high_byte {
                            dasm_operand = "#0".to_string();
                            nb_bytes = 2;
                        } else {
                            let off = if high_byte { offset + 1 } else { offset };
                            if off != 0 {
                                dasm_operand = format!("{}+{}", variable, off);
                            } else {
                                dasm_operand = variable.to_string();
                            }
                            if v.memory == VariableMemory::Zeropage {
                                cycles += 1;
                                nb_bytes = 2;
                            } else {
                                cycles += 2;
                                nb_bytes = 3;
                            }
                        }
                    },
                    VariableType::CharPtr => if !*eight_bits && v.var_const {
                        if high_byte {
                            if offset != 0 {
                                dasm_operand = format!("#>({}+{})", variable, offset);
                            } else {
                                dasm_operand = format!("#>{}", variable);
                            }
                        } else if offset != 0 {
                            dasm_operand = format!("#<({}+{})", variable, offset);
                        } else {
                            dasm_operand = format!("#<{}", variable);
                        }
                        nb_bytes = 2;
                    } else if high_byte && *eight_bits {
                        dasm_operand = "#0".to_string();
                        nb_bytes = 2;
                    } else if *eight_bits && !v.var_const {
                        // This is indirect addressing, but in a mode not possible by 6502
                        // (constant offset)
                        return Err(self.compiler_state.syntax_error("Indirect adressing mode is only available with Y (use Y as array index)", pos));
                    } else {
                        let off = if high_byte { offset + 1 } else { offset };
                        if off != 0 {
                            dasm_operand = format!("{}+{}", variable, off);
                        } else {
                            dasm_operand = variable.to_string();
                        }
                        if v.memory == VariableMemory::Zeropage {
                            cycles += 1;
                            nb_bytes = 2;
                        } else {
                            cycles += 2;
                            nb_bytes = 3;
                        }
                    },
                    VariableType::CharPtrPtr | VariableType::ShortPtr => {
                        let v = self.compiler_state.get_variable(variable);
                        let off = offset + if high_byte { v.size as i32 } else { 0 };
                        if off > 0 {
                            dasm_operand = format!("{}+{}", variable, off);
                        } else {
                            dasm_operand = variable.to_string();
                        }
                        cycles += 2;
                        if v.memory == VariableMemory::Zeropage {
                            nb_bytes = 2;
                        } else {
                            nb_bytes = 3;
                        }
                    }
                }
            },
            ExprType::AbsoluteY(variable) => {
                let mut indirect = false;
                let v = self.compiler_state.get_variable(variable);
                signed = v.signed;
                let offset = if v.memory == VariableMemory::Superchip {
                    match mnemonic {
                        STA | STX | STY => 0,
                        _ => 0x80
                    }
                } else if let VariableMemory::MemoryOnChip(_) = v.memory {
                    if self.bankswitching_scheme == "3E" {
                        match mnemonic {
                            STA | STX | STY => 0x400,
                            _ => 0 
                        }
                    } else if self.bankswitching_scheme == "3EP" {
                        match mnemonic {
                            STA | STX | STY => 0x200,
                            _ => 0 
                        }
                    } else { 0 }
                } else { 0 };
                if v.var_type == VariableType::CharPtrPtr || v.var_type == VariableType::ShortPtr {
                    let off = offset + if high_byte { v.size } else { 0 };
                    if off > 0 {
                        dasm_operand = format!("{}+{},Y", variable, off);
                    } else {
                        dasm_operand = format!("{},Y", variable);
                    }
                    cycles += 2;
                    if v.memory == VariableMemory::Zeropage {
                        match mnemonic {
                            STX | LDX => {
                                nb_bytes = 2;
                            },
                            _ => {
                                nb_bytes = 3;
                            }
                        }
                    } else {
                        nb_bytes = 3;
                    }
                    match mnemonic {
                        STA => cycles += 1,
                        STY | LDY | CPY => return Err(self.compiler_state.syntax_error("Can't use Y addressing on Y operation", pos)),
                        CPX => return Err(self.compiler_state.syntax_error("Can't use Y addressing on compare with X operation", pos)),
                        STX => if v.memory != VariableMemory::Zeropage { return Err(self.compiler_state.syntax_error("Can't use Y addressing on a non zeropage variable with X storage", pos)) }, 
                        _ => () 
                    }
                } else if high_byte {
                    dasm_operand = "#0".to_string();
                    nb_bytes = 2;
                } else if v.var_type == VariableType::CharPtr && !v.var_const {
                    if v.size == 1 {
                        if offset > 0 {
                            dasm_operand = format!("({}+{}),Y", variable, offset);
                        } else {
                            dasm_operand = format!("({}),Y", variable);
                        }
                        if v.memory != VariableMemory::Zeropage {
                            return Err(self.compiler_state.syntax_error("Y indirect addressing works only on zeropage variables", pos))
                        }
                        nb_bytes = 2;
                        cycles = if mnemonic == STA {6} else {5};
                        indirect = true;
                        match mnemonic {
                            STX | STY | LDX | LDY | CPX | CPY => return Err(self.compiler_state.syntax_error("Can't use Y indirect addressing on X or Y operation", pos)),
                            _ => () 
                        }
                    } else {
                        return Err(self.compiler_state.syntax_error("X-Indirect adressing mode not available with Y register", pos));
                    }
                } else {
                    if offset > 0 {
                        dasm_operand = format!("{}+{},Y", variable, offset);
                    } else {
                        dasm_operand = format!("{},Y", variable);
                    }
                    cycles += 2;
                    if v.memory == VariableMemory::Zeropage {
                        match mnemonic {
                            STX | LDX => {
                                nb_bytes = 2;
                            },
                            _ => {
                                nb_bytes = 3;
                            }
                        }
                    } else {
                        nb_bytes = 3;
                    }
                    match mnemonic {
                        STA => cycles += 1,
                        STY | LDY | CPY => return Err(self.compiler_state.syntax_error("Can't use Y addressing on Y operation", pos)),
                        CPX => return Err(self.compiler_state.syntax_error("Can't use Y addressing on compare with X operation", pos)),
                        STX => if v.memory != VariableMemory::Zeropage { return Err(self.compiler_state.syntax_error("Can't use Y addressing on a non zeropage variable with X storage", pos)) }, 
                        _ => () 
                    }
                }
                if v.memory != VariableMemory::Zeropage || indirect { cycles_alt = Some(cycles + 1); }
            },
            ExprType::AbsoluteX(variable) => {
                let v = self.compiler_state.get_variable(variable);
                signed = v.signed;
                let offset = if v.memory == VariableMemory::Superchip {
                    match mnemonic {
                        STA | STX | STY => 0,
                        _ => 0x80
                    }
                } else if let VariableMemory::MemoryOnChip(_) = v.memory {
                    if self.bankswitching_scheme == "3E" {
                        match mnemonic {
                            STA | STX | STY => 0x400,
                            _ => 0 
                        }
                    } else if self.bankswitching_scheme == "3EP" {
                        match mnemonic {
                            STA | STX | STY => 0x200,
                            _ => 0 
                        }
                    } else { 0 }
                } else { 0 };
                if v.var_type == VariableType::CharPtr && !v.var_const && v.size == 1 {
                    return Err(self.compiler_state.syntax_error("Y-Indirect adressing mode not available with X register", pos));
                }
                let off = if v.var_type == VariableType::CharPtrPtr || v.var_type == VariableType::ShortPtr {
                    offset + if high_byte { v.size } else { 0 }
                } else { offset };
                if high_byte && v.var_type != VariableType::CharPtrPtr && v.var_type != VariableType::ShortPtr {
                    dasm_operand = "#0".to_string();
                    nb_bytes = 2;
                } else {
                    if off > 0 {
                        dasm_operand = format!("{}+{},X", variable, off);
                    } else {
                        dasm_operand = format!("{},X", variable);
                    }
                    cycles += 2;
                    if v.memory == VariableMemory::Zeropage {
                        nb_bytes = 2;
                    } else {
                        if mnemonic == STA { cycles += 1; }
                        nb_bytes = 3;
                    }
                    match mnemonic {
                        STX | LDX | CPX => return Err(self.compiler_state.syntax_error("Can't use X addressing on X operation", pos)),
                        CPY => return Err(self.compiler_state.syntax_error("Can't use X addressing on compare with Y operation", pos)),
                        STY => if v.memory != VariableMemory::Zeropage { return Err(self.compiler_state.syntax_error("Can't use X addressing on a non zeropage variable with Y storage", pos)) }, 
                        _ => () 
                    }
                }
                if v.memory != VariableMemory::Zeropage { cycles_alt = Some(cycles + 1); }
            },
            ExprType::Nothing => {
                dasm_operand = "".to_string();
                signed = false;
                nb_bytes = 1;
            },
            _ => unreachable!()
        }

        let mut s = mnemonic.to_string();
        if !dasm_operand.is_empty() {
            s += " ";
            s += &dasm_operand;
        }

        if let Some(f) = &self.current_function {
            let code : &mut AssemblyCode = self.functions_code.get_mut(f).unwrap();
            let instruction = AsmInstruction {
                mnemonic, dasm_operand, cycles, cycles_alt, nb_bytes, protected: self.protected,
            };
            code.append_asm(instruction);
        }
        Ok(signed)
    }

    pub(crate) fn inline(&mut self, s: &str, size: Option<u32>) -> Result<(), Error> {
        if let Some(f) = &self.current_function {
            let code : &mut AssemblyCode = self.functions_code.get_mut(f).unwrap();
            code.append_inline(s.to_string(), size);
        }
        Ok(()) 
    } 

    pub(crate) fn comment(&mut self, s: &str) -> Result<(), Error> {
        if let Some(f) = &self.current_function {
            let code : &mut AssemblyCode = self.functions_code.get_mut(f).unwrap();
            code.append_comment(s.trim_end().to_string());
        }
        Ok(()) 
    } 

    pub(crate) fn label(&mut self, l: &str) -> Result<(), Error> {
        if let Some(f) = &self.current_function {
            let code : &mut AssemblyCode = self.functions_code.get_mut(f).unwrap();
            code.append_label(l.to_string());
            self.flags = FlagsState::Unknown;
            self.carry_flag_ok = false;
        }
        Ok(()) 
    } 

    pub(crate) fn dummy(&mut self) -> Option<usize> {
        if let Some(f) = &self.current_function {
            let code : &mut AssemblyCode = self.functions_code.get_mut(f).unwrap();
            Some(code.append_dummy())
        } else {
            None
        }
    }

    pub(crate) fn asm_save_y(&mut self, line: usize) {
        if let Some(f) = &self.current_function {
            let code : &mut AssemblyCode = self.functions_code.get_mut(f).unwrap();
            let instruction = AsmInstruction { mnemonic: STY, dasm_operand: "cctmp".into(), cycles: 3, cycles_alt: None, nb_bytes: 2, protected: false };
            code.set(line, instruction);
        }
    }

    pub(crate) fn asm_restore_y(&mut self) {
        if let Some(f) = &self.current_function {
            let code : &mut AssemblyCode = self.functions_code.get_mut(f).unwrap();
            let instruction = AsmInstruction { mnemonic: LDY, dasm_operand: "cctmp".into(), cycles: 3, cycles_alt: None, nb_bytes: 2, protected: false };
            code.append_asm(instruction);
        }
    }

    // Inline code
    pub(crate) fn push_code(&mut self, f: &str, pos: usize) -> Result<(), Error> {
        self.inline_label_counter += 1;
        if let Some(fx) = &self.current_function {
            let code2: AssemblyCode = match self.functions_code.get(f) {
                None => return Err(self.compiler_state.syntax_error("Inline function must be defined before use", pos)),
                Some(c) => c.clone()
            };
            let code : &mut AssemblyCode = self.functions_code.get_mut(fx).unwrap();
            code.append_code(&code2, self.inline_label_counter);
            code.append_label(format!(".endofinline{}", self.inline_label_counter))
        }
        Ok(()) 
    }

    pub fn write_function(&mut self, f: &str) -> Result<usize, std::io::Error>
    {
        let code: &AssemblyCode = self.functions_code.get(f).unwrap();
        code.write(self.writer, self.insert_code)
    }

    pub fn optimize_function(&mut self, f: &str) -> u32 
    {
        let code: &mut AssemblyCode = self.functions_code.get_mut(f).unwrap();
        let nb = code.optimize();
        if nb > 0 {
            info!("#{} optimized out instructions in function {}", nb, f);
        }
        nb
    }

    pub fn check_branches(&mut self, f: &str) -> u32 
    {
        let code: &mut AssemblyCode = self.functions_code.get_mut(f).unwrap();
        let nb = code.check_branches();
        if nb > 0 {
            info!("#{} too far relative branch fixes in function {}", nb, f);
        }
        nb
    }

    pub fn write(&mut self, s: &str) -> Result<usize, std::io::Error> {
        self.writer.write(s.as_bytes())
    }
    
    fn function_is_actually_in_use(&self, f: &str, functions_actually_in_use: &mut HashSet<String>) {
        if functions_actually_in_use.get(f).is_none() {
            functions_actually_in_use.insert(f.to_string());
            if let Some(v) = self.functions_call_tree.get(f) {
                for fx in v {
                    self.function_is_actually_in_use(fx, functions_actually_in_use);
                }
            }
        }
    }

    pub fn compute_functions_actually_in_use(&mut self) -> Result<(), Error>
    {
        let mut functions_actually_in_use = HashSet::<String>::new();
        self.function_is_actually_in_use("main", &mut functions_actually_in_use);
        for i in &self.compiler_state.functions {
            if i.1.interrupt {
                self.function_is_actually_in_use(i.0, &mut functions_actually_in_use);
            }    
        }
        debug!("Functions actually in use: {:?}", functions_actually_in_use);
        self.functions_actually_in_use = functions_actually_in_use;
        Ok(())
    }
}
