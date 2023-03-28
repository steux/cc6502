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

use std::io::Write;
use log::debug;

use crate::error::Error;
use crate::compile::*;
use crate::assemble::AssemblyCode;
use crate::generate::*;
use crate::Args;

pub fn simple_build(compiler_state: &CompilerState, writer: &mut dyn Write, args: &Args) -> Result<(), Error> 
{
    // Start generation
    let mut gstate = GeneratorState::new(compiler_state, writer, args.insert_code, "4K");
    gstate.write("\tPROCESSOR 6502\n\n")?;
    
    for v in compiler_state.sorted_variables().iter() {
        if v.1.var_const  {
            if let VariableDefinition::Value(val) = &v.1.def  {
                gstate.write(&format!("{:23}\tEQU ${:x}\n", v.0, val))?;
            }
        }
    }

    gstate.write("\n\tSEG.U VARS\n\tORG $80\n\n")?;
    
    // Generate variables code
    gstate.write("cctmp                  \tds 1\n")?; 
    for v in compiler_state.sorted_variables().iter() {
       // debug!("{:?}",v);
        if v.1.memory == VariableMemory::Zeropage && v.1.def == VariableDefinition::None {
            if v.1.size > 1 {
                let s = match v.1.var_type {
                    VariableType::CharPtr => 1,
                    VariableType::CharPtrPtr => 2,
                    VariableType::ShortPtr => 2,
                    _ => unreachable!()
                };
                gstate.write(&format!("{:23}\tds {}\n", v.0, v.1.size * s))?; 
            } else {
                let s = match v.1.var_type {
                    VariableType::Char => 1,
                    VariableType::Short => 2,
                    VariableType::CharPtr => 2,
                    VariableType::CharPtrPtr => 2,
                    VariableType::ShortPtr => 2,
                };
                gstate.write(&format!("{:23}\tds {}\n", v.0, s))?; 
            }
        }
    }

    // Generate functions code
    gstate.write("\n; Functions definitions\n\tSEG CODE\n")?;

    for f in compiler_state.sorted_functions().iter() {
        if f.1.code.is_some() {
            gstate.local_label_counter_for = 0;
            gstate.local_label_counter_if = 0;

            gstate.functions_code.insert(f.0.clone(), AssemblyCode::new());
            gstate.current_function = Some(f.0.clone());
            gstate.generate_statement(f.1.code.as_ref().unwrap())?;
            gstate.current_function = None;

            if args.optimization_level > 0 {
                gstate.optimize_function(f.0);
            }
            gstate.check_branches(f.0);
        }
    }

    // Generate code for all banks
    gstate.write("\n\tORG $1000\n\tRORG $1000\n")?;

    // Generate functions code
    for f in compiler_state.sorted_functions().iter() {
        if f.1.code.is_some() && !f.1.inline{
            debug!("Generating code for function #{}", f.0);

            gstate.write(&format!("\n{}\tSUBROUTINE\n", f.0))?;
            gstate.write_function(f.0)?;
            gstate.write("\tRTS\n")?;
        }
    }

    // Generate ROM tables
    gstate.write("\n; Tables in ROM\n")?;
    for v in compiler_state.sorted_variables().iter() {
        if let VariableMemory::ROM(rom_bank) = v.1.memory {
            match &v.1.def {
                VariableDefinition::Array(arr) => {
                    if v.1.alignment != 1 {
                        gstate.write(&format!("\n\talign {}\n", v.1.alignment))?;
                    }
                    gstate.write(v.0)?;
                    let mut counter = 0;
                    for i in arr {
                        if counter == 0 {
                            gstate.write("\n\thex ")?;
                        }
                        counter += 1;
                        if counter == 16 { counter = 0; }
                        gstate.write(&format!("{:02x}", i & 0xff))?;
                    } 
                    if v.1.var_type == VariableType::ShortPtr {
                        for i in arr {
                            if counter == 0 {
                                gstate.write("\n\thex ")?;
                            }
                            counter += 1;
                            if counter == 16 { counter = 0; }
                            gstate.write(&format!("{:02x}", (i >> 8) & 0xff))?;
                        } 
                    }
                    gstate.write("\n")?;
                },
                VariableDefinition::ArrayOfPointers(arr) => {
                    if v.1.alignment != 1 {
                        gstate.write(&format!("\n\talign {}\n", v.1.alignment))?;
                    }
                    gstate.write(v.0)?;

                    let mut counter = 0;
                    for i in arr {
                        if counter % 8 == 0 {
                            gstate.write("\n\t.byte ")?;
                        }
                        counter += 1;
                        gstate.write(&format!("<{}", i))?;
                        if counter % 8 != 0 {
                            gstate.write(", ")?;
                        } 
                    } 
                    for i in arr {
                        if counter % 8 == 0 {
                            gstate.write("\n\t.byte ")?;
                        }
                        counter += 1;
                        gstate.write(&format!(">{}", i))?;
                        if counter % 8 != 0 && counter < 2 * arr.len() {
                            gstate.write(", ")?;
                        } 
                    } 
                    gstate.write("\n")?;
                },
                _ => ()
            };
        }
    }
            
    gstate.write("\tEND\n")?;
    Ok(())
}
