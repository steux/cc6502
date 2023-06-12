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
use std::io::Write;
use regex::Regex;

use crate::compile::*;

use crate::assemble::AssemblyCode;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum ExprType<'a> {
    Nothing,
    Immediate(i32),
    Tmp(bool),
    Absolute(&'a str, bool, i32), // variable, eight_bits, offset
    AbsoluteX(&'a str),
    AbsoluteY(&'a str),
    A(bool), X, Y,
    Label(&'a str),
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum FlagsState<'a> {
    Unknown,
    A, X, Y,
    Absolute(&'a str, bool, i32),
    AbsoluteX(&'a str),
    AbsoluteY(&'a str),
}

pub struct GeneratorState<'a> {
    compiler_state: &'a CompilerState<'a>,
    last_included_line_number: usize,
    last_included_position: usize,
    last_included_char: std::str::Chars<'a>,
    writer: &'a mut dyn Write,
    pub local_label_counter_for: u32,
    pub local_label_counter_if: u32,
    local_label_counter_while: u32,
    inline_label_counter: u32,
    loops: Vec<(String,String,bool)>,
    flags: FlagsState<'a>,
    carry_flag_ok: bool,
    acc_in_use: bool,
    tmp_in_use: bool,
    insert_code: bool,
    whitespaces_regex: Regex,
    deferred_plusplus: Vec<(ExprType<'a>, usize, bool)>,
    pub current_bank: u32,
    pub functions_code: HashMap<String, AssemblyCode>,
    pub functions_call_tree: HashMap<String, Vec<String>>,
    pub functions_actually_in_use: HashSet<String>,
    pub current_function: Option<String>,
    bankswitching_scheme: &'a str,
    protected: bool,
    carry_propagation_error: bool,
}

pub mod generate_asm;
pub mod generate_conditions;
pub mod generate_statements;
pub mod generate_arithm;
pub mod generate_assign;
