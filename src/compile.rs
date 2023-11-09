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

use std::{collections::HashMap, hash::Hash, unreachable};
use std::rc::Rc;
use std::sync::Mutex;

use log::debug;

use pest::{Parser, pratt_parser::{Op, PrattParser, Assoc}, iterators::{Pair, Pairs}, error::LineColLocation};
use std::io::{BufRead, Write};

use crate::error::Error;
use crate::cpp;
use crate::Args;

#[derive(Parser)]
#[grammar = "cc6502.pest"]
struct Cc2600Parser;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum VariableType {
    Char,
    Short,
    CharPtr,
    CharPtrPtr,
    ShortPtr,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum VariableMemory {
    ROM(u32),
    Zeropage,
    Superchip,
    Display,
    Frequency,
    Ramchip,
    MemoryOnChip(u32),
}

#[derive(Debug, PartialEq)]
pub enum VariableValue {
    Int(i32),
    LowPtr((String, usize)),
    HiPtr((String, usize)),
}

#[derive(Debug, PartialEq)]
pub enum VariableDefinition {
    None,
    Value(VariableValue),
    Array(Vec<VariableValue>),
    ArrayOfPointers(Vec<(String, usize)>),
}

#[derive(Debug)]
pub struct Variable {
    order: usize,
    pub var_type: VariableType,
    pub var_const: bool,
    pub signed: bool,
    pub memory: VariableMemory,
    pub size: usize,
    pub alignment: usize,
    pub def: VariableDefinition,
    pub reversed: bool,
    pub scattered: Option<(u32, u32)>,
    pub holeydma: bool,
    pub global: bool
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Operation {
    Mul(bool),
    Div(bool),
    Add(bool),
    Sub(bool),
    And(bool),
    Or(bool),
    Xor(bool),
    Brs(bool),
    Bls(bool),
    Assign,
    Eq,
    Neq,
    Gt,
    Gte,
    Lt,
    Lte,
    Land,
    Lor,
    TernaryCond1,
    TernaryCond2,
    Comma
}

#[derive(Debug, Clone)]
pub enum Expr {
    Nothing,
    Integer(i32),
    Identifier(String, Box<Expr>),
    FunctionCall(Box<Expr>, Box<Expr>),
    BinOp {
        lhs: Box<Expr>,
        op: Operation,
        rhs: Box<Expr>,
    },
    Neg(Box<Expr>),
    Not(Box<Expr>),
    BNot(Box<Expr>),
    MinusMinus(Box<Expr>, bool),
    PlusPlus(Box<Expr>, bool),
    Deref(Box<Expr>),
    Addr(Box<Expr>),
    Sizeof(Box<Expr>),
    Type(String),
    TmpId(String),
}

#[derive(Debug, Clone)]
pub(crate) enum Statement<'a> {
    Block(Vec<StatementLoc<'a>>),
    Expression(Expr),
    For { 
        init: Expr,
        condition: Expr,
        update: Expr,
        body: Box<StatementLoc<'a>>
    },
    If {
        condition: Expr,
        body: Box<StatementLoc<'a>>,
        else_body: Option<Box<StatementLoc<'a>>>
    },
    While {
        condition: Expr,
        body: Box<StatementLoc<'a>>,
    },
    DoWhile {
        body: Box<StatementLoc<'a>>,
        condition: Expr,
    },
    Switch {
        expr: Expr,
        cases: Vec<(Vec<i32>, Vec<StatementLoc<'a>>)>
    },
    Break,
    Continue,
    Return(Expr),
    Asm(String, Option<u32>),
    Strobe(Expr),
    Load(Expr),
    Store(Expr),
    CSleep(i32),
    Goto(&'a str),
    LocalVarDecl,
}

#[derive(Debug, Clone)]
pub struct StatementLoc<'a> {
    pub(crate) pos: usize,
    pub(crate) label: Option<String>,
    pub(crate) statement: Statement<'a>
}

#[derive(Debug)]
pub struct Function<'a> {
    order: usize,
    pub inline: bool,
    pub bank: u32,
    pub interrupt: bool,
    pub(crate) return_signed: bool,
    pub(crate) return_type: Option<VariableType>,
    pub code: Option<StatementLoc<'a>>,
    pub local_variables: Vec<String>,
    pub(crate) parameters: Vec<String>,
    pub(crate) stack_frame_size: usize,
}

pub struct CompilerState<'a> {
    pub variables: HashMap<String, Variable>,
    pub functions: HashMap<String, Function<'a>>,
    pratt: PrattParser<Rule>,
    pratt_init_value: PrattParser<Rule>,
    calculator: PrattParser<Rule>,
    mapped_lines: &'a Vec::<(std::rc::Rc::<String>,u32,Option<(std::rc::Rc::<String>,u32)>)>,
    pub preprocessed_utf8: &'a str,
    pub included_assembler: Vec::<(String, Option<String>, Option<usize>, Option<u8>)>,
    pub context: cpp::Context,
    signed_chars: bool,
    literal_counter: usize,
    in_scope_variables: Vec<HashMap<String, String>>,
    current_function: String,
    variable_counter: u32,
}

impl<'a> CompilerState<'a> {
    
    pub fn sorted_variables(&self) -> Vec<(&String, &Variable)> {
        let mut v: Vec<(&String, &Variable)> = self.variables.iter().collect();
        v.sort_by(|a, b| a.1.order.cmp(&b.1.order));
        v
    }

    pub fn get_variable(&self, name: &str) -> &Variable {
        self.variables.get(name).unwrap()
    }

    pub fn sorted_functions(&self) -> Vec<(&String, &Function)> {
        let mut v: Vec<(&String, &Function)> = self.functions.iter().collect();
        v.sort_by(|a, b| a.1.order.cmp(&b.1.order));
        v
    }

    pub fn syntax_error(&self, message: &str, loc: usize) -> Error
    {
        let mut line_number: usize = 0;
        let mut char_number = 0;
        for c in self.preprocessed_utf8.chars() {
            if c == '\n' { line_number += 1; }
            char_number += 1;
            if char_number == loc { break; }
        }
        let included_in = self.mapped_lines[line_number].2.as_ref().map(|iin| (iin.0.to_string(), iin.1));
        Error::Syntax {
            filename: self.mapped_lines[line_number].0.to_string(),
            line: self.mapped_lines[line_number].1,
            included_in,
            msg: message.to_string()
        }
    }

    pub fn warning(&self, msg: &str, loc: usize) -> () 
    {
        let mut line_number: usize = 0;
        let mut char_number = 0;
        for c in self.preprocessed_utf8.chars() {
            if c == '\n' { line_number += 1; }
            char_number += 1;
            if char_number == loc { break; }
        }
        let included_in = self.mapped_lines[line_number].2.as_ref().map(|iin| (iin.0.to_string(), iin.1));
        let filename = self.mapped_lines[line_number].0.to_string();
        let line = self.mapped_lines[line_number].1;
        match included_in {
            Some(include) => println!("Warning: {} on line {} of {} (included in {} on line {})", msg, line, filename, include.0, include.1),
            None => println!("Warning: {} on line {} of {}", msg, line, filename)
        }
    }

    fn parse_identifier(&'a self, pairs: Pairs<'a, Rule>) -> Result<(String, Box<Expr>), Error>
    {
        let mut p = pairs;
        let px = p.next().unwrap();
        let varname = px.as_str();
        let subscript = match p.next() {
            Some(pair) => {
                let expr = self.parse_expr_ex(pair.into_inner())?;
                Box::new(expr.0)
            },
            None => Box::new(Expr::Nothing), 
        };
        if varname.eq("X") || varname.eq("Y") {
            match *subscript {
                Expr::Nothing => return Ok((varname.into(), subscript)),
                _ => return Err(self.syntax_error(&format!("No subscript for {} index", varname), px.as_span().start())),
            }
        }

        match self.in_scope_variables.last() {
            Some(vars) => {
                match vars.get(varname) {
                    Some(vn) => {
                        return Ok((vn.clone(), subscript))
                    },
                    None => match self.functions.get(varname) {
                        Some(_var) => {
                            match *subscript {
                                Expr::Nothing => Ok((varname.into(), subscript)),
                                _ => Err(self.syntax_error("No subscript for functions", px.as_span().start())),
                            }
                        },
                        None => Err(self.syntax_error(&format!("Unknown identifier {}", varname), px.as_span().start()))
                    }
                }
            },
            None => {
                match self.variables.get(varname) {
                    Some(_var) => {
                        Ok((varname.into(), subscript))
                    },
                    None => {
                        match self.functions.get(varname) {
                            Some(_var) => {
                                match *subscript {
                                    Expr::Nothing => Ok((varname.into(), subscript)),
                                    _ => Err(self.syntax_error("No subscript for functions", px.as_span().start())),
                                }
                            },
                            None => Err(self.syntax_error(&format!("Unknown identifier {}", varname), px.as_span().start()))
                        }
                    }

                } 
            }
        }
    }

    fn parse_expr(&mut self, pairs: Pairs<'a, Rule>) -> Result<Expr, Error>
    {
        let res = self.parse_expr_ex(pairs)?;

        // Create collected literal variables in memory
        self.literal_counter += res.1.len();
        for k in &res.1 {
            let vb = k.1.as_bytes();
            let mut v = Vec::<VariableValue>::new();
            for c in vb.iter() {
                v.push(VariableValue::Int(*c as i32));
            }
            let size = v.len();
            self.variables.insert(k.0.clone(), Variable {
                order: self.variables.len(),
                signed: false,
                memory: VariableMemory::ROM(0),
                var_const: true,
                alignment: 1,
                def: VariableDefinition::Array(v),
                var_type: VariableType::CharPtr, size,
                reversed: false,
                scattered: None,
                holeydma: false,
                global: true,
            });
        }
        Ok(res.0)
    }

    fn parse_expr_ex(&self, pairs: Pairs<'a, Rule>) -> Result<(Expr, HashMap<String, String>), Error>
    {
        let literal_counter = Rc::new(Mutex::new(self.literal_counter));
        let literal_strings = Rc::new(Mutex::new(HashMap::<String, String>::new())); 
        let res = self.pratt
            .map_primary(|primary| -> Result<Expr, Error> {
                match primary.as_rule() {
                    Rule::int => Ok(Expr::Integer(parse_int(primary.into_inner().next().unwrap()))),
                    Rule::expr => {
                        let res = self.parse_expr_ex(primary.into_inner())?;
                        let mut lit_strs = literal_strings.lock().unwrap();
                        for k in &res.1 {
                            lit_strs.insert(k.0.clone(), k.1.clone());
                        }
                        let mut l = literal_counter.lock().unwrap();
                        *l += res.1.len();
                        Ok(res.0) 
                    },
                    Rule::identifier => {
                        let id = self.parse_identifier(primary.into_inner())?;
                        Ok(Expr::Identifier(id.0, id.1))
                    },
                    Rule::quoted_string => {
                        // Create a temp variable pointing to this quoted_string
                        let v = self.compile_quoted_string(primary);
                        let mut l = literal_counter.lock().unwrap();
                        let name = format!("cctmp{}", l);
                        *l += 1;
                        let mut lit_strs = literal_strings.lock().unwrap();
                        lit_strs.insert(name.clone(), v);
                        Ok(Expr::TmpId(name))
                    },
                    Rule::primary_var_type => Ok(Expr::Type(primary.as_str().into())),
                    rule => unreachable!("Expr::parse expected atom, found {:?}", rule),
                }
            })
        .map_infix(|lhs, op, rhs| {
            let op = match op.as_rule() {
                Rule::mul => Operation::Mul(false),
                Rule::div => Operation::Div(false),
                Rule::add => Operation::Add(false),
                Rule::sub => Operation::Sub(false),
                Rule::and => Operation::And(false),
                Rule::or => Operation::Or(false),
                Rule::xor => Operation::Xor(false),
                Rule::brs => Operation::Brs(false),
                Rule::bls => Operation::Bls(false),
                Rule::eq => Operation::Eq,
                Rule::neq => Operation::Neq,
                Rule::assign => Operation::Assign,
                Rule::gt => Operation::Gt,
                Rule::gte => Operation::Gte,
                Rule::lt => Operation::Lt,
                Rule::lte => Operation::Lte,
                Rule::mulass => Operation::Mul(true),
                Rule::divass => Operation::Div(true),
                Rule::pass => Operation::Add(true),
                Rule::mass => Operation::Sub(true),
                Rule::blsass => Operation::Bls(true),
                Rule::brsass => Operation::Brs(true),
                Rule::andass => Operation::And(true),
                Rule::orass => Operation::Or(true),
                Rule::xorass => Operation::Xor(true),
                Rule::land => Operation::Land,
                Rule::lor => Operation::Lor,
                Rule::ternary_cond1 => Operation::TernaryCond1,
                Rule::ternary_cond2 => Operation::TernaryCond2,
                Rule::comma => Operation::Comma,
                rule => unreachable!("Expr::parse expected infix operation, found {:?}", rule),
            };
            Ok(Expr::BinOp {
                lhs: Box::new(lhs?),
                op,
                rhs: Box::new(rhs?),
            })
        })
        .map_prefix(|op, rhs| match op.as_rule() {
            Rule::neg => Ok(Expr::Neg(Box::new(rhs?))),
            Rule::not => Ok(Expr::Not(Box::new(rhs?))),
            Rule::bnot => Ok(Expr::BNot(Box::new(rhs?))),
            Rule::deref => Ok(Expr::Deref(Box::new(rhs?))),
            Rule::addr => Ok(Expr::Addr(Box::new(rhs?))),
            Rule::mmp => Ok(Expr::MinusMinus(Box::new(rhs?), false)),
            Rule::ppp => Ok(Expr::PlusPlus(Box::new(rhs?), false)),
            Rule::sizeof => Ok(Expr::Sizeof(Box::new(rhs?))),
            _ => unreachable!(),
        })
        .map_postfix(|lhs, op| match op.as_rule() {
            Rule::mm => Ok(Expr::MinusMinus(Box::new(lhs?), true)),
            Rule::pp => Ok(Expr::PlusPlus(Box::new(lhs?), true)),
            Rule::call => {
                let params = if let Some(x) = op.into_inner().next() {
                    let res = self.parse_expr_ex(x.into_inner())?;
                    let mut lit_strs = literal_strings.lock().unwrap();
                    for k in &res.1 {
                        lit_strs.insert(k.0.clone(), k.1.clone());
                    }
                    let mut l = literal_counter.lock().unwrap();
                    *l += res.1.len();
                    res.0 
                } else { Expr::Nothing };
                Ok(Expr::FunctionCall(Box::new(lhs?), Box::new(params)))
            },             
            _ => unreachable!(),
        })
        .parse(pairs);
        let lit_strs = Rc::into_inner(literal_strings).unwrap().into_inner().unwrap();
        match res {
            Ok(r) => Ok((r, lit_strs)),
            Err(x) => Err(x),
        }
    }

    fn parse_expr_init_value(&mut self, pairs: Pairs<'a, Rule>) -> Result<Expr, Error>
    {
        let res = self.parse_expr_init_value_ex(pairs)?;

        // Create collected literal variables in memory
        self.literal_counter += res.1.len();
        for k in &res.1 {
            let vb = k.1.as_bytes();
            let mut v = Vec::<VariableValue>::new();
            for c in vb.iter() {
                v.push(VariableValue::Int(*c as i32));
            }
            let size = v.len();
            self.variables.insert(k.0.clone(), Variable {
                order: self.variables.len(),
                signed: false,
                memory: VariableMemory::ROM(0),
                var_const: true,
                alignment: 1,
                def: VariableDefinition::Array(v),
                var_type: VariableType::CharPtr, size,
                reversed: false,
                scattered: None,
                holeydma: false,
                global: true,
            });
        }
        Ok(res.0)
    }

    fn parse_expr_init_value_ex(&self, pairs: Pairs<'a, Rule>) -> Result<(Expr, HashMap<String, String>), Error>
    {
        let literal_counter = Rc::new(Mutex::new(self.literal_counter));
        let literal_strings = Rc::new(Mutex::new(HashMap::<String, String>::new())); 
        let res = self.pratt_init_value
            .map_primary(|primary| -> Result<Expr, Error> {
                match primary.as_rule() {
                    Rule::int => Ok(Expr::Integer(parse_int(primary.into_inner().next().unwrap()))),
                    Rule::expr => {
                        let res = self.parse_expr_ex(primary.into_inner())?;
                        let mut lit_strs = literal_strings.lock().unwrap();
                        for k in &res.1 {
                            lit_strs.insert(k.0.clone(), k.1.clone());
                        }
                        let mut l = literal_counter.lock().unwrap();
                        *l += res.1.len();
                        Ok(res.0) 
                    },
                    Rule::identifier => {
                        let id = self.parse_identifier(primary.into_inner())?;
                        Ok(Expr::Identifier(id.0, id.1))
                    },
                    Rule::quoted_string => {
                        // Create a temp variable pointing to this quoted_string
                        let v = self.compile_quoted_string(primary);
                        let mut l = literal_counter.lock().unwrap();
                        let name = format!("cctmp{}", l);
                        *l += 1;
                        let mut lit_strs = literal_strings.lock().unwrap();
                        lit_strs.insert(name.clone(), v);
                        Ok(Expr::TmpId(name))
                    },
                    Rule::primary_var_type => Ok(Expr::Type(primary.as_str().into())),
                    rule => unreachable!("Expr::parse expected atom, found {:?}", rule),
                }
            })
        .map_infix(|lhs, op, rhs| {
            let op = match op.as_rule() {
                Rule::mul => Operation::Mul(false),
                Rule::div => Operation::Div(false),
                Rule::add => Operation::Add(false),
                Rule::sub => Operation::Sub(false),
                Rule::and => Operation::And(false),
                Rule::or => Operation::Or(false),
                Rule::xor => Operation::Xor(false),
                Rule::brs => Operation::Brs(false),
                Rule::bls => Operation::Bls(false),
                Rule::eq => Operation::Eq,
                Rule::neq => Operation::Neq,
                Rule::assign => Operation::Assign,
                Rule::gt => Operation::Gt,
                Rule::gte => Operation::Gte,
                Rule::lt => Operation::Lt,
                Rule::lte => Operation::Lte,
                Rule::mulass => Operation::Mul(true),
                Rule::divass => Operation::Div(true),
                Rule::pass => Operation::Add(true),
                Rule::mass => Operation::Sub(true),
                Rule::blsass => Operation::Bls(true),
                Rule::brsass => Operation::Brs(true),
                Rule::andass => Operation::And(true),
                Rule::orass => Operation::Or(true),
                Rule::xorass => Operation::Xor(true),
                Rule::land => Operation::Land,
                Rule::lor => Operation::Lor,
                Rule::ternary_cond1 => Operation::TernaryCond1,
                Rule::ternary_cond2 => Operation::TernaryCond2,
                rule => unreachable!("Expr::parse expected infix operation, found {:?}", rule),
            };
            Ok(Expr::BinOp {
                lhs: Box::new(lhs?),
                op,
                rhs: Box::new(rhs?),
            })
        })
        .map_prefix(|op, rhs| match op.as_rule() {
            Rule::neg => Ok(Expr::Neg(Box::new(rhs?))),
            Rule::not => Ok(Expr::Not(Box::new(rhs?))),
            Rule::bnot => Ok(Expr::BNot(Box::new(rhs?))),
            Rule::deref => Ok(Expr::Deref(Box::new(rhs?))),
            Rule::addr => Ok(Expr::Addr(Box::new(rhs?))),
            Rule::mmp => Ok(Expr::MinusMinus(Box::new(rhs?), false)),
            Rule::ppp => Ok(Expr::PlusPlus(Box::new(rhs?), false)),
            Rule::sizeof => Ok(Expr::Sizeof(Box::new(rhs?))),
            _ => unreachable!(),
        })
        .map_postfix(|lhs, op| match op.as_rule() {
            Rule::mm => Ok(Expr::MinusMinus(Box::new(lhs?), true)),
            Rule::pp => Ok(Expr::PlusPlus(Box::new(lhs?), true)),
            Rule::call => {
                let params = if let Some(x) = op.into_inner().next() {
                    let res = self.parse_expr_ex(x.into_inner())?;
                    let mut lit_strs = literal_strings.lock().unwrap();
                    for k in &res.1 {
                        lit_strs.insert(k.0.clone(), k.1.clone());
                    }
                    let mut l = literal_counter.lock().unwrap();
                    *l += res.1.len();
                    res.0 
                } else { Expr::Nothing };
                Ok(Expr::FunctionCall(Box::new(lhs?), Box::new(params)))
            },             
            _ => unreachable!(),
        })
        .parse(pairs);
        let lit_strs = Rc::into_inner(literal_strings).unwrap().into_inner().unwrap();
        match res {
            Ok(r) => Ok((r, lit_strs)),
            Err(x) => Err(x),
        }
    }

    fn compile_statement(&mut self, p: Pair<'a, Rule>) -> Result<StatementLoc<'a>, Error>
    {
        let mut inner = p.into_inner();
        let pair = inner.next().unwrap();
        //debug!("Compile statement: {:?}\ninner:{:?}", pair, inner);
        let pos = pair.as_span().start();
        match pair.as_rule() {
            Rule::label => {
                let statement = self.compile_statement_ex(inner.next().unwrap())?;
                Ok(StatementLoc { pos, label: Some(pair.into_inner().next().unwrap().as_str().to_string()), statement: statement.statement })
            },
            _ => {
                self.compile_statement_ex(pair)
            }
        }
    }

    fn compile_statement_ex(&mut self, pair: Pair<'a, Rule>) -> Result<StatementLoc<'a>, Error>
    {
        let pos = pair.as_span().start();
        match pair.as_rule() {
            Rule::expr => {
                let expr = self.parse_expr(pair.into_inner())?;
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Expression(expr)
                })
            },
            Rule::block => {
                let c = self.in_scope_variables.last().unwrap();
                self.in_scope_variables.push(c.clone());
                let ret = self.compile_block(pair);
                self.in_scope_variables.pop();
                ret
            },
            Rule::local_var_decl => {
                self.compile_local_var_decl(pair.into_inner())
            }
            Rule::for_loop => {
                let mut p = pair.into_inner();
                let i = p.next().unwrap();
                let init = match i.as_rule() {
                    Rule::nothing => Expr::Nothing,
                    _ => self.parse_expr(i.into_inner())?
                };
                let condition = self.parse_expr(p.next().unwrap().into_inner())?;
                let update = self.parse_expr(p.next().unwrap().into_inner())?;
                let body = self.compile_statement(p.next().unwrap())?;
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::For {
                        init, condition, update, body: Box::new(body) 
                    }
                })
            },
            Rule::if_statement => {
                let mut p = pair.into_inner();
                let condition = self.parse_expr(p.next().unwrap().into_inner())?;
                let body = self.compile_statement(p.next().unwrap())?;
                let else_body = match p.next() {
                    None => None,
                    Some(px) => Some(Box::new(self.compile_statement(px)?)),
                };
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::If {
                        condition, body: Box::new(body), else_body 
                    }
                })
            },
            Rule::do_while => {
                let mut p = pair.into_inner();
                let body = self.compile_statement(p.next().unwrap())?;
                let condition = self.parse_expr(p.next().unwrap().into_inner())?;
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::DoWhile {
                        body: Box::new(body), condition  
                    }
                })
            },
            Rule::while_do => {
                let mut p = pair.into_inner();
                let condition = self.parse_expr(p.next().unwrap().into_inner())?;
                let body = self.compile_statement(p.next().unwrap())?;
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::While {
                        condition, body: Box::new(body) 
                    }
                })
            },
            Rule::switch_statement => {
                let mut p = pair.into_inner();
                let mut cases = Vec::<(Vec<i32>, Vec<StatementLoc<'a>>)>::new();
                let expr = self.parse_expr(p.next().unwrap().into_inner())?;
                let c = p.next().unwrap().into_inner();
                debug!("Cases: {:?}", c);
                let mut case_set = (Vec::<i32>::new(), Vec::<StatementLoc<'a>>::new());
                let mut last_was_a_statement = false;
                for i in c {
                    match i.as_rule() {
                        Rule::int => {
                            if last_was_a_statement {
                                cases.push(case_set.clone());
                                case_set = (Vec::<i32>::new(), Vec::<StatementLoc<'a>>::new());
                                last_was_a_statement = false;
                            }
                            case_set.0.push(parse_int(i.into_inner().next().unwrap()));
                        },
                        Rule::statement => {
                            case_set.1.push(self.compile_statement(i)?);
                            last_was_a_statement = true;
                        },
                        Rule::default_case => {
                            cases.push(case_set.clone());
                            let mut default_set = (Vec::<i32>::new(), Vec::<StatementLoc<'a>>::new());
                            let d = i.into_inner();
                            for j in d {
                                match j.as_rule() {
                                    Rule::statement => {
                                        default_set.1.push(self.compile_statement(j)?);
                                    },
                                    _ => unreachable!()
                                }
                            }
                            cases.push(default_set);
                            last_was_a_statement = false;
                        },
                        _ => unreachable!()
                    }
                }
                if last_was_a_statement {
                    cases.push(case_set.clone());
                }
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Switch {
                        expr, cases 
                    }
                })
            },
            Rule::break_statement => {
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Break
                })
            },
            Rule::continue_statement => {
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Continue
                })
            },
            Rule::return_statement => {
                let mut p = pair.into_inner();
                let i = p.next().unwrap();
                let return_value = match i.as_rule() {
                    Rule::nothing => Expr::Nothing,
                    _ => self.parse_expr(i.into_inner())?
                };
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Return(return_value)
                })
            },
            Rule::asm_statement => {
                let mut px = pair.into_inner();
                let mut s = self.compile_quoted_string(px.next().unwrap());
                let size = if let Some(x) = px.next() {
                    Some(self.parse_calc(x.into_inner())? as u32)
                } else { None };
                s.pop();
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Asm(s, size)
                })
            },
            Rule::strobe_statement => {
                let s = self.parse_expr(pair.into_inner())?;
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Strobe(s)
                })
            },
            Rule::load_statement => {
                let s = self.parse_expr(pair.into_inner())?;
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Load(s)
                })
            },
            Rule::store_statement => {
                let s = self.parse_expr(pair.into_inner())?;
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Store(s)
                })
            },
            Rule::csleep_statement => {
                let s = parse_int(pair.into_inner().next().unwrap().into_inner().next().unwrap());
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::CSleep(s)
                })
            },
            Rule::goto_statement => {
                let s = pair.into_inner().next().unwrap().as_str();
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Goto(s)
                })
            },
            Rule::nothing => {
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Expression(Expr::Nothing)
                })
            },
            _ => {
                debug!("What's this ? {:?}", pair);
                unreachable!()
            }
        }
    }

    fn parse_calc(&self, pairs: Pairs<'a, Rule>) -> Result<i32, Error>
    {
        self.calculator
            .map_primary(|primary| -> Result<i32, Error> {
                match primary.as_rule() {
                    Rule::int => Ok(parse_int(primary.into_inner().next().unwrap())),
                    Rule::calc_expr => Ok(self.parse_calc(primary.into_inner())?),
                    rule => unreachable!("parse_calc expected atom, found {:?}", rule),
                }
            })
        .map_infix(|lhs, op, rhs| {
            let res = match op.as_rule() {
                Rule::mul => lhs.unwrap() * rhs.unwrap(),
                Rule::div => {
                    let d = rhs.unwrap();
                    if d == 0 {
                        let start = op.as_span().start();
                        return Err(self.syntax_error("Division by zero", start));
                    }
                    lhs.unwrap() / d
                },
                Rule::add => lhs.unwrap() + rhs.unwrap(),
                Rule::sub => lhs.unwrap() - rhs.unwrap(),
                Rule::and => lhs.unwrap() & rhs.unwrap(),
                Rule::or => lhs.unwrap() | rhs.unwrap(),
                Rule::xor => lhs.unwrap() ^ rhs.unwrap(),
                Rule::brs => lhs.unwrap() >> rhs.unwrap(),
                Rule::bls => lhs.unwrap() << rhs.unwrap(),
                Rule::land => if lhs.unwrap() != 0 && rhs.unwrap() != 0 { 1 } else { 0 },
                Rule::lor => if lhs.unwrap() != 0 || rhs.unwrap() != 0 { 1 } else { 0 },
                Rule::gt => if lhs.unwrap() > rhs.unwrap() { 1 } else { 0 },
                Rule::gte => if lhs.unwrap() >= rhs.unwrap() { 1 } else { 0 },
                Rule::lt => if lhs.unwrap() < rhs.unwrap() { 1 } else { 0 },
                Rule::lte => if lhs.unwrap() <= rhs.unwrap() { 1 } else { 0 },
                Rule::eq => if lhs.unwrap() == rhs.unwrap() { 1 } else { 0 },
                Rule::neq => if lhs.unwrap() != rhs.unwrap() { 1 } else { 0 },
                Rule::ternary_cond1 => {
                    let l = lhs.unwrap();
                    let r = rhs.unwrap();
                    debug!("t1: left: {} right: {}", l, r);
                    if l != 0 { r } else { 0x7eaddead }
                },
                Rule::ternary_cond2 => { 
                    let l = lhs.unwrap();
                    let r = rhs.unwrap();
                    debug!("t2: left: {} right: {}", l, r); 
                    if l == 0x7eaddead { r } else { l } 
                },
                rule => unreachable!("parse_calc expected infix operation, found {:?}", rule),
            };
            Ok(res)
        })
        .map_prefix(|op, rhs| match op.as_rule() {
            Rule::neg => Ok(-rhs?),
            Rule::not => Ok(!rhs?),
            Rule::bnot => Ok(!rhs?),
            _ => unreachable!(),
        })
        .parse(pairs)
    }

#[allow(unused_assignments)]
    fn compile_var_decl(&mut self, pairs: Pairs<Rule>, global: bool) -> Result<(), Error>
    {
        let mut var_type_ex = VariableType::Char;
        let mut set_const = !global;
        let mut var_const = !global;
        let mut signedness_specified = false;
        let mut signed = self.signed_chars;
        let mut memory = VariableMemory::Zeropage;
        let mut alignment = 1;
        let mut reversed = false;
        let mut scattered = None;
        let mut holeydma = false;
        let mut screencode = false;
        for pair in pairs {
            match pair.as_rule() {
                Rule::var_type => {
                    for p in pair.into_inner() {
                        //debug!("{:?}", p);
                        let start = p.as_span().start();
                        match p.as_rule() {
                            Rule::var_const => {
                                var_const = true;
                                set_const = true;
                            },
                            Rule::bank => memory = VariableMemory::ROM(p.into_inner().next().unwrap().as_str().parse::<u32>().unwrap()),
                            Rule::superchip => memory = VariableMemory::Superchip,
                            Rule::display => memory = VariableMemory::Display,
                            Rule::frequency => memory = VariableMemory::Frequency,
                            Rule::ramchip => memory = VariableMemory::Ramchip, 
                            Rule::var_sign => {
                                signed = p.as_str().eq("signed");
                                signedness_specified = true;
                            },
                            Rule::var_simple_type => if p.as_str().starts_with("short") || p.as_str().starts_with("int") {
                                var_type_ex = VariableType::Short;
                                if !signedness_specified { signed = true; }
                            },
                            Rule::aligned => {
                                let px = p.into_inner().next().unwrap();
                                let a = self.parse_calc(px.into_inner())?;
                                if a > 0 { alignment = a as usize } else {
                                    return Err(self.syntax_error("Alignement must be positive", start));
                                }
                            },
                            Rule::reversed => reversed = true,
                            Rule::scattered => {
                                let mut px = p.into_inner();
                                let a = self.parse_calc(px.next().unwrap().into_inner())?;
                                let b = self.parse_calc(px.next().unwrap().into_inner())?;
                                if a > 0 && b > 0 {
                                    scattered = Some((a as u32, b as u32));
                                } else {
                                    return Err(self.syntax_error("Memory scattering parameters must be positive", start));
                                }
#[cfg(not(feature = "atari7800"))]
                                return Err(self.syntax_error("Memory scattering is only available on Atari 7800 ", start));
                            } 
                            Rule::holeydma => {
                                holeydma = true;
#[cfg(not(feature = "atari7800"))]
                                return Err(self.syntax_error("Holey DMA is only available on Atari 7800 ", start));
                            },
                            Rule::screencode => {
                                screencode = true;
                            },
                            _ => unreachable!()
                        }
                    }
                },
                Rule::global_id => {
                    let mut shortname = "";
                    let mut name = String::new();
                    let mut size = None;
                    let mut def = VariableDefinition::None;
                    let mut var_type = var_type_ex;
                    let mut start = 0;
                    for p in pair.into_inner() {
                        match p.as_rule() {
                            Rule::pointer => var_type = match var_type {
                                VariableType::Char => VariableType::CharPtr,
                                _ => return Err(self.syntax_error("Type too complex not supported", start))
                            },
                            Rule::var_const => {
                                var_const = true;
                                set_const = true;
                            },
                            Rule::id_name => {
                                shortname = p.as_str();
                                if global {
                                    name = shortname.into();
                                } else {
                                    name = format!("{}_{}_{shortname}", self.current_function, self.in_scope_variables.len()); 
                                }
                                start = p.as_span().start();
                                if self.variables.get(&name).is_some() {
                                    return Err(self.syntax_error(&format!("Variable {} already defined", &name), start));
                                }
                            },
                            Rule::array_spec => {
                                start = p.as_span().start();
                                if let Some(px) = p.into_inner().next() {
                                    size = Some(self.parse_calc(px.into_inner())? as usize);
                                }
                                if var_type == VariableType::Char {
                                    var_type = VariableType::CharPtr;
                                    var_const = true;
                                } else if var_type == VariableType::CharPtr {
                                    var_type = VariableType::CharPtrPtr;
                                    var_const = true;
                                } else if var_type == VariableType::Short {
                                    var_type = VariableType::ShortPtr;
                                    var_const = true;
                                } else {
                                    return Err(self.syntax_error("Kind of array not available", start));
                                }
                            },
                            Rule::var_def => {
                                let px = p.into_inner().next().unwrap();
                                start = px.as_span().start();
                                match px.as_rule() {
                                    Rule::calc_expr => {
                                        if !set_const {
                                            return Err(self.syntax_error("Non constant global variable can't be statically initialized", start))
                                        }
                                        let vx = self.parse_calc(px.into_inner())?;
                                        def = VariableDefinition::Value(VariableValue::Int(vx));
                                        if var_type == VariableType::CharPtr && vx > 0xff {
                                            memory = VariableMemory::Ramchip;
                                        }
                                    },
                                    Rule::var_ptr => {
                                        if !set_const {
                                            return Err(self.syntax_error("Non constant global variable can't be statically initialized", start))
                                        }
                                        let mut pxx = px.into_inner();
                                        let id_name = pxx.next().unwrap().as_str().to_string();
                                        def = VariableDefinition::Value(match pxx.next() {
                                            Some(x) => match x.as_rule() {
                                                Rule::ptr_low => {
                                                    let val = self.parse_calc(x.into_inner().next().unwrap().into_inner())?;
                                                    if val == 255 {
                                                        VariableValue::LowPtr((id_name, 0))
                                                    } else {
                                                        return Err(self.syntax_error(&format!("Incorrect suffix to reference {}", id_name), start))
                                                    }
                                                },
                                                Rule::ptr_hi => {
                                                    let val = self.parse_calc(x.into_inner().next().unwrap().into_inner())?;
                                                    if val == 8 {
                                                        VariableValue::HiPtr((id_name, 0))
                                                    } else {
                                                        return Err(self.syntax_error(&format!("Incorrect suffix to reference {}", id_name), start))
                                                    }
                                                },
                                                _ => return Err(self.syntax_error(&format!("Incorrect suffix to reference {}", id_name), start))
                                            },
                                            None => VariableValue::LowPtr((id_name, 0)),
                                        });
                                    },
                                    Rule::array_def => {
                                        if !set_const {
                                            return Err(self.syntax_error("Non constant global variable can't be statically initialized", start))
                                        }
                                        memory = match memory {
                                            VariableMemory::ROM(_) | VariableMemory::Display | VariableMemory::Frequency => memory,
                                            _ => VariableMemory::ROM(0)
                                        };
                                        if var_type != VariableType::CharPtr && var_type != VariableType::CharPtrPtr && var_type != VariableType::ShortPtr {
                                            return Err(self.syntax_error("Array definition provided for something not an array", start));
                                        }
                                        if var_type == VariableType::CharPtr || var_type == VariableType::ShortPtr {
                                            let mut v = Vec::new();
                                            for pxx in px.into_inner() {
                                                match pxx.as_rule() {
                                                    Rule::calc_expr => v.push(VariableValue::Int(self.parse_calc(pxx.into_inner())?)),
                                                    Rule::var_ptr => {
                                                        let mut pxxx = pxx.into_inner();
                                                        let id_name = pxxx.next().unwrap().as_str().to_string();
                                                        match pxxx.next() {
                                                            Some(x) => match x.as_rule() {
                                                                Rule::ptr_low => {
                                                                    let val = self.parse_calc(x.into_inner().next().unwrap().into_inner())?;
                                                                    if val == 255 {
                                                                        v.push(VariableValue::LowPtr((id_name, 0)))
                                                                    } else {
                                                                        return Err(self.syntax_error(&format!("Incorrect suffix to reference {}", id_name), start))
                                                                    }
                                                                },
                                                                Rule::ptr_hi => {
                                                                    let val = self.parse_calc(x.into_inner().next().unwrap().into_inner())?;
                                                                    if val == 8 {
                                                                        v.push(VariableValue::HiPtr((id_name, 0)))
                                                                    } else {
                                                                        return Err(self.syntax_error(&format!("Incorrect suffix to reference {}", id_name), start))
                                                                    }
                                                                },
                                                                _ => return Err(self.syntax_error(&format!("Incorrect suffix to reference {}", id_name), start))
                                                            },
                                                            None => v.push(VariableValue::LowPtr((id_name, 0))),
                                                        };
                                                    },
                                                    _ => return Err(self.syntax_error(&format!("Expecting constant literal, found {}", pxx.as_str() ), start))
                                                };
                                            }
                                            if let Some(s) = size {
                                                if s != v.len() {
                                                    return Err(self.syntax_error("Specified array size is different from actual definition", start));
                                                }
                                            }
                                            size = Some(v.len());
                                            def = VariableDefinition::Array(v);
                                        } else {
                                            let mut v = Vec::new();
                                            for pxx in px.into_inner() {
                                                match pxx.as_rule() {
                                                    Rule::var_ptr => {
                                                        let mut pxxx = pxx.into_inner();
                                                        let s = pxxx.next().unwrap().as_str().to_string();
                                                        let offset = match pxxx.next() {
                                                            Some(x) => match x.as_rule() {
                                                                Rule::ptr_offset => {
                                                                    self.parse_calc(x.into_inner().next().unwrap().into_inner())? as usize
                                                                },
                                                                _ => return Err(self.syntax_error(&format!("Incorrect suffix to reference {}", s), start))
                                                            },
                                                            None => 0,
                                                        };
                                                        let var = self.variables.get(&s);
                                                        if let Some(vx) = var {
                                                            if vx.var_type != VariableType::CharPtr && vx.var_type != VariableType::CharPtrPtr {
                                                                return Err(self.syntax_error(&format!("Reference {} should be a pointer", s), start));
                                                            }
                                                        } else {
                                                            return Err(self.syntax_error(&format!("Unknown identifier {}", s), start));
                                                        }
                                                        v.push((s, offset));
                                                    },
                                                    Rule::quoted_string => {
                                                        let k = self.compile_quoted_string(pxx);
                                                        let name = format!("cctmp{}", self.literal_counter);
                                                        self.literal_counter += 1;
                                                        let vb = k.as_bytes();
                                                        let mut arr = Vec::<VariableValue>::new();
                                                        for c in vb.iter() {
                                                            arr.push(VariableValue::Int(*c as i32));
                                                        }
                                                        let size = v.len();
                                                        self.variables.insert(name.clone(), Variable {
                                                            order: self.variables.len(),
                                                            signed: false,
                                                            memory,
                                                            var_const: true,
                                                            alignment: 1,
                                                            def: VariableDefinition::Array(arr),
                                                            var_type: VariableType::CharPtr, size,
                                                            reversed: false, scattered: None, holeydma: false, global: true});
                                                        v.push((name, 0));
                                                    },
                                                    _ => return Err(self.syntax_error("Unexpected array value", start)),
                                                }
                                            }
                                            if let Some(s) = size {
                                                if s != v.len() {
                                                    return Err(self.syntax_error("Specified array size is different from actual definition", start));
                                                }
                                            }
                                            size = Some(v.len());
                                            def = VariableDefinition::ArrayOfPointers(v);
                                        }
                                    },
                                    Rule::quoted_string => {
                                        if !set_const {
                                            return Err(self.syntax_error("Non constant global variable can't be statically initialized", start))
                                        }
                                        memory = match memory {
                                            VariableMemory::ROM(_) | VariableMemory::Display | VariableMemory::Frequency => memory,
                                            _ => VariableMemory::ROM(0)
                                        };
                                        if var_type != VariableType::CharPtr {
                                            return Err(self.syntax_error("String provided for something not a char*", start));
                                        }
                                        let string = self.compile_quoted_string(px);
                                        let vb = string.as_bytes();
                                        let mut v = Vec::<VariableValue>::new();
                                        for c in vb.iter() {
                                            let d = if screencode {
                                                if *c < 32 { *c + 128 }
                                                else if *c < 64 { *c }
                                                else if *c < 96 { *c - 64 }
                                                else if *c < 128 { *c - 32 }
                                                else if *c < 160 { *c + 64 }
                                                else if *c < 255 { *c - 128 }
                                                else { 94 }
                                            } else { *c };
                                            v.push(VariableValue::Int(d as i32));
                                        }
                                        size = Some(v.len());
                                        def = VariableDefinition::Array(v);
                                    },
                                    _ => unreachable!()
                                } 
                            },
                            _ => unreachable!()
                        }
                    }

                    // If there is no definition, then it's not ROM, it's a variable in RAM on the cart
                    if def == VariableDefinition::None {
                        if let VariableMemory::ROM(bank) = memory {
                            memory = VariableMemory::MemoryOnChip(bank);
                        }
                    }

#[cfg(feature = "atari7800")]
                    if holeydma {
                        if let Some((a, _)) = scattered {
                            if a != 8 && a != 16 {
                                return Err(self.syntax_error("Holey DMA is only available for 8 or 16 lines scattering", start));
                            }
                        }
                    }

                    if name != "X" && name != "Y" {
                        if !global {
                            // Insert it also in the local scope
                            let vars = self.in_scope_variables.last_mut().unwrap();
                            vars.insert(shortname.into(), name.clone());
                        }
                        self.variables.insert(name.to_string(), Variable {
                            order: self.variables.len(),
                            signed,
                            memory,
                            var_const,
                            alignment,
                            def,
                            var_type, size: size.unwrap_or(1),
                            reversed, scattered, holeydma, global: true
                        });
                    }
                },
                _ => {
                    debug!("What's this ? {:?}", pair);
                    unreachable!()
                }
            }
        }
        Ok(())
    }

    fn compile_local_var_decl(&mut self, mut pairs: Pairs<'a, Rule>) -> Result<StatementLoc<'a>, Error>
    {
        let p = pairs.next().unwrap();
        let pos = p.as_span().start();
        match p.as_rule() {
            Rule::local_var_decl_const => {
                self.compile_var_decl(p.into_inner(), false)?;
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::LocalVarDecl
                })
            },
            Rule::local_var_decl_mut => {
                let mut statements = Vec::<StatementLoc>::new();
                let mut var_type_ex = VariableType::Char;
                let mut var_const = false;
                let mut signedness_specified = false;
                let mut signed = self.signed_chars;
                let memory = VariableMemory::Zeropage;
                let alignment = 1;
                let reversed = false;
                let scattered = None;
                let holeydma = false;
                for pair in p.into_inner() {
                    match pair.as_rule() {
                        Rule::local_var_type => {
                            for p in pair.into_inner() {
                                match p.as_rule() {
                                    Rule::var_sign => {
                                        signed = p.as_str().eq("signed");
                                        signedness_specified = true;
                                    },
                                    Rule::var_simple_type => if p.as_str().starts_with("short") || p.as_str().starts_with("int") {
                                        var_type_ex = VariableType::Short;
                                        if !signedness_specified { signed = true; }
                                    },
                                    _ => unreachable!()
                                }
                            }
                        },
                        Rule::local_id => {
                            let mut shortname = "";
                            let mut name = String::new(); 
                            let mut size = None;
                            let mut var_type = var_type_ex;
                            let mut start = 0;
                            for p in pair.into_inner() {
                                match p.as_rule() {
                                    Rule::pointer => var_type = match var_type {
                                        VariableType::Char => VariableType::CharPtr,
                                        _ => return Err(self.syntax_error("Type too complex not supported", start))
                                    },
                                    Rule::id_name => {
                                        shortname = p.as_str();
                                        name = format!("{}_{}_{shortname}", self.current_function, self.in_scope_variables.len()); 
                                        if self.variables.get(&name).is_some() {
                                            name = format!("{}_{}_{shortname}_{}", self.current_function, self.in_scope_variables.len(), self.variable_counter); 
                                            self.variable_counter += 1;
                                        }
                                    },
                                    Rule::array_spec => {
                                        start = p.as_span().start();
                                        if let Some(px) = p.into_inner().next() {
                                            size = Some(self.parse_calc(px.into_inner())? as usize);
                                        }
                                        if var_type == VariableType::Char {
                                            var_type = VariableType::CharPtr;
                                            var_const = true;
                                        } else if var_type == VariableType::CharPtr {
                                            var_type = VariableType::CharPtrPtr;
                                            var_const = true;
                                        } else if var_type == VariableType::Short {
                                            var_type = VariableType::ShortPtr;
                                            var_const = true;
                                        } else {
                                            return Err(self.syntax_error("Kind of array not available", start));
                                        }
                                    },
                                    Rule::expr_init_value => {
                                        if var_const {
                                            return Err(self.syntax_error("Can't dynamically initialize array this way", start));
                                        }
                                        let expr = self.parse_expr_init_value(p.into_inner())?;
                                        let assign = Expr::BinOp {
                                            lhs: Box::new(Expr::Identifier(name.clone(), Box::new(Expr::Nothing))),
                                            op: Operation::Assign,
                                            rhs: Box::new(expr),
                                        };
                                        statements.push(StatementLoc {
                                            pos, label: None, statement: Statement::Expression(assign)
                                        });
                                    },
                                    _ => unreachable!()
                                }
                            }

                            if name != "X" && name != "Y" {
                                // Insert it into the functions table
                                let f = self.functions.get_mut(&self.current_function).unwrap();
                                f.local_variables.push(name.clone());
                                // Insert it also in the local scope
                                let vars = self.in_scope_variables.last_mut().unwrap();
                                vars.insert(shortname.into(), name.clone());
                                // Insert it into the global table
                                self.variables.insert(name, Variable {
                                    order: self.variables.len(),
                                    signed,
                                    memory,
                                    var_const,
                                    alignment,
                                    def: VariableDefinition::None,
                                    var_type, size: size.unwrap_or(1),
                                    reversed, scattered, holeydma, global: false
                                });
                            }
                        },
                        _ => {
                            debug!("What's this ? {:?}", pair);
                            unreachable!()
                        }
                    }
                }
                Ok(StatementLoc {
                    pos, label: None, statement: Statement::Block(statements) 
                })
            },
            _ => {
                debug!("What's this ? {:?}", p);
                unreachable!()
            }
        }
    }

    fn compile_block(&mut self, p: Pair<'a, Rule>) -> Result<StatementLoc<'a>, Error>
    {
        let pos = p.as_span().start();
        let mut statements = Vec::<StatementLoc>::new();
        for pair in p.into_inner() {
            match pair.as_rule() {
                Rule::statement => {
                    statements.push(self.compile_statement(pair)?)
                },
                _ => {
                    debug!("What's this ? {:?}", pair);
                    unreachable!()
                }
            }
        }
        Ok(StatementLoc {
            pos, label: None, statement: Statement::Block(statements) 
        })
    }

    fn compile_func_decl(&mut self, pairs: Pairs<'a, Rule>) -> Result<(), Error>
    {
        let mut inline = false;
        let mut bank = 0u32;
        let mut return_signed = self.signed_chars;
        let mut return_type = None;
        let mut interrupt = false;
        let mut name = String::new();
        let mut parameters = Vec::<String>::new();
        for pair in pairs {
            let start = pair.as_span().start();
            match pair.as_rule() {
                Rule::inline => {
                    inline = true; 
                },
                Rule::bank => {
                    bank = pair.into_inner().next().unwrap().as_str().parse::<u32>().unwrap();
                    if bank != 0 && inline {
                        return Err(self.syntax_error("Bank spec and inlining are incompatible", start));
                    }
                },
                Rule::interrupt => {
                    if bank != 0 {
                        return Err(self.syntax_error("Bank spec and interrupt are incompatible", start));
                    }
                    interrupt = true;
                },
                Rule::id_name => {
                    name = pair.as_str().to_string();
                },
                Rule::var_sign => {
                    return_signed = pair.as_str().eq("return_signed");
                },
                Rule::var_simple_type => if pair.as_str().starts_with("char") {
                    return_type = Some(VariableType::Char);
                } else {
                    return Err(self.syntax_error("Only char type is allowed as return type of function", start));
                },
                Rule::block => {
                    if let Some(f) = self.functions.get(&name) {
                        if f.code.is_some() {
                            return Err(self.syntax_error(&format!("Function {} already defined", name), start));
                        }
                    }
                    self.current_function = name.clone();
                    let mut map = HashMap::<String, String>::new();
                    for i in &self.variables {
                        map.insert(i.0.into(), i.0.into());
                    }
                    let mut local_variables = Vec::new();
                    for i in &parameters {
                        let s = format!("{}_{i}", self.current_function);
                        map.insert(i.clone(), s.clone());
                        local_variables.push(s);
                    }
                    self.in_scope_variables.push(map);
                    self.functions.insert(name.clone(), Function {
                        order: self.functions.len(),
                        inline,
                        bank,
                        code: None,
                        interrupt,
                        return_signed,
                        return_type,
                        local_variables,
                        parameters,
                        stack_frame_size: 0,
                    });
                    let code = self.compile_block(pair)?;
                    let f = self.functions.get_mut(&self.current_function).unwrap();
                    f.code = Some(code);
                    self.in_scope_variables.clear();
                    // Compute stack frame size
                    f.stack_frame_size = 0;
                    for vx in &f.local_variables {
                        if let Some(v) = self.variables.get(vx) {
                            f.stack_frame_size += if v.size > 1 {
                                let s = match v.var_type {
                                    VariableType::CharPtr => 1,
                                    VariableType::CharPtrPtr => 2,
                                    VariableType::ShortPtr => 2,
                                    _ => unreachable!()
                                };
                                v.size * s
                            } else {
                                let s = match v.var_type {
                                    VariableType::Char => 1,
                                    VariableType::Short => 2,
                                    VariableType::CharPtr => 2,
                                    VariableType::CharPtrPtr => 2,
                                    VariableType::ShortPtr => 2,
                                };
                                s
                            }
                        }
                    }
                    return Ok(())
                },
                Rule::parameters => {
                    let px = pair.into_inner();
                    for p in px {
                        let param = p.into_inner();
                        let mut var_type = VariableType::Char;
                        let mut var_const = false;
                        let mut signedness_specified = false;
                        let mut signed = self.signed_chars;
                        let memory = VariableMemory::Zeropage;
                        let alignment = 1;
                        let reversed = false;
                        let scattered = None;
                        let holeydma = false;
                        let mut shortname = "";
                        let mut longname = String::new(); 
                        let mut size = None;
                        let mut start = 0;
                        for pair in param {
                            match pair.as_rule() {
                                Rule::local_var_type => {
                                    for p in pair.into_inner() {
                                        match p.as_rule() {
                                            Rule::var_sign => {
                                                signed = p.as_str().eq("signed");
                                                signedness_specified = true;
                                            },
                                            Rule::var_simple_type => if p.as_str().starts_with("short") || p.as_str().starts_with("int") {
                                                var_type = VariableType::Short;
                                                if !signedness_specified { signed = true; }
                                            },
                                            _ => unreachable!()
                                        }
                                    }
                                },
                                Rule::pointer => var_type = match var_type {
                                    VariableType::Char => VariableType::CharPtr,
                                    _ => return Err(self.syntax_error("Type too complex not supported", start))
                                },
                                Rule::id_name => {
                                    shortname = pair.as_str();
                                    longname = format!("{name}_{shortname}"); 
                                    start = pair.as_span().start();
                                    if self.variables.get(&longname).is_some() {
                                        return Err(self.syntax_error(&format!("Variable {} already defined", longname), start));
                                    }
                                },
                                Rule::array_spec => {
                                    start = pair.as_span().start();
                                    if let Some(px) = pair.into_inner().next() {
                                        size = Some(self.parse_calc(px.into_inner())? as usize);
                                    }
                                    if var_type == VariableType::Char {
                                        var_type = VariableType::CharPtr;
                                        var_const = true;
                                    } else if var_type == VariableType::CharPtr {
                                        var_type = VariableType::CharPtrPtr;
                                        var_const = true;
                                    } else if var_type == VariableType::Short {
                                        var_type = VariableType::ShortPtr;
                                        var_const = true;
                                    } else {
                                        return Err(self.syntax_error("Kind of array not available", start));
                                    }
                                },
                                _ => unreachable!()
                            }
                        }
                        // Insert it into the global table
                        let var = Variable {
                            order: self.variables.len(),
                            signed,
                            memory,
                            var_const,
                            alignment,
                            def: VariableDefinition::None,
                            var_type, size: size.unwrap_or(1),
                            reversed, scattered, holeydma, global: false
                        };
                        self.variables.insert(longname, var);
                        parameters.push(shortname.into());
                    }
                },
                _ => unreachable!()
            } 
        };
        // This is just a prototype definition
        if self.functions.get(&name).is_none() {
            self.functions.insert(name, Function {
                order: self.functions.len(),
                inline,
                bank,
                code: None,
                interrupt,
                return_signed,
                return_type,
                local_variables: Vec::new(),
                parameters,
                stack_frame_size: 0
            });
        }
        Ok(())
    }

    fn compile_decl(&mut self, pairs: Pairs<'a, Rule>) -> Result<(), Error> 
    {
        for pair in pairs {
            match pair.as_rule() {
                Rule::var_decl => {
                    self.compile_var_decl(pair.into_inner(), true)?;
                },
                Rule::func_decl => {
                    self.compile_func_decl(pair.into_inner())?;
                },
                Rule::included_assembler => {
                    //debug!("Assembler: {:?}", pair);
                    let str = pair.into_inner().next().unwrap().as_str();
                    let mut filename = None;
                    let mut codesize = None;
                    let mut bank = None;
                    let mut split = str.split('\n');
                    for _ in 0..4 {
                        let line = split.next().unwrap().trim();
                        if line.starts_with("; file: ") {
                            filename = Some(line.split_at(8).1.into()); 
                        }
                        if line.starts_with("; codesize: ") {
                            codesize = line.split_at(12).1.parse::<usize>().ok(); 
                        }
                        if line.starts_with("; bank: ") {
                            bank = line.split_at(8).1.parse::<u8>().ok(); 
                        }
                    }
                    self.included_assembler.push((str.into(), filename, codesize, bank));
                },
                _ => {
                    debug!("What's this ? {:?}", pair);
                    unreachable!()
                }
            }
        }
        Ok(())
    }

    fn compile_quoted_string(&self, p: Pair<Rule>) -> String
    {
        let mut v = String::new();
        let it = p.into_inner();
        for i in it {
            let j = i.as_str().parse::<usize>().unwrap();
            v.push_str(&compile_quoted_string_ex(&self.context.literal_strings[j]));
        }
        v.push(char::from_u32(0).unwrap());
        v
    }


}

fn parse_int(p: Pair<Rule>) -> i32
{
    match p.as_rule() {
        Rule::decimal => p.as_str().parse::<i32>().unwrap(),
        Rule::hexadecimal => i32::from_str_radix(&p.as_str()[2..], 16).unwrap(),
        Rule::octal => i32::from_str_radix(p.as_str(), 8).unwrap(),
        Rule::quoted_character => {
            let s = compile_quoted_string_ex(p.into_inner().next().unwrap().as_str());
            s.chars().next().unwrap() as i32
        }
        _ => {
            unreachable!()
        }
    }
}

fn compile_quoted_string_ex(s: &str) -> String 
{
    let mut i = s.chars();
    let mut v = String::new();
    while let Some(c) = i.next() {
        if c == '\\' {
            match i.next() {
                Some('0') => v.push(char::from_u32(0).unwrap()),
                Some('n') => v.push(char::from_u32(10).unwrap()),
                Some('r') => v.push(char::from_u32(13).unwrap()),
                Some('a') => v.push(char::from_u32(7).unwrap()), // Bell
                Some('b') => v.push(char::from_u32(8).unwrap()), // Backspace
                Some('t') => v.push(char::from_u32(9).unwrap()), // Tab
                Some('f') => v.push(char::from_u32(14).unwrap()), // Form feed
                Some('v') => v.push(char::from_u32(11).unwrap()), // Vertical tab
                Some(a) => v.push(a),
                _ => (),
            }
        } else {
            v.push(c);
        }
    }
    v
}
    
pub fn compile<I: BufRead, O: Write>(input: I, output: &mut O, args: &Args, builder: fn(&CompilerState, &mut dyn Write, &Args) -> Result<(), Error>) -> Result<(), Error> {
    let mut preprocessed = Vec::new();
    
    let pratt =
        PrattParser::new()
        .op(Op::infix(Rule::comma, Assoc::Right))
        .op(Op::infix(Rule::assign, Assoc::Right) | Op::infix(Rule::mass, Assoc::Right) | Op::infix(Rule::pass, Assoc::Right) |
            Op::infix(Rule::andass, Assoc::Right) | Op::infix(Rule::orass, Assoc::Right) | Op::infix(Rule::xorass, Assoc::Right) |
            Op::infix(Rule::blsass, Assoc::Right) | Op::infix(Rule::brsass, Assoc::Right))
        .op(Op::infix(Rule::ternary_cond1, Assoc::Right))
        .op(Op::infix(Rule::ternary_cond2, Assoc::Right))
        .op(Op::infix(Rule::lor, Assoc::Left))
        .op(Op::infix(Rule::land, Assoc::Left))
        .op(Op::infix(Rule::or, Assoc::Left))
        .op(Op::infix(Rule::xor, Assoc::Left))
        .op(Op::infix(Rule::and, Assoc::Left))
        .op(Op::infix(Rule::eq, Assoc::Left) | Op::infix(Rule::neq, Assoc::Left) | Op::infix(Rule::gt, Assoc::Left) | Op::infix(Rule::gte, Assoc::Left) | Op::infix(Rule::lt, Assoc::Left) | Op::infix(Rule::lte, Assoc::Left))
        .op(Op::infix(Rule::brs, Assoc::Left) | Op::infix(Rule::bls, Assoc::Left))
        .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
        .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
        .op(Op::prefix(Rule::neg) | Op::prefix(Rule::not) | Op::prefix(Rule::bnot) | Op::prefix(Rule::mmp) | Op::prefix(Rule::ppp) | Op::prefix(Rule::deref) | Op::prefix(Rule::addr) | Op::prefix(Rule::sizeof))
        .op(Op::postfix(Rule::call) | Op::postfix(Rule::mm) | Op::postfix(Rule::pp));
   
    let pratt_init_value =
        PrattParser::new()
        .op(Op::infix(Rule::assign, Assoc::Right) | Op::infix(Rule::mass, Assoc::Right) | Op::infix(Rule::pass, Assoc::Right) |
            Op::infix(Rule::andass, Assoc::Right) | Op::infix(Rule::orass, Assoc::Right) | Op::infix(Rule::xorass, Assoc::Right) |
            Op::infix(Rule::blsass, Assoc::Right) | Op::infix(Rule::brsass, Assoc::Right))
        .op(Op::infix(Rule::ternary_cond1, Assoc::Right))
        .op(Op::infix(Rule::ternary_cond2, Assoc::Right))
        .op(Op::infix(Rule::lor, Assoc::Left))
        .op(Op::infix(Rule::land, Assoc::Left))
        .op(Op::infix(Rule::or, Assoc::Left))
        .op(Op::infix(Rule::xor, Assoc::Left))
        .op(Op::infix(Rule::and, Assoc::Left))
        .op(Op::infix(Rule::eq, Assoc::Left) | Op::infix(Rule::neq, Assoc::Left) | Op::infix(Rule::gt, Assoc::Left) | Op::infix(Rule::gte, Assoc::Left) | Op::infix(Rule::lt, Assoc::Left) | Op::infix(Rule::lte, Assoc::Left))
        .op(Op::infix(Rule::brs, Assoc::Left) | Op::infix(Rule::bls, Assoc::Left))
        .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
        .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
        .op(Op::prefix(Rule::neg) | Op::prefix(Rule::not) | Op::prefix(Rule::bnot) | Op::prefix(Rule::mmp) | Op::prefix(Rule::ppp) | Op::prefix(Rule::deref) | Op::prefix(Rule::addr) | Op::prefix(Rule::sizeof))
        .op(Op::postfix(Rule::call) | Op::postfix(Rule::mm) | Op::postfix(Rule::pp));
   
    let calculator = 
        PrattParser::new()
        .op(Op::infix(Rule::ternary_cond2, Assoc::Right))
        .op(Op::infix(Rule::ternary_cond1, Assoc::Right))
        .op(Op::infix(Rule::lor, Assoc::Left))
        .op(Op::infix(Rule::land, Assoc::Left))
        .op(Op::infix(Rule::or, Assoc::Left))
        .op(Op::infix(Rule::xor, Assoc::Left))
        .op(Op::infix(Rule::and, Assoc::Left))
        .op(Op::infix(Rule::eq, Assoc::Left) | Op::infix(Rule::neq, Assoc::Left) | Op::infix(Rule::gt, Assoc::Left) | Op::infix(Rule::gte, Assoc::Left) | Op::infix(Rule::lt, Assoc::Left) | Op::infix(Rule::lte, Assoc::Left))
        .op(Op::infix(Rule::brs, Assoc::Left) | Op::infix(Rule::bls, Assoc::Left))
        .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
        .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
        .op(Op::prefix(Rule::neg) | Op::prefix(Rule::not) | Op::prefix(Rule::bnot));

    // Prepare the context
    let mut context = cpp::Context::new(&args.input);
    context.include_directories = args.include_directories.clone();
#[cfg(feature = "atari2600")]
    context.define("__ATARI2600__", "1");
#[cfg(feature = "atari7800")]
    context.define("__ATARI7800__", "1");
    for i in &args.defines {
        let mut s = i.splitn(2, '=');
        let def = s.next().unwrap();
        let value = s.next().unwrap_or("1");
        context.define(def, value);
    }

    // Start preprocessor
    //debug!("Preprocessor");
    let mapped_lines = cpp::process(input, &mut preprocessed, &mut context, false)?;
    debug!("Mapped lines = {:?}", mapped_lines);

    let preprocessed_utf8 = std::str::from_utf8(&preprocessed)?;
    debug!("Preprocessed: {}", preprocessed_utf8);

    // Prepare the state
    let mut state = CompilerState {
        variables: HashMap::new(),
        functions: HashMap::new(),
        pratt, pratt_init_value, calculator,
        mapped_lines: &mapped_lines,
        preprocessed_utf8,
        included_assembler: Vec::<(String, Option<String>, Option<usize>, Option<u8>)>::new(),
        context,
        signed_chars: args.signed_chars,
        literal_counter: 0,
        in_scope_variables: Vec::new(),
        current_function: String::new(),
        variable_counter: 0
    };

    let r = Cc2600Parser::parse(Rule::program, preprocessed_utf8);
    match r {
        Err(e) => {
            let mut ex = e.clone();
            let filename;
            let line;
            ex.line_col = match e.line_col {
                LineColLocation::Pos((l, c)) => {
                    filename = mapped_lines[l - 1].0.clone();
                    line = mapped_lines[l - 1].1;
                    LineColLocation::Pos((mapped_lines[l - 1].1 as usize, c))
                },
                LineColLocation::Span((l1, c1), (l2, c2)) => {
                    filename = mapped_lines[l1 - 1].0.clone();
                    line = mapped_lines[l1 - 1].1;
                    LineColLocation::Span((mapped_lines[l1 - 1].1 as usize, c1), (mapped_lines[l2 - 1].1 as usize, c2))
                },
            };
            eprintln!("{}", ex);
            return Err(Error::Syntax {
                filename: filename.to_string(), included_in: None, line,
                msg: e.variant.message().to_string() })
        }
        Ok(mut p) => {
            let pairs = p.next().unwrap();
            for pair in pairs.into_inner() {
                match pair.as_rule() {
                    Rule::decl => {
                        state.compile_decl(pair.into_inner())?;
                    },
                    Rule::EOI => break,
                    _ => {
                        debug!("What's this ? {:?}", pair);
                        unreachable!()
                    }
                }
            }
        }
    };

    #[cfg(feature="atari2600")]
    state.variables.insert("DUMMY".to_string(), Variable {
        order: state.variables.len(),
        signed: false,
        memory: VariableMemory::Zeropage,
        var_const: true,
        alignment: 1,
        def: VariableDefinition::Value(VariableValue::Int(0x2d)),
        var_type: VariableType::Char, 
        size: 1,
        reversed: false, scattered: None, holeydma: false,
        global: true
    });

    // Generate assembly code from compilation output (abstract syntax tree)
    builder(&state, output, args)?;
    Ok(())
}

