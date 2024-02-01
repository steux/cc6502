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

// DONE: Implement NMI interrupt routine support
// DONE: cpp.rs: process string literal before comments or any macro substitution
// DONE: implement 16 bits comparison
// DONE: Add function return values (in cctmp)
// DONE: Mark functions as used or not for the linker
// DONE: Implement better optimized 16 bits increment
// DONE: Detect & 0xff and return lower 8 bits
// DONE: Detect 16 bits aithm bad carry propagation
// DONE: Implement function return in Acc
// DONE: Add nbbytes param to asm statement
// DONE: Add local variables stack storage code
// DONE: Add functions params support
// DONE: Accept *ptr
// DONE: Generate performance warnings
// DONE: Bug fix : Already defined local functions in blocks 
// DONE: Bug fix: (x << 4) << 8 != x << 12
// DONE: Fix 16 bits +=Y
// DONE: Initialized global data should be const
// DONE: Check (char) >> 8 => 0 (too complex?)
// DONE: Check X << 8 => too complex ?
// DONE: Check for (X = 0; X < 10;) { X++ }
// DONE: Optimize ptr |= 16 * 256
// DONE: Optimize ptr = Y | (X << 8)
// DONE: Bug ptr = Y | (X++ << 8)
// DONE: Swap CLC/SEC and LDA 
// DONE: Optimize out AND #255
// TODO: Indicate error line when compiler error not implemented
// DONE: 16 bits inc produces incorrect core for ramchip

mod cpp;
pub mod error;
pub mod compile;
pub mod generate;
pub mod assemble;

extern crate pest;
#[macro_use]
extern crate pest_derive;

use clap::Parser as ClapParser;

#[derive(ClapParser, Debug)]
#[command(author, about = "A subset of C compiler for the 6502 processor", long_about = "A subset of C compiler for the 6502 processor\nCopyright (C) 2023 Bruno STEUX\n\nThis program comes with ABSOLUTELY NO WARRANTY;\nThis is free software, and you are welcome to redistribute it\nunder certain conditions;")]
pub struct Args {
    /// Input file name
    #[arg(default_value="stdin")]
    pub input: String,

    /// Preprocessor definitions
    #[arg(short='D')]
    defines: Vec<String>,

    /// Optimization level
    #[arg(short='O', default_value="1", value_parser=clap::value_parser!(u8).range(0..=3))]
    pub optimization_level: u8,

    /// Verbosity 
    #[arg(short, long, default_value="false")]
    pub verbose: bool,

    /// Include directories
    #[arg(short='I')]
    include_directories: Vec<String>,

    /// Warning directives
    #[arg(short='W')]
    pub warnings: Vec<String>,

    /// Output file name
    #[arg(short, long, default_value="a.out")]
    pub output: String,

    /// Insert C code as comments
    #[arg(long, default_value="false")]
    pub insert_code: bool,

    /// Set char signedness to signed
    #[arg(long("fsigned_char"), default_value = "false")]
    signed_chars: bool,
    
    /// Set char signedness to unsigned (default)
    #[arg(long("funsigned_char"), default_value = "true")]
    unsigned_chars: bool,

    /// Stop after the stage of compilation proper; do not assemble 
    #[arg(short='S', default_value="false")]
    pub assembler_output: bool,

    /// Generate debug information 
    #[arg(short='g', long, default_value="false")]
    pub debug: bool,

    /// Print compiler version
    #[arg(long, default_value = "false")]
    pub version: bool
}

#[cfg(test)]
mod tests {
    use super::Args;
    use super::compile::compile;
    use std::str;
    mod build;
    use build::simple_build;

    fn sargs(optimization_level: u8) -> Args {
        Args {
            input: "string".to_string(),
            output: "string".to_string(),
            include_directories: Vec::new(),
            defines: Vec::new(),
            insert_code: false,
            verbose: false,
            optimization_level,
            signed_chars: false,
            unsigned_chars: true,
            version: false,
            assembler_output: true,
            debug: false,
            warnings: Vec::new()
        }
    }

    #[test]
    fn for_statement_test1() {
        let args = sargs(1); 
        let input = "unsigned char i; void main() { for (i = 0; i < 10; i++); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #0\n\tSTA i\n\tCMP #10\n\tBCS .forend1\n.for1\n.forupdate1\n\tINC i\n\tLDA i\n\tCMP #10\n\tBCC .for1\n.forend1\n"));
    }
    
    #[test]
    fn for_statement_test2() {
        let args = sargs(1); 
        let input = "unsigned char i; void main() { for (i = 0; i != 10; i++); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #0\n\tSTA i\n.for1\n.forupdate1\n\tINC i\n\tLDA i\n\tCMP #10\n\tBNE .for1\n.forend1\n"));
    }
    
    #[test]
    fn for_statement_test3() {
        let args = sargs(1); 
        let input = "void main() { for (X = 0; X != 10; ) X++; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #0\n.for1\n\tINX\n.forupdate1\n\tCPX #10\n\tBNE .for1\n.forend1"));
    }
    
    #[test]
    fn plusplus_statement_test1() {
        let args = sargs(1); 
        let input = "unsigned char i, j; void main() { i = 0; j = i++; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #0\n\tSTA i\n\tSTA j\n\tINC i\n"));
    }
    
    #[test]
    fn plusplus_statement_test2() {
        let args = sargs(1); 
        let input = "unsigned char i, j; void main() { i = 0; j = ++i; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #0\n\tSTA i\n\tINC i\n\tLDA i\n\tSTA j"));
    }
    
    #[test]
    fn plusplus_statement_test3() {
        let args = sargs(1); 
        let input = "short i, j; void main() { i = 0; j = ++i; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #0\n\tSTA i\n\tSTA i+1\n\tINC i\n\tBNE .ifend1\n\tINC i+1\n.ifend1\n\tLDA i\n\tSTA j\n\tLDA i+1\n\tSTA j+1"));
    }
    
    #[test]
    fn plusplus_statement_test4() {
        let args = sargs(1); 
        let input = "short i; char *j; void main() { i = j[++Y]; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("INY\n\tLDA (j),Y\n\tSTA i\n\tLDA #0\n\tSTA i+1"));
    }
    
    #[test]
    fn sixteen_bits_test1() {
        let args = sargs(1);
        let input = "short i, j, k; void main() { i = 1; j = 1; k = i + j; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CLC\n\tLDA i\n\tADC j\n\tSTA k\n\tLDA i+1\n\tADC j+1\n\tSTA k+1"));
    }
    
    #[test]
    fn sixteen_bits_test2() {
        let args = sargs(1);
        let input = "unsigned short i; unsigned char j; void main() { i = j; i = j << 8; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA j\n\tSTA i\n\tLDA #0\n\tSTA i+1\n\tSTA i\n\tLDA j\n\tSTA i+1"));
    }
    
    #[test]
    fn if_test1() {
        let args = sargs(1);
        let input = "void main() { if (0) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("JMP .ifend1\n\tLDX #1\n.ifend1"));
    }

    #[test]
    fn if_test2() {
        let args = sargs(1);
        let input = "void main() { if (!0) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("main\tSUBROUTINE\n\tLDX #1\n.ifend1"));
    }
    
    #[test]
    fn if_test3() {
        let args = sargs(1);
        let input = "unsigned char i, j; void main() { i = 0; j = 0; if (i == 0 && j == 0) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        assert!(result.contains("LDA #0\n\tSTA i\n\tSTA j\n\tLDA i\n\tBNE .ifend1\n\tLDA j\n\tBNE .ifend1\n\tLDX #1"));
        print!("{:?}", result);
    }
    
    #[test]
    fn if_test4() {
        let args = sargs(1);
        let input = "unsigned char i, j; void main() { i = 0; j = 0; if (i == 0 || j == 0) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #0\n\tSTA i\n\tSTA j\n\tLDA i\n\tBEQ .ifstart1\n\tLDA j\n\tBNE .ifend1\n.ifstart1\n\tLDX #1"));
    }
    
    #[test]
    fn if_test5() {
        let args = sargs(1);
        let input = "unsigned char i, j, k; void main() { i = 0; j = 0; k = 0; if (i == 0 || j == 0 || k == 0) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #0\n\tSTA i\n\tSTA j\n\tSTA k\n\tLDA i\n\tBEQ .ifstart1\n\tLDA j\n\tBEQ .ifstart1\n\tLDA k\n\tBNE .ifend1\n.ifstart1\n\tLDX #1"));
    }
    
    #[test]
    fn if_test6() {
        let args = sargs(1);
        let input = "unsigned char i, j, k; void main() { i = 0; i = 0; k = 0; if (i == 0 && j == 0 && k == 0) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #0\n\tSTA i\n\tSTA i\n\tSTA k\n\tLDA i\n\tBNE .ifend1\n\tLDA j\n\tBNE .ifend1\n\tLDA k\n\tBNE .ifend1\n\tLDX #1\n.ifend1"));
    }
    
    #[test]
    fn if_test7() {
        let args = sargs(1);
        let input = "char i, j, k; void main() { i = j + k; if (i < 0) i = 0; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CLC\n\tLDA j\n\tADC k\n\tSTA i\n\tBPL .ifend1\n\tLDA #0\n\tSTA i\n.ifend1"));
    }
    
    #[test]
    fn if_test8() {
        let args = sargs(1);
        let input = "char i, j, k; void main() { i = j + k; if (i >= 0) i = 0; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CLC\n\tLDA j\n\tADC k\n\tSTA i\n\tBMI .ifend1\n\tLDA #0\n\tSTA i\n.ifend1"));
    }
    
    #[test]
    fn if_test9() {
        let args = sargs(1);
        let input = "char i[1]; void main() { if (Y < i[X]) X = 0; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("TYA\n\tCMP i,X\n\tBCS .ifend1"));
    }
    
    #[test]
    fn if_test10() {
        let args = sargs(1);
        let input = "char i[1]; void main() { if (X < i[Y]) X = 0; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("TXA\n\tCMP i,Y\n\tBCS .ifend1"));
    }
    
    #[test]
    fn not_test() {
        let args = sargs(1);
        let input = "void main() { X = 0; Y = !X; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #0\n\tBNE .else1\n\tLDA #1\n\tJMP .ifend1\n.else1\n\tLDA #0\n.ifend1\n\tTAY"));
    }
    
    #[test]
    fn condition_test() {
        let args = sargs(1);
        let input = "void main() { X = 0; Y = X == 0; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #0\n\tBEQ .else1\n\tLDA #0\n\tJMP .ifend1\n.else1\n\tLDA #1\n.ifend1\n\tTAY"));
    }
    
    #[test]
    fn ternary_test() {
        let args = sargs(1);
        let input = "void main() { X = 0; Y = (X == 0)?0x10:0x20; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #0\n\tBNE .else1\n\tLDA #16\n\tJMP .ifend1\n.else1\n\tLDA #32\n.ifend1\n\tTAY"));
    }
    
    #[test]
    fn switch_test1() {
        let args = sargs(1);
        let input = "void main() { switch(X) { case 0: case 1: Y = 0; case 2: Y = 1; break; default: Y = 2; } }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CPX #0\n\tBEQ .switchnextstatement2\n\tCPX #1\n\tBEQ .switchnextstatement2\n\tJMP .switchnextcase3\n.switchnextstatement2\n\tLDY #0\n\tJMP .switchnextstatement4\n.switchnextcase3\n\tCPX #2\n\tBNE .switchnextcase5\n.switchnextstatement4\n\tLDY #1\n\tJMP .switchend1\n.switchnextcase5\n.switchnextstatement6\n\tLDY #2\n.switchend1"));
    }
    
    #[test]
    fn switch_test2() {
        let args = sargs(1);
        let input = "void main() { switch(X) { case 0: Y = 0; break; case 1: Y = 1; } }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CPX #0\n\tBNE .switchnextcase3\n.switchnextstatement2\n\tLDY #0\n\tJMP .switchend1\n.switchnextcase3\n\tCPX #1\n\tBNE .switchnextcase5\n.switchnextstatement4\n\tLDY #1\n.switchnextcase5\n.switchend1"));
    }
    
    #[test]
    fn goto_test() {
        let args = sargs(1);
        let input = "void main() { goto test; return; test: X = 0; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("JMP .test\n\tRTS\n.test\n\tLDX #0"));
    }
    
    #[test]
    fn assign_test() {
        let args = sargs(1);
        let input = "char a, b, c, d, e, f, g; void main() { g = (a+b)+(c+(d&(e=f))); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CLC\n\tLDA a\n\tADC b\n\tPHA\n\tLDA f\n\tSTA e\n\tLDA d\n\tAND e\n\tSTA cctmp\n\tCLC\n\tLDA c\n\tADC cctmp\n\tSTA cctmp\n\tPLA\n\tCLC\n\tADC cctmp\n\tSTA g"));
    }

    #[test]
    fn inline_test() {
        let args = sargs(1);
        let input = "inline void add() { X += Y; }; void main() { add(); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("main\tSUBROUTINE\n\tTXA\n\tCLC\n\tSTY cctmp\n\tADC cctmp\n\tTAX"));
    }

    #[test]
    fn inline_test2() {
        let args = sargs(1);
        let input = "inline void w() { while(Y) Y--; }; void main() { w(); w(); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains(".while1inline1\n\tCPY #0\n\tBEQ .whileend1inline1\n\tDEY\n\tJMP .while1inline1\n.whileend1inline1\n.endofinline1\n.while1inline2\n\tCPY #0\n\tBEQ .whileend1inline2\n\tDEY\n\tJMP .while1inline2\n.whileend1inline2\n.endofinline2"));
    }

    #[test]
    fn inline_test3() {
        let args = sargs(1);
        let input = "inline char w() { if (Y) return 1; return 0; }; void main() { X = w(); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CPY #0\n\tBEQ .ifend1inline1\n\tLDA #1\n\tJMP .endofinline1\n.ifend1inline1\n\tLDA #0\n.endofinline1\n\tTAX\n"));
    }

    #[test]
    fn array_of_pointers_test() {
        let args = sargs(1);
        let input = "
const char s1[] = {0};
const char s2[] = {0};
const char *ss[] = {s1, s2};

char *ptr;
char v;

void main()
{
    ptr = ss[X];
    v = ptr[Y];
}
            ";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA ss,X\n\tSTA ptr\n\tLDA ss+2,X\n\tSTA ptr+1\n\tLDA (ptr),Y\n\tSTA v"));
    }
    
    #[test]
    fn array_of_pointers_test2() {
        let args = sargs(1);
        let input = "
const char s1[] = {0};
const char s2[] = {0};
const char *ss[] = {s1, s2};

char *ptr;
char v;

void main()
{
    ptr = ss[0];
    v = ptr[Y];
}
            ";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA ss\n\tSTA ptr\n\tLDA ss+2\n\tSTA ptr+1\n\tLDA (ptr),Y\n\tSTA v"));
    }
    
    #[test]
    fn array_of_pointers_test3() {
        let args = sargs(1);
        let input = "
char *s1, *s2;
char *ss[2];

char *ptr;
char v;

void main()
{
    ss[0] = s1;
    ss[1] = s2;
    ptr = ss[1];
    v = ptr[Y];
}
            ";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA s1\n\tSTA ss\n\tLDA s1+1\n\tSTA ss+2\n\tLDA s2\n\tSTA ss+1\n\tLDA s2+1\n\tSTA ss+3\n\tLDA ss+1\n\tSTA ptr\n\tLDA ss+3\n\tSTA ptr+1\n\tLDA (ptr),Y\n\tSTA v"));
    }
    
    #[test]
    fn array_of_pointers_test4() {
        let args = sargs(1);
        let input = "
const char s1[] = {0};
const char s2[] = {0};
const char *ss[] = {s1, s2};

char *ptr;
char v;

void main()
{
    ptr = ss[v];
    v = ptr[v];
}
            ";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("STY cctmp\n\tLDY v\n\tLDA ss,Y\n\tSTA ptr\n\tLDY v\n\tLDA ss+2,Y\n\tSTA ptr+1\n\tLDY v\n\tLDA (ptr),Y\n\tSTA v\n\tLDY cctmp"));
    }
    
    #[test]
    fn longbranch_test() {
        let args = sargs(1);
        let mut input: String = "void main() { do {".to_string();
        for _ in 0..130 {
            input.push_str("csleep(2);");
        }
        input.push_str("} while (Y);}");
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CPY #0\n\tBEQ .fix1\n\tJMP .dowhile1\n.fix1\n.dowhileend1"));
    }

    #[test]
    fn load_test() {
        let args = sargs(1);
        let input = "char i; void main() { i = 0; load(0); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #0\n\tSTA i\n\tLDA #0"));
    }
    
    #[test]
    fn calc_test() {
        let args = sargs(1);
        let input = "const char tab[1 + 1] = {3 * 5, 4 << 2};";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("hex 0f10"));
    }
    
    #[test]
    fn array_indexing_test() {
        let args = sargs(1);
        let input = "char c[2]; char i; void main() { c[X = i] = 0; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX i\n\tLDA #0\n\tSTA c,X"));
    }
    
    #[test]
    fn sixteen_bits_minusminus_test() {
        let args = sargs(1);
        let input = "short i; void main() { i--; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA i\n\tBNE .ifend1\n\tDEC i+1\n.ifend1\n\tDEC i"));
    }
    
    #[test]
    fn sixteen_bits_increment_test() {
        let args = sargs(1);
        let input = "short i; void main() { i += -1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CLC\n\tLDA i\n\tADC #255\n\tSTA i\n\tLDA i+1\n\tADC #255\n\tSTA i+1"));
    }
    
    #[test]
    fn sign_extend_test() {
        let args = sargs(1);
        let input = "short i; signed char x; void main() { i += x; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CLC\n\tLDA i\n\tADC x\n\tSTA i\n\tLDA x\n\tORA #127\n\tBMI .ifneg1\n\tLDA #0\n.ifneg1\n\tADC i+1\n\tSTA i+1"));
    }
    
    #[test]
    fn sign_extend_test2() {
        let args = sargs(1);
        let input = "short i; void main() { i += -1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CLC\n\tLDA i\n\tADC #255\n\tSTA i\n\tLDA i+1\n\tADC #255\n\tSTA i+1"));
    }
    
    #[test]
    fn splices_test() {
        let args = sargs(1);
        let input = "#define one \\
1
char i; void main() { i = one; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #1\n\tSTA i"));
    }
    
    #[test]
    fn quoted_string_test1() {
        let args = sargs(1);
        let input = "char *s; void main() { s = \"zobi\\\"\\\\\"; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("cctmp0\n\thex 7a6f6269225c0"));
    }
    
    #[test]
    fn quoted_string_test2() {
        let args = sargs(1);
        let input = "const char *s = \"\tzobi\\\"\\\\\";";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("s\n\thex 097a6f6269225c00"));
    }
    
    #[test]
    fn quoted_string_test3() {
        let args = sargs(1);
        let input = "const char *s[2] = {\"zobi\", \"zoba\"};";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("cctmp0\n\thex 7a6f626900\ncctmp1\n\thex 7a6f626100\ns\n\t.byte <cctmp0, <cctmp1, >cctmp0, >cctmp1"));
    }
    
    #[test]
    fn quoted_string_test4() {
        let args = sargs(1);
        let input = "const char *s = \"zobi/*comment*/\";";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("s\n\thex 7a6f62692f2a636f6d6d656e742a2f00"));
    }
    
    #[test]
    fn quoted_string_test5() {
        let args = sargs(1);
        let input = "#define zobi(x) x\nchar *s; void main() { s = zobi(\"hello, world!\"); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("hex 68656c6c6f2c20776f726c642100"));
    }
    
    #[test]
    fn quoted_string_test6() {
        let args = sargs(1);
        let input = "const char *s = \"hello, \"\n\t\"world!\";";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("hex 68656c6c6f2c20776f726c642100"));
    }
    
    #[test]
    fn right_shift_test1() {
        let args = sargs(1);
        let input = "signed char i; void main() { i >>= 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA i\n\tCMP #128\n\tROR\n\tSTA i"));
    }

    #[test]
    fn right_shift_test2() {
        let args = sargs(1);
        let input = "signed char i; void main() { i >>= 2; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA i\n\tLSR\n\tLSR\n\tCLC\n\tADC #224\n\tEOR #224\n\tSTA i"));
    }
    
    #[test]
    fn right_shift_test3() {
        let args = sargs(1);
        let input = "char i; char *ptr; void main() { i = ptr >> 8; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA ptr+1\n\tSTA i"));
    }
    
    #[test]
    fn right_shift_test4() {
        let args = sargs(1);
        let input = "char i; unsigned short j; void main() { i = (j >> 8) >> 4; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA j+1\n\tLSR\n\tLSR\n\tLSR\n\tLSR\n\tSTA i"));
    }
    
    #[test]
    fn right_shift_test5() {
        let args = sargs(1);
        let input = "char i; char j; void main() { i = (j >> 8); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #0\n\tSTA i"));
    }
    
    #[test]
    fn left_shift_test1() {
        let args = sargs(1);
        let input = "char *ptr; void main() { ptr = X << 8; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #0\n\tSTA ptr\n\tSTX ptr+1"));
    }
    
    #[test]
    fn left_shift_test2() {
        let args = sargs(1);
        let input = "void main() { char *ptr = X | (Y << 8); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("STX main_1_ptr\n\tSTY main_1_ptr+1"));
    }
    
    #[test]
    fn left_shift_test3() {
        let args = sargs(1);
        let input = "void main() { char *ptr = Y | (X << 8); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("STY main_1_ptr\n\tSTX main_1_ptr+1"));
    }
    
    #[test]
    fn left_shift_test4() {
        let args = sargs(1);
        let input = "void main() { char *ptr = Y | (X++ << 8); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("STY main_1_ptr\n\tSTX main_1_ptr+1\n\tINX"));
    }
    
    #[test]
    fn comma_test() {
        let args = sargs(1);
        let input = "void main() { for (Y = 0, X = 0; X != 10; Y++, X++); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDY #0\n\tLDX #0\n.for1\n.forupdate1\n\tINY\n\tINX\n\tCPX #10\n\tBNE .for1"));
    }

    #[test]
    fn for_test1() {
        let args = sargs(1);
        let input = "void main() { for (Y = 127; Y >= 0; Y--); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDY #127\n\tBMI .forend1\n.for1\n.forupdate1\n\tDEY\n\tBPL .for1\n.forend1"));
    }
    
    #[test]
    fn for_test2() {
        let args = sargs(1);
        let input = "void main() { for (Y = 255; Y > 0; Y--); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDY #255\n\tBEQ .forend1\n.for1\n.forupdate1\n\tDEY\n\tBEQ .ifhere1\n.ifhere1\n.forend1"));
    }
    
    #[test]
    fn while_test() {
        let args = sargs(1);
        let input = "void main() {  do { Y--; } while (Y >= 0); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains(".dowhile1\n\tDEY\n\tBPL .dowhile1"));
    }
    
    #[test]
    fn sixteen_bits_test3() {
        let args = sargs(1);
        let input = "short i; short int j; int k; void main() { i = 1; j = 1; k = i + j; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CLC\n\tLDA i\n\tADC j\n\tSTA k\n\tLDA i+1\n\tADC j+1\n\tSTA k+1"));
    }
    
    #[test]
    fn sixteen_bits_test4() {
        let args = sargs(1);
        let input = "short i; void main() { i += X; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CLC\n\tLDA i\n\tSTX cctmp\n\tADC cctmp\n\tSTA i\n\tLDA i+1\n\tADC #0\n\tSTA i+1"));
    }
    
    #[test]
    fn sixteen_bits_test5() {
        let args = sargs(1);
        let input = "short i; void main() { i += Y; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CLC\n\tLDA i\n\tSTY cctmp\n\tADC cctmp\n\tSTA i\n\tLDA i+1\n\tADC #0\n\tSTA i+1"));
    }
    
    #[test]
    fn ternary_immediate_test1() {
        let args = sargs(1);
        let input = "void main() { X = (1 > 0)?2:3; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #2"));
    }
    
    #[test]
    fn ternary_immediate_test2() {
        let args = sargs(1);
        let input = "void main() { X = (0)?2:3; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #3"));
    }
    
    #[test]
    fn cond_expr_immediate_test1() {
        let args = sargs(1);
        let input = "void main() { X = 0 == 1; Y = 1 > 0;}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #0\n\tLDY #1"));
    }
    
    #[test]
    fn cond_expr_immediate_test2() {
        let args = sargs(1);
        let input = "void main() { X = !(0 == 1); Y = !(1 > 0);}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #1\n\tLDY #0"));
    }
    
    #[test]
    fn cond_expr_immediate_test3() {
        let args = sargs(1);
        let input = "void main() { X = 0 && Y; Y = 1 && 0;}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #0\n\tLDY #0"));
    }
    
    #[test]
    fn cond_expr_immediate_test4() {
        let args = sargs(1);
        let input = "void main() { X = Y && 1; Y = X && 0;}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        // Far from optimal, but the result if correct
        assert!(result.contains("CPY #0\n\tBEQ .ifstart1\n\tJMP .else1\n.ifstart1\n\tLDA #0\n\tJMP .ifend1\n.else1\n\tLDA #1\n.ifend1\n\tTAX\n\tBEQ .ifstart3\n.ifstart3\n\tLDA #0\n\tJMP .ifend3\n.else3\n\tLDA #1\n.ifend3\n\tTAY"));
    }
    
    #[test]
    fn cond_expr_immediate_test5() {
        let args = sargs(1);
        let input = "void main() { X = 0 || Y; Y = 1 || 0;}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CPY #0\n\tBNE .else1\n\tLDA #0\n\tJMP .ifend1\n.else1\n\tLDA #1\n.ifend1\n\tTAX\n\tLDY #1"));
    }
    
    #[test]
    fn cond_expr_immediate_test6() {
        let args = sargs(1);
        let input = "void main() { X = Y || 1; Y = X || 0;}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        // Far from optimal, but the result if correct
        assert!(result.contains("CPY #0\n\tBNE .else1\n\tJMP .else1\n\tLDA #0\n\tJMP .ifend1\n.else1\n\tLDA #1\n.ifend1\n\tTAX\n\tBNE .else2\n\tLDA #0\n\tJMP .ifend2\n.else2\n\tLDA #1\n.ifend2\n\tTAY"));
    }
    
    #[test]
    fn cond_expr_immediate_test7() {
        let args = sargs(1);
        let input = "void main() { X = 0 || 0; Y = 0 || X;}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        // Far from optimal, but the result if correct
        assert!(result.contains("LDX #0\n\tLDA #0\n\tJMP .ifend2\n.else2\n\tLDA #1\n.ifend2\n\tTAY"));
    }
    
    #[test]
    fn ternary_immediate_test3() {
        let args = sargs(1);
        let input = "char i; void main() { X = (0 && 1)?2:3; Y = (1 && i)?3:4; X = (1 && 0)?2:3;}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #3\n\tLDA i\n\tBEQ .else2\n\tLDA #3\n\tJMP .ifend2\n.else2\n\tLDA #4\n.ifend2\n\tTAY\n\tLDX #3"));
    }
    
    #[test]
    fn ternary_immediate_test4() {
        let args = sargs(1);
        let input = "char i; void main() { X = (0 || 1)?2:3; Y = (1 || i)?3:4; X = (0 || 0)?2:3;}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #2\n\tLDY #3\n\tLDX #3"));
    }
    
    #[test]
    fn ternary_immediate_test5() {
        let args = sargs(1);
        let input = "char array[(1 == 0)?2:3]; void main() { X = sizeof(array);}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #3"));
    }
    
    #[test]
    fn sizeof_test1() {
        let args = sargs(1);
        let input = "char arr1[3]; char *arr2[3]; const char *ptr[] = { arr1 }; void main() { X = sizeof(arr1); Y = sizeof(arr2); X = sizeof(ptr); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #3\n\tLDY #6\n\tLDX #2"));
    }
    
    #[test]
    fn sizeof_test2() {
        let args = sargs(1);
        let input = "void main() { X = sizeof(char); Y = sizeof(int);}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #1\n\tLDY #2"));
    }
    
    #[test]
    fn minusminus_statement_test() {
        let args = sargs(1); 
        let input = "char array[3]; void main() { array[--X] = Y; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("DEX\n\tSTY array,X"));
    }

    #[test]
    fn define_test1() {
        let args = sargs(1); 
        let input = "#define macro() X\nvoid main() { Y = macro(); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("TXA\n\tTAY"));
    }
    
    #[test]
    fn define_test2() {
        let args = sargs(1); 
        let input = "#define macro X\nvoid main() { Y = macro; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("TXA\n\tTAY"));
    }

    #[test]
    fn function_call_test1() {
        let args = sargs(1); 
        let input = "char f() { return 2;} void main() { Y = f(); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("f\tSUBROUTINE\n\tLDA #2\n\tRTS"));
        assert!(result.contains("JSR f\n\tTAY"));
    } 
    
    #[test]
    fn function_call_test2() {
        let args = sargs(1); 
        let input = "char f() { return Y;} void main() { Y = f(); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("f\tSUBROUTINE\n\tTYA\n\tRTS\n\tRTS\n\nmain\tSUBROUTINE\n\tJSR f\n\tTAY"));
    } 
    
    #[test]
    fn if_16bits_test1() {
        let args = sargs(1); 
        let input = "int a; void main() { if (a == 10000) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("SEC\n\tLDA a\n\tSBC #16\n\tSTA cctmp\n\tLDA a+1\n\tSBC #39\n\tBNE .ifend1\n\tLDA cctmp\n\tBNE .ifend1\n\tLDX #1\n.ifend1"));
    } 
    
    #[test]
    fn if_16bits_test2() {
        let args = sargs(1); 
        let input = "int a; void main() { if (a != 10000) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("SEC\n\tLDA a\n\tSBC #16\n\tSTA cctmp\n\tLDA a+1\n\tSBC #39\n\tBNE .ifstart1\n\tLDA cctmp\n\tBEQ .ifend1\n.ifstart1\n\tLDX #1\n.ifend1"));
    } 
    
    #[test]
    fn if_16bits_test3() {
        let args = sargs(1); 
        let input = "int a; void main() { if (a == 0) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA a\n\tSTA cctmp\n\tLDA a+1\n\tBNE .ifend1\n\tLDA cctmp\n\tBNE .ifend1\n\tLDX #1\n.ifend1"));
    } 
    
    #[test]
    fn if_16bits_test4() {
        let args = sargs(1); 
        let input = "int a; void main() { if (a != 0) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA a\n\tSTA cctmp\n\tLDA a+1\n\tBNE .ifstart1\n\tLDA cctmp\n\tBEQ .ifend1\n.ifstart1\n\tLDX #1\n.ifend1"));
    } 
    
    #[test]
    fn if_16bits_test5() {
        let args = sargs(1); 
        let input = "int a; void main() { if (a >= 0) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA a+1\n\tBMI .ifend1\n\tLDX #1\n.ifend1"));
    } 
    
    #[test]
    fn if_16bits_test6() {
        let args = sargs(1); 
        let input = "int a; void main() { if (a) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA a\n\tSTA cctmp\n\tLDA a+1\n\tBNE .ifstart1\n\tLDA cctmp\n\tBEQ .ifend1\n.ifstart1\n\tLDX #1\n.ifend1"));
    } 
    
    #[test]
    fn if_16bits_test7() {
        let args = sargs(1); 
        let input = "int a; void main() { if (!a) X = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA a\n\tSTA cctmp\n\tLDA a+1\n\tBNE .ifend1\n\tLDA cctmp\n\tBNE .ifend1\n\tLDX #1\n.ifend1"));
    } 
    
    #[test]
    fn negate_test1() {
        let args = sargs(1); 
        let input = "int a; void main() { a = -a; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("SEC\n\tLDA #0\n\tSBC a\n\tSTA a\n\tLDA #0\n\tSBC a+1\n\tSTA a+1"));
    } 
    
    #[test]
    fn negate_test2() {
        let args = sargs(1); 
        let input = "char a; void main() { a = -a; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("SEC\n\tLDA #0\n\tSBC a\n\tSTA a"));
    } 

    #[test]
    fn asm_test1() {
        let args = sargs(1); 
        let input = "void main() { asm(\"LDA #32\\n\\tSTA cctmp\"); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #32\n\tSTA cctmp\n\t"));
    } 
    
    #[test]
    fn asm_test2() {
        let args = sargs(1); 
        let input = "void main() { asm(\"LDA #32\\n\\tSTA cctmp\", 4); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #32\n\tSTA cctmp\n\t"));
    } 
    
    #[test]
    fn link_test1() {
        let args = sargs(1); 
        let input = "void fn1() {}; void fn2() {}; void main() { fn1(); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("fn1\tSUBROUTINE"));
        assert!(!result.contains("fn2\tSUBROUTINE"));
    } 
    
    #[test]
    fn link_test2() {
        let args = sargs(1); 
        let input = "void fn1() {}; void interrupt fn2() {}; void main() { fn1(); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("fn1\tSUBROUTINE"));
        assert!(result.contains("fn2\tSUBROUTINE"));
    } 
    
    #[test]
    fn link_test3() {
        let args = sargs(1); 
        let input = "void fn2(); void fn1() {fn2();}; void fn2() {}; void fn3() {}; void fn4() {}; void main() { fn1(); fn4();}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("fn1\tSUBROUTINE"));
        assert!(result.contains("fn2\tSUBROUTINE"));
        assert!(!result.contains("fn3\tSUBROUTINE"));
        assert!(result.contains("fn4\tSUBROUTINE"));
    } 
    
    #[test]
    fn bnot_test() {
        let args = sargs(1); 
        let input = "void main() { X = ~Y; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("TYA\n\tEOR #255\n\tTAX"));
    } 
    
    #[test]
    fn and_test1() {
        let args = sargs(1); 
        let input = "char *x; void main() { Y = x & 0xff; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA x\n\tTAY"));
    } 
    
    #[test]
    fn and_test2() {
        let args = sargs(1); 
        let input = "short x; void main() { Y = x & 0xff; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDY x\n"));
    } 
    
    #[test]
    fn and_test3() {
        let args = sargs(1); 
        let input = "short x, y; void main() { y = x & 0xff; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA x\n\tSTA y\n\tLDA #0\n\tSTA y+1\n"));
    } 
    
    #[test]
    fn and_test4() {
        let args = sargs(1); 
        let input = "short x; void main() { Y = x & 0; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA x\n\tAND #0\n\tTAY"));
    } 
    
    #[test]
    fn carry_propagation_error_test() {
        let args = sargs(1); 
        let input = "short x, y; void main() { x += y + 1; }";
        let mut output = Vec::new();
        let result = compile(input.as_bytes(), &mut output, &args, simple_build);
        assert!(result.is_err());
    } 
    
    #[test]
    fn macro_test1() {
        let args = sargs(1);
        let input = "#define zobi(a,b) a+b\nvoid main() { X = zobi(zobi(1,zobi(12,2)),zobi(3,4)); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDX #22"));
    }

    #[test]
    fn array_decl_test1() {
        let args = sargs(1);
        let input = "const char hello[] = \"Hello\"; const char a[] = {0, hello, hello & 0xff, hello >> 8};";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("hex 00\n\t.byte <hello\n\t.byte <hello\n\t.byte >hello"));
    }

    #[test]
    fn decl_test1() {
        let args = sargs(1);
        let input = "const char hello[] = \"Hello\"; const char x = hello & 0xff; const char y = hello >> 8;";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("x                      \tEQU <hello\ny                      \tEQU >hello"));
    }

    #[test]
    fn local_var_test1() {
        let args = sargs(1);
        let input = "void main() { char i; i = X; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LOCAL_VARIABLES_0\n\n\tORG LOCAL_VARIABLES_0\nmain_1_i               \tds 1"));
        assert!(result.contains("main\tSUBROUTINE\n\tSTX main_1_i\n\tRTS"));
    }
    
    #[test]
    fn local_var_test2() {
        let args = sargs(1);
        let input = "void f() { char j; j = Y; }\nvoid main() { char i; i = X; f(); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LOCAL_VARIABLES_0\n\n\tORG LOCAL_VARIABLES_0\nmain_1_i               \tds 1\n\nLOCAL_VARIABLES_1\n\n\tORG LOCAL_VARIABLES_1\nf_1_j                  \tds 1"));
    }
    
    #[test]
    fn local_var_test3() {
        let args = sargs(1);
        let input = "void main() { char i, j; i = X; j = Y; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LOCAL_VARIABLES_0\n\n\tORG LOCAL_VARIABLES_0\nmain_1_i               \tds 1\nmain_1_j               \tds 1"));
    }
    
    #[test]
    fn local_var_test4() {
        let args = sargs(1);
        let input = "void main() { char i; i = X; if (X) { char i; i = X; } i = Y;}";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LOCAL_VARIABLES_0\nmain_1_i               \tds 1\nmain_2_i               \tds 1"));
        assert!(result.contains("STX main_1_i\n\tCPX #0\n\tBEQ .ifend1\n\tSTX main_2_i\n.ifend1\n\tSTY main_1_i"));
    }
    
    #[test]
    fn local_var_test5() {
        let args = sargs(1);
        let input = "void main() { const char i = 7; X = i; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("main_1_i               \tEQU $7"));
        assert!(result.contains("LDX #7"));
    }
    
    #[test]
    fn local_var_test6() {
        let args = sargs(1);
        let input = "void main() { char i = 7; X = i; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LOCAL_VARIABLES_0\n\n\tORG LOCAL_VARIABLES_0\nmain_1_i               \tds 1"));
        assert!(result.contains("main\tSUBROUTINE\n\tLDA #7\n\tSTA main_1_i\n\tLDX main_1_i"));
    }
    
    #[test]
    fn local_var_test7() {
        let args = sargs(1);
        let input = "void main() { char i = 7, j = 8; X = i; Y = j; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LOCAL_VARIABLES_0\n\n\tORG LOCAL_VARIABLES_0\nmain_1_i               \tds 1\nmain_1_j               \tds 1"));
        assert!(result.contains("main\tSUBROUTINE\n\tLDA #7\n\tSTA main_1_i\n\tLDA #8\n\tSTA main_1_j\n\tLDX main_1_i\n\tLDY main_1_j"));
    }
    
    #[test]
    fn local_var_test8() {
        let args = sargs(1);
        let input = "void main() { char i[2], j[3]; i[0] = X; j[1] = Y; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LOCAL_VARIABLES_0\n\n\tORG LOCAL_VARIABLES_0\nmain_1_i               \tds 2\nmain_1_j               \tds 3"));
        assert!(result.contains("main\tSUBROUTINE\n\tSTX main_1_i\n\tSTY main_1_j+1"));
    }
    
    #[test]
    fn local_var_test9() {
        let args = sargs(1);
        let input = "void main() { int i = 0; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LOCAL_VARIABLES_0\n\n\tORG LOCAL_VARIABLES_0\nmain_1_i               \tds 2\n"));
        assert!(result.contains("main\tSUBROUTINE\n\tLDA #0\n\tSTA main_1_i\n\tSTA main_1_i+1"));
    }
    
    #[test]
    fn local_var_test10() {
        let args = sargs(1);
        let input = "
void fn1() { char x, y; }; 
void fn2() { char x, y; fn1(); }
void fn3() { char x; }
void main() { fn2(); fn3(); }
            ";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LOCAL_VARIABLES_1\n\n\tORG LOCAL_VARIABLES_1\nfn2_1_x                \tds 1\nfn2_1_y                \tds 1\n\tORG LOCAL_VARIABLES_1\nfn3_1_x                \tds 1\n\tORG LOCAL_VARIABLES_1 + 2\n\nLOCAL_VARIABLES_2\n\n\tORG LOCAL_VARIABLES_2\nfn1_1_x                \tds 1\nfn1_1_y                \tds 1"));
    }
    
    #[test]
    fn params_test1() {
        let args = sargs(1);
        let input = "void f(char x, int y) { x = y; }; void main() { f(1, 2); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("ORG LOCAL_VARIABLES_1\nf_x                    \tds 1\nf_y                    \tds 2"));
        assert!(result.contains("f\tSUBROUTINE\n\tLDA f_y\n\tSTA f_x\n\tRTS"));
        assert!(result.contains("main\tSUBROUTINE\n\tLDA #1\n\tSTA f_x\n\tLDA #2\n\tSTA f_y\n\tLDA #0\n\tSTA f_y+1\n\tJSR f\n\tRTS"));
    }
    
    #[test]
    fn params_test2() {
        let args = sargs(1);
        let input = "char f(char x, int y) { return x + y; }; void main() { X = f(1, 2); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("f\tSUBROUTINE\n\tCLC\n\tLDA f_x\n\tADC f_y\n\tRTS\n\tRTS\n\nmain\tSUBROUTINE\n\tLDA #1\n\tSTA f_x\n\tLDA #2\n\tSTA f_y\n\tLDA #0\n\tSTA f_y+1\n\tJSR f\n\tTAX\n\tRTS"));
    }
    
    #[test]
    fn params_test3() {
        let args = sargs(1);
        let input = "char f(char x, char y) { return x + y; }; void main() { char x, y; x = X; y = f(1, 2); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("f\tSUBROUTINE\n\tCLC\n\tLDA f_x\n\tADC f_y\n\tRTS\n\tRTS\n\nmain\tSUBROUTINE\n\tSTX main_1_x\n\tLDA #1\n\tSTA f_x\n\tLDA #2\n\tSTA f_y\n\tJSR f\n\tSTA main_1_y\n\tRTS"));
    }

    #[test]
    fn params_test4() {
        let args = sargs(1);
        let input = "char x, y; void f(char *x, char y) { x[Y = 0] = y; }; void main() { f(&x, y); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("f\tSUBROUTINE\n\tLDY #0\n\tLDA f_y\n\tSTA (f_x),Y\n\tRTS\n\nmain\tSUBROUTINE\n\tLDA #<x\n\tSTA f_x\n\tLDA #>x\n\tSTA f_x+1\n\tLDA y\n\tSTA f_y\n\tJSR f\n\tRTS"));
    }
    
    #[test]
    fn params_test5() {
        let args = sargs(1);
        let input = "char x, y; void f(char *x, char y) { x[0] = y; }; void main() { f(&x, y); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("f\tSUBROUTINE\n\tSTY cctmp\n\tLDY #0\n\tLDA f_y\n\tSTA (f_x),Y\n\tLDY cctmp\n\tRTS"));
    }
    
    #[test]
    fn params_test6() {
        let args = sargs(1);
        let input = "char x, y; void f(char *x, char y) { *x = y; }; void main() { f(&x, y); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("f\tSUBROUTINE\n\tSTY cctmp\n\tLDY #0\n\tLDA f_y\n\tSTA (f_x),Y\n\tLDY cctmp\n\tRTS"));
    }
    
    #[test]
    fn params_test7() {
        let args = sargs(1);
        let input = "char x, y, z; void f(char *x, char y, char z) { *x = z; }; void main() { f(&x, y, z); }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("f\tSUBROUTINE\n\tSTY cctmp\n\tLDY #0\n\tLDA f_z\n\tSTA (f_x),Y\n\tLDY cctmp\n\tRTS\n\nmain\tSUBROUTINE\n\tLDA #<x\n\tSTA f_x\n\tLDA #>x\n\tSTA f_x+1\n\tLDA y\n\tSTA f_y\n\tLDA z\n\tSTA f_z\n\tJSR f\n\tRTS"));
    }
    
    #[test]
    fn var_test1() {
        let args = sargs(1);
        let input = "char charx;";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("charx                  \tds 1"));
    }
    
    #[test]
    fn whitespace_test() {
        let args = sargs(1);
        let input = "void main() { char charz; charz = 1; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA #1\n\tSTA main_1_charz"));
    }
    
    #[test]
    fn add_test1() {
        let args = sargs(1); 
        let input = "void main() { short int a; a += 0x100; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("CLC\n\tLDA main_1_a+1\n\tADC #1\n\tSTA main_1_a+1\n\tRTS"));
    } 
    
    #[test]
    fn and_16bits_test() {
        let args = sargs(1); 
        let input = "void main() { char *ptr; ptr &= 0x1ff; }";
        let mut output = Vec::new();
        compile(input.as_bytes(), &mut output, &args, simple_build).unwrap();
        let result = str::from_utf8(&output).unwrap();
        print!("{:?}", result);
        assert!(result.contains("LDA main_1_ptr+1\n\tAND #1\n\tSTA main_1_ptr+1"));
    } 
    
}
