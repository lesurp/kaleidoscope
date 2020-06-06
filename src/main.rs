#![feature(generators, generator_trait)]

mod lexer;
mod llvm_stuff;
mod parser;

use lexer::{Lexer, LexingError, Newliner};
use llvm_stuff::LlvmStuff;
use parser::{AstGenerator, ParsingError};
use std::io::Write;

struct ReplNewline;
impl Newliner for ReplNewline {
    fn new_line(&self) {
        print!(">> ");
        std::io::stdout()
            .flush()
            .expect("I don't deal with stdout-writing problems");
    }
}

fn main() {
    env_logger::init();

    let stdin = std::io::stdin();
    let mut stdin = stdin.lock();

    let mut lexer = Lexer::with_newliner(&mut stdin, ReplNewline);

    let mut llvm = LlvmStuff::new("kaleidoscope");
    for ast_node in AstGenerator(&mut lexer) {
        match ast_node {
            Ok(ast) => {
                println!("\t{:?}", ast);
                let val = llvm.ast_node_to_llvm(ast);
                LlvmStuff::dump_value(val);
            }
            Err(ParsingError::LexingError(LexingError::IoError)) => panic!("Can't deal with that"),
            Err(ParsingError::LexingError(LexingError::IncompleteToken)) => break,

            Err(ParsingError::IncompleteAstError) => continue,
            Err(ParsingError::FatalError(e)) => panic!(
                "Something wrong, so I'm just gonna panic, whatever ({:?}",
                e
            ),
        }
    }
}
