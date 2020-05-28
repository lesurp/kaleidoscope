#![feature(generators, generator_trait)]

mod lexer;
mod parser;

use lexer::Lexer;


fn main() {
    let stdin = std::io::stdin();
    let lexer = Lexer::new(&mut stdin.lock());
}

