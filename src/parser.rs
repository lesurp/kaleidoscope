use crate::lexer::{Lexer, LexerToken, LexingError};
use std::io::BufRead;
use std::ops::{Generator, GeneratorState};
use std::pin::Pin;

impl<'a, R: BufRead> Generator for AstGenerator<'a, R> {
    type Yield = Result<AstNode, ParsingError>;
    type Return = ();
    fn resume(self: Pin<&mut Self>, _: ()) -> GeneratorState<Self::Yield, Self::Return> {
        match AstNode::try_from_lexer(Pin::into_inner(self).0) {
            Ok(Some(t)) => GeneratorState::Yielded(Ok(t)),
            Err(e) => GeneratorState::Yielded(Err(e)),
            Ok(None) => GeneratorState::Complete(()),
        }
    }
}

impl<'a, R: BufRead> IntoIterator for AstGenerator<'a, R> {
    type Item = Result<AstNode, ParsingError>;
    type IntoIter = GeneratorIteratorAdapter<AstGenerator<'a, R>>;
    fn into_iter(self) -> Self::IntoIter {
        GeneratorIteratorAdapter(Box::pin(self))
    }
}

pub struct GeneratorIteratorAdapter<G: Generator>(Pin<Box<G>>);
impl<G: Generator> Iterator for GeneratorIteratorAdapter<G> {
    type Item = G::Yield;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.as_mut().resume(()) {
            GeneratorState::Yielded(x) => Some(x),
            GeneratorState::Complete(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParsingError {
    LexingError(LexingError),
    ExpectedIdent,
    ExpectedCommaOrClosingParenthesis,
    ExpectedClosingParenthesis,
    ExpectedPrimaryExpression,
    ExpectedBinaryOperator,
    ExpectedOpeningParenthesis,
}

impl From<LexingError> for ParsingError {
    fn from(l: LexingError) -> Self {
        ParsingError::LexingError(l)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnProto(String, Vec<String>);

#[derive(Debug, Clone, PartialEq)]
pub enum AstNode {
    Number(f64),
    Ident(String),
    Binary(char, Box<AstNode>, Box<AstNode>),
    Call(String, Vec<AstNode>),
    FnDec(FnProto),
    FnDef(FnProto, Box<AstNode>),
}

fn precedence(c: char) -> Option<u32> {
    Some(match c {
        '<' => 10,
        '+' => 20,
        '-' => 20,
        '*' => 40,
        _ => return None,
    })
}

pub struct Ast(Vec<AstNode>);
pub struct AstGenerator<'a, R: BufRead>(pub &'a mut Lexer<'a, R>);

impl Ast {
    pub fn try_from_lexer<'a, R: BufRead>(lexer: &mut Lexer<'a, R>) -> Result<Self, ParsingError> {
        let mut ast = Vec::new();
        while let Some(node) = AstNode::try_from_lexer(lexer)? {
            ast.push(node);
        }
        Ok(Ast(ast))
    }

    pub fn try_from_str(s: &str) -> Result<Self, ParsingError> {
        let mut s_u8 = s.as_bytes();
        let mut lexer = Lexer::new(&mut s_u8);
        Self::try_from_lexer(&mut lexer)
    }
}

impl AstNode {
    pub fn try_from_lexer<'a, R: BufRead>(
        lexer: &mut Lexer<'a, R>,
    ) -> Result<Option<Self>, ParsingError> {
        loop {
            match lexer.peek()? {
                None => return Ok(None),
                Some(LexerToken::Kwd(';')) => {
                    lexer.token().unwrap();
                }
                Some(LexerToken::Extern) => return AstNode::parse_extern(lexer).map(|n| Some(n)),
                Some(LexerToken::Def) => return AstNode::parse_definition(lexer).map(|n| Some(n)),
                Some(_) => return AstNode::parse_toplevel(lexer).map(|n| Some(n)),
            }
        }
    }

    /// For testing!
    fn as_top_level(self) -> Self {
        AstNode::FnDef(FnProto("".to_owned(), Vec::new()), self.into())
    }

    fn parse_raw_ident<R: BufRead>(lexer: &mut Lexer<R>) -> Result<String, ParsingError> {
        match lexer.token()? {
            Some(LexerToken::Ident(i)) => Ok(i),
            _ => Err(ParsingError::ExpectedIdent),
        }
    }

    fn parse_raw_operator<R: BufRead>(lexer: &mut Lexer<R>) -> Result<char, ParsingError> {
        match lexer.token()? {
            Some(LexerToken::Kwd(c)) => match precedence(c) {
                Some(_) => Ok(c),
                None => Err(ParsingError::ExpectedBinaryOperator),
            },
            _ => Err(ParsingError::ExpectedBinaryOperator),
        }
    }

    fn parse_number<R: BufRead>(_: &mut Lexer<R>, t: f64) -> Result<Self, ParsingError> {
        Ok(AstNode::Number(t))
    }

    fn parse_call_parameters<R: BufRead>(lexer: &mut Lexer<R>) -> Result<Vec<Self>, ParsingError> {
        assert!(matches!(lexer.token(), Ok(Some(LexerToken::Kwd('(')))));

        let mut elems = Vec::new();
        loop {
            elems.push(AstNode::parse_primary(lexer)?);

            match lexer.token()? {
                Some(LexerToken::Kwd(',')) => {}
                Some(LexerToken::Kwd(')')) => return Ok(elems),
                // expected comma/parenthesis after expression
                _ => return Err(ParsingError::ExpectedCommaOrClosingParenthesis),
            }
        }
    }

    fn parse_primary<R: BufRead>(lexer: &mut Lexer<R>) -> Result<Self, ParsingError> {
        match lexer.token()? {
            Some(LexerToken::Number(n)) => AstNode::parse_number(lexer, n),
            Some(LexerToken::Ident(i)) => {
                if matches!(lexer.peek()?, Some(LexerToken::Kwd('('))) {
                    Ok(AstNode::Call(i, AstNode::parse_call_parameters(lexer)?))
                } else {
                    Ok(AstNode::Ident(i))
                }
            }
            Some(LexerToken::Kwd('(')) => {
                let node = AstNode::parse_expr(lexer);
                if matches!(lexer.token()?, Some(LexerToken::Kwd(')'))) {
                    node
                } else {
                    // expecting closnig ')'
                    Err(ParsingError::ExpectedClosingParenthesis)
                }
            }
            _ => Err(ParsingError::ExpectedPrimaryExpression),
        }
    }

    fn parse_expr<R: BufRead>(lexer: &mut Lexer<R>) -> Result<Self, ParsingError> {
        let lhs = AstNode::parse_primary(lexer)?;
        println!("lhs: {:?}", lhs);
        println!("peek: {:?}", lexer.peek()?);
        match lexer.peek()? {
            Some(LexerToken::Kwd(c)) => match precedence(*c) {
                Some(_) => AstNode::parse_expr_rec(lexer, lhs),
                None => Ok(lhs),
            },
            _ => return Ok(lhs),
        }
    }

    fn parse_expr_rec<R: BufRead>(
        lexer: &mut Lexer<R>,
        lhs: AstNode,
    ) -> Result<Self, ParsingError> {
        let prev_op = AstNode::parse_raw_operator(lexer)?;
        let rhs = AstNode::parse_primary(lexer)?;
        match lexer.peek()? {
            Some(LexerToken::Kwd(c)) => {
                Ok(match precedence(*c) {
                    Some(prec_next) => {
                        let should_nomnom = prec_next > precedence(prev_op).unwrap();
                        // keep nomnom'ing if precedence is higher e.g. a + b * c
                        // then our new rhs is the recursively parsed b * c
                        if should_nomnom {
                            let rhs = AstNode::parse_expr_rec(lexer, rhs)?;
                            AstNode::Binary(prev_op, lhs.into(), rhs.into())
                        }
                        // otherwise; e.g. a * b + c,
                        // we replace the lhs with the already parsed binary expr <=> lhs prev_op rhs,
                        // and we parse another rhs
                        else {
                            let lhs = AstNode::Binary(prev_op, lhs.into(), rhs.into());
                            AstNode::parse_expr_rec(lexer, lhs)?
                        }
                    }

                    None => AstNode::Binary(prev_op, lhs.into(), rhs.into()),
                })
            }
            _ => return Ok(lhs),
        }
    }

    fn parse_prototype<R: BufRead>(lexer: &mut Lexer<R>) -> Result<FnProto, ParsingError> {
        Ok(FnProto(
            AstNode::parse_raw_ident(lexer)?,
            AstNode::parse_prototype_args(lexer)?,
        ))
    }

    fn parse_prototype_args<R: BufRead>(lexer: &mut Lexer<R>) -> Result<Vec<String>, ParsingError> {
        if !matches!(lexer.token()?, Some(LexerToken::Kwd('('))) {
            // expected (
            return Err(ParsingError::ExpectedOpeningParenthesis);
        }

        let mut elems = Vec::new();
        loop {
            elems.push(AstNode::parse_raw_ident(lexer)?);

            match lexer.token()? {
                Some(LexerToken::Kwd(',')) => {}
                Some(LexerToken::Kwd(')')) => return Ok(elems),
                // expected comma/parenthesis after expression
                _ => return Err(ParsingError::ExpectedCommaOrClosingParenthesis),
            }
        }
    }

    fn parse_definition<R: BufRead>(lexer: &mut Lexer<R>) -> Result<Self, ParsingError> {
        assert!(matches!(lexer.token(), Ok(Some(LexerToken::Def))));
        Ok(AstNode::FnDef(
            AstNode::parse_prototype(lexer)?,
            AstNode::parse_expr(lexer)?.into(),
        ))
    }

    fn parse_extern<R: BufRead>(lexer: &mut Lexer<R>) -> Result<Self, ParsingError> {
        assert!(matches!(lexer.token(), Ok(Some(LexerToken::Extern))));
        Ok(AstNode::FnDec(AstNode::parse_prototype(lexer)?))
    }

    fn parse_toplevel<R: BufRead>(lexer: &mut Lexer<R>) -> Result<Self, ParsingError> {
        Ok(AstNode::FnDef(
            FnProto("".to_owned(), Vec::new()),
            AstNode::parse_expr(lexer)?.into(),
        ))
    }
}

#[cfg(test)]
mod test {
    use super::{Ast, AstNode, FnProto};
    use crate::lexer::Lexer;

    #[test]
    fn parse_variable() {
        let var = "var".to_owned();
        let ast = Ast::try_from_str(&var).unwrap();
        let expected = AstNode::Ident(var);
        let parsed = ast.0.first().unwrap();

        assert_eq!(ast.0.len(), 1);
        assert_eq!(parsed, &expected.as_top_level());
    }

    #[test]
    fn parse_number() {
        let var = 1.123;
        let ast = Ast::try_from_str(&var.to_string()).unwrap();
        let expected = AstNode::Number(var);
        let parsed = ast.0.first().unwrap();

        assert_eq!(ast.0.len(), 1);
        assert_eq!(parsed, &expected.as_top_level());
    }

    #[test]
    fn parse_def() {
        let var = "def foo(x, y) x+foo(y, 4.0);"; // from LLVM's site :)
        let ast = Ast::try_from_str(&var.to_string()).unwrap();

        assert_eq!(ast.0.len(), 1);
        match ast.0.first() {
            Some(AstNode::FnDef(FnProto(fn_name, args), _)) => {
                assert_eq!(fn_name, "foo");
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], "x");
                assert_eq!(args[1], "y");
            }
            _ => panic!("Wrong node type :("),
        }
    }

    #[test]
    fn parse_def2() {
        let var = "def foo(x) x+1;";
        let mut s_u8 = var.as_bytes();
        let mut lexer = Lexer::new(&mut s_u8);
        lexer.peek_nth(10).unwrap();
        println!("{:?}", lexer.parsed_buf);
        let ast = Ast::try_from_str(&var.to_string()).unwrap();

        assert_eq!(ast.0.len(), 1);
        match ast.0.first() {
            Some(AstNode::FnDef(FnProto(fn_name, args), _)) => {
                assert_eq!(fn_name, "foo");
                assert_eq!(args.len(), 1);
                assert_eq!(args[0], "x");
            }
            _ => panic!("Wrong node type :("),
        }
    }

    #[test]
    fn parse_extern() {
        let var = "extern sin(a);"; // from LLVM's site :)
        let ast = Ast::try_from_str(&var.to_string()).unwrap();

        assert_eq!(ast.0.len(), 1);
        match ast.0.first() {
            Some(AstNode::FnDec(FnProto(fn_name, args))) => {
                assert_eq!(fn_name, "sin");
                assert_eq!(args.len(), 1);
                assert_eq!(args[0], "a");
            }
            _ => panic!("Wrong node type :("),
        }
    }

    #[test]
    fn parse_def_and_toplevel() {
        let var = "def foo(x, y, z) x+y*z y;"; // from LLVM's site :)
        let ast = Ast::try_from_str(&var.to_string()).unwrap();

        assert_eq!(ast.0.len(), 2);
        match ast.0.first() {
            Some(AstNode::FnDef(FnProto(fn_name, args), _)) => {
                assert_eq!(fn_name, "foo");
                assert_eq!(args.len(), 3);
                assert_eq!(args[0], "x");
                assert_eq!(args[1], "y");
                assert_eq!(args[2], "z");
            }
            _ => panic!("Wrong node type :("),
        }

        assert_eq!(ast.0[1], AstNode::Ident("y".to_owned()).as_top_level());
    }
}
