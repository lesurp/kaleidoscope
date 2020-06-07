use crate::lexer::{Lexer, LexerToken, LexerTrait, LexingError};
use log::debug;
use std::ops::{Generator, GeneratorState};
use std::pin::Pin;

impl<'a, L: LexerTrait> Generator for AstGenerator<'a, L> {
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

impl<'a, L: LexerTrait> IntoIterator for AstGenerator<'a, L> {
    type Item = Result<AstNode, ParsingError>;
    type IntoIter = GeneratorIteratorAdapter<AstGenerator<'a, L>>;
    fn into_iter(self) -> Self::IntoIter {
        GeneratorIteratorAdapter(Box::pin(self))
    }
}

pub struct AstGenerator<'a, L: LexerTrait>(pub &'a mut L);

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
    IncompleteAstError,
    FatalError(FatalError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IncompleteAstError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FatalError {
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

impl From<FatalError> for ParsingError {
    fn from(l: FatalError) -> Self {
        ParsingError::FatalError(l)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnProto(pub String, pub Vec<String>);

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
        '/' => 40,
        _ => return None,
    })
}

impl AstNode {
    pub fn try_all_from_lexer<'a, L: LexerTrait>(lexer: &mut L) -> Result<Vec<Self>, ParsingError> {
        let mut ast = Vec::new();
        while let Some(node) = AstNode::try_from_lexer(lexer)? {
            ast.push(node);
        }
        Ok(ast)
    }

    pub fn try_all_from_str(s: &str) -> Result<Vec<Self>, ParsingError> {
        let mut s_u8 = s.as_bytes();
        let mut lexer = Lexer::new(&mut s_u8);
        Self::try_all_from_lexer(&mut lexer)
    }

    pub fn try_from_lexer<'a, L: LexerTrait>(lexer: &mut L) -> Result<Option<Self>, ParsingError> {
        let node = loop {
            let next_token = lexer.cursor_next()?;
            debug!("next_token to feed to the ast builder: {:?}", next_token);
            match next_token {
                None => break Ok(None),
                Some(LexerToken::Kwd(';')) => {}
                Some(LexerToken::Extern) => break AstNode::parse_extern(lexer).map(|n| Some(n)),
                Some(LexerToken::Def) => break AstNode::parse_definition(lexer).map(|n| Some(n)),
                Some(token) => {
                    let token = token.clone();
                    break AstNode::parse_toplevel(lexer, token).map(|n| Some(n));
                }
            }
        };

        match &node {
            Ok(n) => {
                debug!(
                    "A node was built, consuming the corresponding lexer tokens: {:?}",
                    n
                );
                lexer.consume();
            }
            Err(ParsingError::IncompleteAstError) => {
                debug!("AST node possibly incomplete - reet the lexer");
                lexer.reset()
            }
            _ => {}
        }

        node
    }

    #[cfg(test)]
    fn as_top_level(self) -> Self {
        AstNode::FnDef(FnProto("".to_owned(), Vec::new()), self.into())
    }

    fn parse_raw_ident<L: LexerTrait>(lexer: &mut L) -> Result<String, ParsingError> {
        debug!("parse_raw_ident");
        match lexer.cursor_next()? {
            Some(LexerToken::Ident(i)) => Ok(i.clone()),
            Some(_) => Err(ParsingError::FatalError(FatalError::ExpectedIdent)),
            None => Err(ParsingError::IncompleteAstError),
        }
    }

    fn parse_raw_operator<L: LexerTrait>(lexer: &mut L) -> Result<char, ParsingError> {
        debug!("parse_raw_operator");
        let next = lexer.cursor_next()?;
        debug!("next: {:?}", next);
        match next {
            Some(LexerToken::Kwd(c)) => match precedence(*c) {
                Some(_) => Ok(*c),
                None => Err(ParsingError::FatalError(FatalError::ExpectedBinaryOperator)),
            },
            Some(_) => Err(ParsingError::FatalError(FatalError::ExpectedBinaryOperator)),
            None => Err(ParsingError::IncompleteAstError),
        }
    }

    fn parse_number<L: LexerTrait>(_: &mut L, t: f64) -> Result<Self, ParsingError> {
        debug!("parse_number");
        Ok(AstNode::Number(t))
    }

    fn parse_call_parameters<L: LexerTrait>(lexer: &mut L) -> Result<Vec<Self>, ParsingError> {
        debug!("parse_call_parameters");
        let mut elems = Vec::new();
        loop {
            elems.push(AstNode::parse_primary(lexer)?);

            match lexer.cursor_next()? {
                Some(LexerToken::Kwd(',')) => {}
                Some(LexerToken::Kwd(')')) => return Ok(elems),
                // expected comma/parenthesis after expression
                Some(_) => {
                    return Err(ParsingError::FatalError(
                        FatalError::ExpectedCommaOrClosingParenthesis,
                    ))
                }
                None => return Err(ParsingError::IncompleteAstError),
            }
        }
    }

    fn parse_primary_with_token<L: LexerTrait>(
        lexer: &mut L,
        next: Option<LexerToken>,
    ) -> Result<Self, ParsingError> {
        debug!("parse_primary_with_token");
        debug!("Next token: {:?}", next);
        match next {
            Some(LexerToken::Number(n)) => AstNode::parse_number(lexer, n),
            Some(LexerToken::Ident(i)) => {
                if matches!(lexer.peek()?, Some(LexerToken::Kwd('('))) {
                    lexer.cursor_next()?; // consume the opening parenthesis
                    Ok(AstNode::Call(i, AstNode::parse_call_parameters(lexer)?))
                } else {
                    debug!("Returning mah ident");
                    Ok(AstNode::Ident(i))
                }
            }
            Some(LexerToken::Kwd('(')) => {
                let node = AstNode::parse_expr(lexer);
                match lexer.cursor_next()? {
                    Some(LexerToken::Kwd(')')) => node,
                    Some(_) => Err(ParsingError::FatalError(
                        FatalError::ExpectedClosingParenthesis,
                    )),
                    None => Err(ParsingError::IncompleteAstError),
                }
            }
            Some(_) => Err(ParsingError::FatalError(
                FatalError::ExpectedPrimaryExpression,
            )),
            None => Err(ParsingError::IncompleteAstError),
        }
    }

    fn parse_primary<L: LexerTrait>(lexer: &mut L) -> Result<Self, ParsingError> {
        debug!("parse_primary");
        let next = lexer.cursor_next()?.clone();
        AstNode::parse_primary_with_token(lexer, next)
    }

    fn parse_expr_with_token<L: LexerTrait>(
        lexer: &mut L,
        token: LexerToken,
    ) -> Result<Self, ParsingError> {
        debug!("parse_expr_with_token");
        AstNode::parse_expr_with_opt_token(lexer, Some(token))
    }

    fn parse_expr_with_opt_token<L: LexerTrait>(
        lexer: &mut L,
        token: Option<LexerToken>,
    ) -> Result<Self, ParsingError> {
        debug!("parse_expr_with_opt_token");
        let lhs = AstNode::parse_primary_with_token(lexer, token)?;
        debug!("lhs: {:?}", lhs);
        match lexer.peek()? {
            Some(LexerToken::Kwd(c)) => {
                debug!("Next token is a keyword with char: {}", c);
                match precedence(*c) {
                    Some(val) => {
                        debug!(
                            "This char has a precedence ({}), recursing into the expression...",
                            val
                        );
                        let c = *c;

                        // Important!
                        // We consume the token if it's a binary operator, otherwise we let it be parsed for the next step.
                        // This could be a semi column, a comma, a parenthesis etc.
                        lexer.cursor_next()?;
                        AstNode::parse_expr_rec_with_op(lexer, lhs, c)
                    }
                    None => Ok(lhs),
                }
            }
            _ => return Ok(lhs),
        }
    }

    fn parse_expr<L: LexerTrait>(lexer: &mut L) -> Result<Self, ParsingError> {
        debug!("parse_expr");
        let token = lexer.cursor_next()?.clone();
        AstNode::parse_expr_with_opt_token(lexer, token)
    }

    fn parse_expr_rec_with_op<L: LexerTrait>(
        lexer: &mut L,
        lhs: AstNode,
        op: char,
    ) -> Result<Self, ParsingError> {
        debug!("parsed operator: {}", op);
        let rhs = AstNode::parse_primary(lexer)?;
        debug!("parsed rhs: {:?}", rhs);
        match lexer.peek()? {
            Some(LexerToken::Kwd(c)) => {
                Ok(match precedence(*c) {
                    Some(prec_next) => {
                        let should_nomnom = prec_next > precedence(op).unwrap();
                        // keep nomnom'ing if precedence is higher e.g. a + b * c
                        // then our new rhs is the recursively parsed b * c
                        if should_nomnom {
                            let rhs = AstNode::parse_expr_rec(lexer, rhs)?;
                            AstNode::Binary(op, lhs.into(), rhs.into())
                        }
                        // otherwise; e.g. a * b + c,
                        // we replace the lhs with the already parsed binary expr <=> lhs op rhs,
                        // and we parse another rhs
                        else {
                            let lhs = AstNode::Binary(op, lhs.into(), rhs.into());
                            AstNode::parse_expr_rec(lexer, lhs)?
                        }
                    }

                    None => AstNode::Binary(op, lhs.into(), rhs.into()),
                })
            }
            _ => Ok(AstNode::Binary(op, lhs.into(), rhs.into())),
        }
    }

    fn parse_expr_rec<L: LexerTrait>(lexer: &mut L, lhs: AstNode) -> Result<Self, ParsingError> {
        debug!("parse_expr_rec");
        let prev_op = AstNode::parse_raw_operator(lexer)?;
        AstNode::parse_expr_rec_with_op(lexer, lhs, prev_op)
    }

    fn parse_prototype<L: LexerTrait>(lexer: &mut L) -> Result<FnProto, ParsingError> {
        debug!("parse_prototype");
        let fn_name = AstNode::parse_raw_ident(lexer)?;
        debug!("function name: {}", fn_name);
        let fn_args = AstNode::parse_prototype_args(lexer)?;
        debug!("function args: {:?}", fn_args);
        Ok(FnProto(fn_name, fn_args))
    }

    fn parse_prototype_args<L: LexerTrait>(lexer: &mut L) -> Result<Vec<String>, ParsingError> {
        debug!("parse_prototype_args");
        match lexer.cursor_next()? {
            Some(LexerToken::Kwd('(')) => {}
            Some(_) => {
                return Err(ParsingError::FatalError(
                    FatalError::ExpectedOpeningParenthesis,
                ))
            }
            None => return Err(ParsingError::IncompleteAstError),
        }

        let mut elems = Vec::new();
        loop {
            elems.push(AstNode::parse_raw_ident(lexer)?);

            match lexer.cursor_next()? {
                Some(LexerToken::Kwd(',')) => {}
                Some(LexerToken::Kwd(')')) => return Ok(elems),
                // expected comma/parenthesis after expression
                Some(_) => {
                    return Err(ParsingError::FatalError(
                        FatalError::ExpectedCommaOrClosingParenthesis,
                    ))
                }
                None => return Err(ParsingError::IncompleteAstError),
            }
        }
    }

    fn parse_definition<L: LexerTrait>(lexer: &mut L) -> Result<Self, ParsingError> {
        debug!("parse_definition");
        Ok(AstNode::FnDef(
            AstNode::parse_prototype(lexer)?,
            AstNode::parse_expr(lexer)?.into(),
        ))
    }

    fn parse_extern<L: LexerTrait>(lexer: &mut L) -> Result<Self, ParsingError> {
        debug!("parse_extern");
        Ok(AstNode::FnDec(AstNode::parse_prototype(lexer)?))
    }

    fn parse_toplevel<L: LexerTrait>(
        lexer: &mut L,
        token: LexerToken,
    ) -> Result<Self, ParsingError> {
        debug!("parse_toplevel");
        Ok(AstNode::FnDef(
            FnProto("".to_owned(), Vec::new()),
            AstNode::parse_expr_with_token(lexer, token)?.into(),
        ))
    }
}

#[cfg(test)]
mod test {
    use super::{AstNode, FnProto};
    use crate::lexer::Lexer;

    #[test]
    fn parse_variable() {
        let var = "var".to_owned();
        let ast = AstNode::try_all_from_str(&var).unwrap();
        let expected = AstNode::Ident(var);
        let parsed = ast.first().unwrap();

        assert_eq!(ast.len(), 1);
        assert_eq!(parsed, &expected.as_top_level());
    }

    #[test]
    fn parse_number() {
        let var = 1.123;
        let ast = AstNode::try_all_from_str(&var.to_string()).unwrap();
        let expected = AstNode::Number(var);
        let parsed = ast.first().unwrap();

        assert_eq!(ast.len(), 1);
        assert_eq!(parsed, &expected.as_top_level());
    }

    #[test]
    fn parse_def1() {
        let var = "def foo(x, y) x+foo(y, 4.0);";
        let ast = AstNode::try_all_from_str(&var.to_string()).unwrap();

        assert_eq!(ast.len(), 1);
        match ast.first() {
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
        let ast = AstNode::try_all_from_str(&var.to_string()).unwrap();

        assert_eq!(ast.len(), 1);
        match ast.first() {
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
        let var = "extern sin(a);";
        let ast = AstNode::try_all_from_str(&var.to_string()).unwrap();

        assert_eq!(ast.len(), 1);
        match ast.first() {
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
        let var = "def foo(x, y, z) x+y*z; y;";
        let ast = AstNode::try_all_from_str(&var.to_string()).unwrap();

        assert_eq!(ast.len(), 2);
        match ast.first() {
            Some(AstNode::FnDef(FnProto(fn_name, args), _)) => {
                assert_eq!(fn_name, "foo");
                assert_eq!(args.len(), 3);
                assert_eq!(args[0], "x");
                assert_eq!(args[1], "y");
                assert_eq!(args[2], "z");
            }
            _ => panic!("Wrong node type :("),
        }

        assert_eq!(ast[1], AstNode::Ident("y".to_owned()).as_top_level());
    }

    #[test]
    fn parse_toplevel_expr() {
        let var = "x+y\n;z";
        let ast = AstNode::try_all_from_str(&var.to_string()).unwrap();

        assert_eq!(ast.len(), 2);
        assert_eq!(
            ast[0],
            AstNode::Binary(
                '+',
                AstNode::Ident("x".to_owned()).into(),
                AstNode::Ident("y".to_owned()).into()
            )
            .as_top_level()
        );
    }
}
