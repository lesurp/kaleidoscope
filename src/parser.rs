use crate::lexer::{GeneratorIteratorAdapter, Lexer, Token};

pub struct FnProto(String, Vec<String>);
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

impl AstNode {
    pub fn try_from_lexer<R: std::io::BufRead>(lexer: &mut Lexer<R>) -> Result<Self, ()> {
        loop {
            let token = lexer.token()?;
            //match token {
            //Token::
            //}
        }
        Err(())
    }

    fn parse_number<R: std::io::BufRead>(_: &mut Lexer<R>, t: f64) -> Result<Self, ()> {
        Ok(AstNode::Number(t))
    }

    fn parse_raw_ident<R: std::io::BufRead>(lexer: &mut Lexer<R>) -> Result<String, ()> {
        match lexer.token()? {
            Some(Token::Ident(i)) => Ok(i),
            _ => Err(()),
        }
    }

    fn parse_call_parameters<R: std::io::BufRead>(lexer: &mut Lexer<R>) -> Result<Vec<Self>, ()> {
        let mut elems = Vec::new();
        loop {
            elems.push(AstNode::parse_primary(lexer)?);

            match lexer.token()? {
                Some(Token::Kwd(',')) => {}
                Some(Token::Kwd(')')) => return Ok(elems),
                // expected comma/parenthesis after expression
                _ => return Err(()),
            }
        }
    }

    fn parse_primary<R: std::io::BufRead>(lexer: &mut Lexer<R>) -> Result<Self, ()> {
        match lexer.token()? {
            Some(Token::Number(n)) => AstNode::parse_number(lexer, n),
            Some(Token::Ident(i)) => {
                if matches!(lexer.peek_next()?, Some(Token::Kwd('('))) {
                    lexer.token()?;
                    Ok(AstNode::Call(i, AstNode::parse_call_parameters(lexer)?))
                } else {
                    Ok(AstNode::Ident(i))
                }
            }
            Some(Token::Kwd('(')) => {
                let node = AstNode::parse_expr(lexer);
                if matches!(lexer.token()?, Some(Token::Kwd(')'))) {
                    node
                } else {
                    // expecting closnig ')'
                    Err(())
                }
            }
            _ => Err(()),
        }
    }

    fn parse_expr<R: std::io::BufRead>(lexer: &mut Lexer<R>) -> Result<Self, ()> {
        let lhs = AstNode::parse_primary(lexer)?;
        match *lexer.peek_next()? {
            Some(Token::Kwd(c)) => match precedence(c) {
                Some(_) => {
                    let _ = lexer.token()?;
                    AstNode::parse_expr_rec(lexer, lhs, c)
                }
                None => Ok(lhs),
            },
            _ => return Ok(lhs),
        }
    }

    fn parse_expr_rec<R: std::io::BufRead>(
        lexer: &mut Lexer<R>,
        lhs: AstNode,
        op: char,
    ) -> Result<Self, ()> {
        let rhs = AstNode::parse_primary(lexer)?;
        match *lexer.peek_next()? {
            Some(Token::Kwd(c)) => {
                Ok(match precedence(c) {
                    Some(prec_next) => {
                        lexer.token()?;
                        let should_nomnom = prec_next > precedence(op).unwrap();
                        // keep nomnom'ing if precedence is higher e.g. a + b * c
                        // then our new rhs is the recursively parsed b * c
                        if should_nomnom {
                            let rhs = AstNode::parse_expr_rec(lexer, rhs, c)?;
                            AstNode::Binary(op, lhs.into(), rhs.into())
                        }
                        // otherwise; e.g. a * b + c,
                        // we replace the lhs with the already parsed binary expr <=> lhs op rhs,
                        // and we parse another rhs
                        else {
                            let lhs = AstNode::Binary(op, lhs.into(), rhs.into());
                            AstNode::parse_expr_rec(lexer, lhs, c)?
                        }
                    }

                    None => AstNode::Binary(op, lhs.into(), rhs.into()),
                })
            }
            _ => return Ok(lhs),
        }
    }

    fn parse_prototype<R: std::io::BufRead>(lexer: &mut Lexer<R>) -> Result<FnProto, ()> {
        Ok(FnProto(
            AstNode::parse_raw_ident(lexer)?,
            AstNode::parse_prototype_args(lexer)?,
        ))
    }

    fn parse_prototype_args<R: std::io::BufRead>(lexer: &mut Lexer<R>) -> Result<Vec<String>, ()> {
        if !matches!(lexer.token()?, Some(Token::Kwd('('))) {
            // expected (
            return Err(());
        }

        let mut elems = Vec::new();
        loop {
            elems.push(AstNode::parse_raw_ident(lexer)?);

            match lexer.token()? {
                Some(Token::Kwd(',')) => {}
                Some(Token::Kwd(')')) => return Ok(elems),
                // expected comma/parenthesis after expression
                _ => return Err(()),
            }
        }
    }

    fn parse_definition<R: std::io::BufRead>(lexer: &mut Lexer<R>) -> Result<Self, ()> {
        Ok(AstNode::FnDef(
            AstNode::parse_prototype(lexer)?,
            AstNode::parse_expr(lexer)?.into(),
        ))
    }

    fn parse_extern<R: std::io::BufRead>(lexer: &mut Lexer<R>) -> Result<Self, ()> {
        Ok(AstNode::FnDec(AstNode::parse_prototype(lexer)?))
    }

    fn parse_toplevel<R: std::io::BufRead>(lexer: &mut Lexer<R>) -> Result<Self, ()> {
        Ok(AstNode::FnDef(
            FnProto("".to_owned(), Vec::new()),
            AstNode::parse_expr(lexer)?.into(),
        ))
    }
}

//impl Into<Box<AstNode>> for AstNode {
//fn into(self) -> Self {
////Box::new(self)
//}
//}
