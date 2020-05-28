use log::debug;
use std::io::BufRead;
use std::ops::{Generator, GeneratorState};
use std::pin::Pin;

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Def,
    Extern,
    Ident(String),
    Number(f64),
    Kwd(char),
}

pub struct Lexer<'a, R: BufRead> {
    input: &'a mut R,
    toparse_buf: String,
    parsed_buf: Vec<Option<Token>>,
}

fn is_ident_accepted(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

/// Note that we NEED to handle keywords here if we don't want to backtrack during parsing,
/// e.g. extern_asd is properly parsed here as 'extern_asd', but with the naive tag
/// version, we sould parse it as extern + _asd
/// That is unless we check if there are whitespaces, but then we never when those should
/// actually be trimmed...
/// TODO: allow digit WITHIN the ident
fn take_ident(s: &str) -> nom::IResult<&str, Token> {
    nom::bytes::complete::take_while1(is_ident_accepted)(s).map(|(reminder, ident)| {
        (
            reminder,
            match ident {
                "extern" => Token::Extern,
                "def" => Token::Def,
                s => Token::Ident(s.into()),
            },
        )
    })
}

fn take_char(s: &str) -> nom::IResult<&str, Token> {
    nom::bytes::complete::take(1usize)(s)
        .map(|(reminder, chr)| (reminder, Token::Kwd(chr.chars().next().unwrap())))
}

fn take_double(s: &str) -> nom::IResult<&str, Token> {
    match nom::number::complete::double(s) {
        Ok((reminder, val)) => {
            if val.is_finite() {
                nom::IResult::Ok((reminder, Token::Number(val)))
            } else {
                nom::IResult::Err(nom::Err::Error((s, nom::error::ErrorKind::Float)))
            }
        }
        Err(e) => nom::IResult::Err(e),
    }
}

fn parse_token(s: &str) -> nom::IResult<&str, Token> {
    nom::branch::alt((take_ident, take_double, take_char))(s)
}

impl<'a, R: BufRead> Lexer<'a, R> {
    pub fn new(input: &'a mut R) -> Self {
        Lexer {
            input,
            toparse_buf: String::new(),
            parsed_buf: Vec::new(),
        }
    }

    fn are_leftovers_trivial(&self) -> bool {
        self.toparse_buf.is_empty() || self.toparse_buf.trim_start().is_empty()
    }

    pub fn token(&mut self) -> Result<Option<Token>, ()> {
        if self.parsed_buf.is_empty() {
            self.next_token()
        } else {
            Ok(self.parsed_buf.remove(0))
        }
    }

    pub fn peek_cur(&mut self) -> Result<&Option<Token>, ()> {
        self.peek_nth(0)
    }

    pub fn peek_next(&mut self) -> Result<&Option<Token>, ()> {
        self.peek_nth(1)
    }

    pub fn peek_nth(&mut self, n: usize) -> Result<&Option<Token>, ()> {
        while self.parsed_buf.len() < n {
            let t = self.next_token()?;
            self.parsed_buf.push(t);
        }

        Ok(self.parsed_buf.get(n).unwrap())
    }

    fn next_token(&mut self) -> Result<Option<Token>, ()> {
        debug!("Trying to parse: '{}'", self.toparse_buf);

        match parse_token(self.toparse_buf.trim_start()) {
            // Could parse data from the previously retrieved line
            Ok((leftovers, result)) => {
                debug!("Parsing succeeded: {:?}", result);
                self.toparse_buf = leftovers.into();
                return Ok(Some(result));
            }
            // Line is not complete apparently, grabbing a new one
            Err(nom::Err::Error(_)) => {
                let mut line = String::new();
                match self.input.read_line(&mut line) {
                    Ok(0) => {
                        if self.are_leftovers_trivial() {
                            // We may have trailing ws but we just ignore those
                            debug!(
                                "Nothing left to read, and nothing left to parse - done lexing!"
                            );
                            return Ok(None);
                        } else {
                            // Otherwise, since we failed to parse the leftovers, and we reached EOF, that means
                            // the last token is an error
                            debug!("Nothing left to read but buffer is not empty; error :(");
                            return Err(());
                        }
                    }
                    Ok(_) => {}
                    Err(_) => {
                        // Error reading another line - client code's problem
                        debug!("Could not read line from the BufRead");
                        return Err(());
                    }
                }

                // appending the new bytes to the 'leftovers' before trying to parse again
                self.toparse_buf += &line;
                debug!("New data was read into the buffer; next iteration!");
            }

            // we work with complete-versions, so this should never go through
            Err(nom::Err::Incomplete(_)) => unreachable!(),
            // note sure when this could actually occur :<
            Err(nom::Err::Failure(_)) => unreachable!(),
        }

        // hopefully it's gonna be tail-recursion optimized 😁
        self.next_token()
    }

    pub fn into_iter(self) -> GeneratorIteratorAdapter<Self> {
        GeneratorIteratorAdapter::new(self)
    }
}

impl<'a, R: BufRead> Generator for Lexer<'a, R> {
    type Yield = Result<Token, ()>;
    type Return = ();
    fn resume(self: Pin<&mut Self>, _: ()) -> GeneratorState<Self::Yield, Self::Return> {
        match Pin::into_inner(self).token() {
            Ok(Some(t)) => GeneratorState::Yielded(Ok(t)),
            Err(e) => GeneratorState::Yielded(Err(e)),
            Ok(None) => GeneratorState::Complete(()),
        }
    }
}

pub struct GeneratorIteratorAdapter<G>(Pin<Box<G>>);
impl<G> GeneratorIteratorAdapter<G>
where
    G: Generator<Return = ()>,
{
    pub fn new(gen: G) -> Self {
        Self(Box::pin(gen))
    }
}

impl<G> Iterator for GeneratorIteratorAdapter<G>
where
    G: Generator<Return = ()>,
{
    type Item = G::Yield;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.as_mut().resume(()) {
            GeneratorState::Yielded(x) => Some(x),
            GeneratorState::Complete(_) => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_def_ok() {
        let defs = vec!["def", "\tdef", "\t\tdef", "\t     \tdef\t"];

        for def in defs {
            let mut s = def.as_bytes();
            let mut lexer = Lexer::new(&mut s);
            assert_eq!(lexer.next_token().unwrap().unwrap(), Token::Def);
            assert_eq!(lexer.next_token(), Ok(None));
        }
    }

    #[test]
    fn parse_extern_ok() {
        let externs = vec!["extern", "\textern", "\t\textern", "\t     \textern\t"];

        for extern_ in externs {
            let mut s = extern_.as_bytes();
            let mut lexer = Lexer::new(&mut s);
            assert_eq!(lexer.next_token().unwrap().unwrap(), Token::Extern);
            assert_eq!(lexer.next_token(), Ok(None));
        }
    }

    #[test]
    fn parse_f64_ok() {
        //env_logger::init();
        let floats = vec![1.0, -2.0, 1e245, -4.1554e-1, 90e-90];

        for f in floats {
            let s = f.to_string();
            let mut sb = s.as_bytes();
            let mut lexer = Lexer::new(&mut sb);
            debug!("OK{}", s);
            match lexer.next_token().unwrap().unwrap() {
                Token::Number(val) => {
                    assert_eq!(val, f);
                }
                _ => unreachable!(),
            }
            assert_eq!(lexer.next_token(), Ok(None));
        }
    }

    #[test]
    fn parse_f64_nok() {
        //env_logger::init();
        let floats = vec![std::f64::NAN, std::f64::INFINITY, std::f64::NEG_INFINITY];

        for f in floats {
            let s = f.to_string();
            let mut sb = s.as_bytes();
            let mut lexer = Lexer::new(&mut sb);
            debug!("OK{}", s);
            assert!(!matches!(
                lexer.next_token().unwrap().unwrap(),
                Token::Number(_)
            ));
        }
    }

    #[test]
    fn parse_ident_ok() {
        let idents = vec![
            "qwe",
            "\t\n  \n QWQWEASD \t \t \n",
            "z",
            "extern_asdb",
            "_def",
            "NaNLol",
            "inf_ormatic",
        ];

        for i in idents {
            let mut s = i.as_bytes();
            let mut lexer = Lexer::new(&mut s);
            assert_eq!(
                lexer.next_token().unwrap().unwrap(),
                Token::Ident(i.trim().to_owned())
            );
            assert_eq!(lexer.next_token(), Ok(None));
        }
    }

    #[test]
    fn parse_kwd_ok() {
        let kwds = vec!["+", "-", "("];

        for k in kwds {
            let mut s = k.as_bytes();
            let mut lexer = Lexer::new(&mut s);
            assert_eq!(
                lexer.next_token().unwrap().unwrap(),
                Token::Kwd(k.chars().next().unwrap())
            );
            assert_eq!(lexer.next_token(), Ok(None));
        }
    }
}
