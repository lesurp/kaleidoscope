use log::debug;
use std::io::BufRead;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexingError {
    IncompleteToken,
    IoError,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LexerToken {
    Def,
    Extern,
    Ident(String),
    Number(f64),
    Kwd(char),
}

pub trait Newliner {
    fn new_line(&self) {}
}

pub struct NoNewline;
impl Newliner for NoNewline {}

pub trait LexerTrait {
    //fn token(&mut self) -> Result<Option<LexerToken>, LexingError>;
    //fn peek(&mut self) -> Result<&Option<LexerToken>, LexingError>;
    fn cursor_next(&mut self) -> Result<&Option<LexerToken>, LexingError>;
    fn peek(&mut self) -> Result<&Option<LexerToken>, LexingError>;
    fn consume(&mut self);
    fn reset(&mut self);
}

pub struct Lexer<'a, R: BufRead, N: Newliner = NoNewline> {
    input: &'a mut R,
    toparse_buf: String,
    newliner: N,
    parsed_buf: Vec<Option<LexerToken>>,
    cursor: Option<usize>,
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
fn take_ident(s: &str) -> nom::IResult<&str, LexerToken> {
    nom::bytes::complete::take_while1(is_ident_accepted)(s).map(|(reminder, ident)| {
        (
            reminder,
            match ident {
                "extern" => LexerToken::Extern,
                "def" => LexerToken::Def,
                s => LexerToken::Ident(s.into()),
            },
        )
    })
}

fn take_kwd(s: &str) -> nom::IResult<&str, LexerToken> {
    nom::character::complete::none_of("0123456789")(s)
        .map(|(reminder, chr)| (reminder, LexerToken::Kwd(chr)))
}

fn take_double(s: &str) -> nom::IResult<&str, LexerToken> {
    match nom::number::complete::double(s) {
        Ok((reminder, val)) => {
            if val.is_finite() {
                nom::IResult::Ok((reminder, LexerToken::Number(val)))
            } else {
                nom::IResult::Err(nom::Err::Error((s, nom::error::ErrorKind::Float)))
            }
        }
        Err(e) => nom::IResult::Err(e),
    }
}

fn parse_token(s: &str) -> nom::IResult<&str, LexerToken> {
    nom::branch::alt((take_ident, take_kwd, take_double))(s)
}

impl<'a, R: BufRead> Lexer<'a, R> {
    pub fn new(input: &'a mut R) -> Self {
        Lexer {
            input,
            toparse_buf: String::new(),
            parsed_buf: Vec::new(),
            newliner: NoNewline,
            cursor: None,
        }
    }
}

impl<'a, R: BufRead, N: Newliner> Lexer<'a, R, N> {
    pub fn with_newliner(input: &'a mut R, newliner: N) -> Self {
        Lexer {
            input,
            toparse_buf: String::new(),
            parsed_buf: Vec::new(),
            newliner,
            cursor: None,
        }
    }

    fn are_leftovers_trivial(&self) -> bool {
        self.toparse_buf.is_empty() || self.toparse_buf.trim_start().is_empty()
    }

    pub fn peek_nth(&mut self, n: usize) -> Result<&Option<LexerToken>, LexingError> {
        while self.parsed_buf.len() < n + 1 {
            let t = self.next_token()?;
            self.parsed_buf.push(t);
        }

        Ok(self.parsed_buf.get(n).unwrap())
    }

    fn next_token(&mut self) -> Result<Option<LexerToken>, LexingError> {
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
                self.newliner.new_line();
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
                            return Err(LexingError::IncompleteToken);
                        }
                    }
                    Ok(_) => {}
                    Err(_) => {
                        // Error reading another line - client code's problem
                        debug!("Could not read line from the BufRead");
                        return Err(LexingError::IoError);
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
}

impl<'a, R: BufRead, N: Newliner> LexerTrait for Lexer<'a, R, N> {
    fn cursor_next(&mut self) -> Result<&Option<LexerToken>, LexingError> {
        let cursor = self.cursor.map_or(0, |cursor| cursor + 1);
        self.cursor = Some(cursor);
        self.peek_nth(cursor)
    }

    fn peek(&mut self) -> Result<&Option<LexerToken>, LexingError> {
        self.peek_nth(self.cursor.map_or(0, |cursor| cursor + 1))
    }

    fn consume(&mut self) {
        let cursor = self
            .cursor
            .expect("Calling consume() on a lexer without actually consuming anything");
        self.parsed_buf.drain(0..cursor + 1);
        self.cursor = None;
    }

    fn reset(&mut self) {
        self.cursor = None;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn lex_def_ok() {
        let defs = vec!["def", "\tdef", "\t\tdef", "\t     \tdef\t"];

        for def in defs {
            let mut s = def.as_bytes();
            let mut lexer = Lexer::new(&mut s);
            assert_eq!(lexer.next_token().unwrap().unwrap(), LexerToken::Def);
            assert_eq!(lexer.next_token(), Ok(None));
        }
    }

    #[test]
    fn lex_extern_ok() {
        let externs = vec!["extern", "\textern", "\t\textern", "\t     \textern\t"];

        for extern_ in externs {
            let mut s = extern_.as_bytes();
            let mut lexer = Lexer::new(&mut s);
            assert_eq!(lexer.next_token().unwrap().unwrap(), LexerToken::Extern);
            assert_eq!(lexer.next_token(), Ok(None));
        }
    }

    #[test]
    fn lex_f64_ok() {
        //env_logger::init();
        let floats = vec![1.0, 2.0, 1e245, 4.1554e-1, 90e-90];

        for f in floats {
            let s = f.to_string();
            let mut sb = s.as_bytes();
            let mut lexer = Lexer::new(&mut sb);
            debug!("OK{}", s);
            match lexer.next_token().unwrap().unwrap() {
                LexerToken::Number(val) => {
                    assert_eq!(val, f);
                }
                _ => unreachable!(),
            }
            assert_eq!(lexer.next_token(), Ok(None));
        }
    }

    #[test]
    fn lex_f64_nok() {
        //env_logger::init();
        let floats = vec![std::f64::NAN, std::f64::INFINITY, std::f64::NEG_INFINITY];

        for f in floats {
            let s = f.to_string();
            let mut sb = s.as_bytes();
            let mut lexer = Lexer::new(&mut sb);
            debug!("OK{}", s);
            assert!(!matches!(
                lexer.next_token().unwrap().unwrap(),
                LexerToken::Number(_)
            ));
        }
    }

    #[test]
    fn lex_ident_ok() {
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
                LexerToken::Ident(i.trim().to_owned())
            );
            assert_eq!(lexer.next_token(), Ok(None));
        }
    }

    #[test]
    fn lex_signed_float_ok() {
        let s = vec!["+123", "-4.3"];

        for s in s {
            let mut sb = s.as_bytes();
            let mut lexer = Lexer::new(&mut sb);
            assert_eq!(
                lexer.next_token().unwrap().unwrap(),
                LexerToken::Kwd(s.chars().next().unwrap())
            );
            assert!(matches!(
                lexer.next_token().unwrap().unwrap(),
                LexerToken::Number(_)
            ));
        }
    }

    #[test]
    fn lex_kwd_ok() {
        let kwds = vec!["+", "-", "("];

        for k in kwds {
            let mut s = k.as_bytes();
            let mut lexer = Lexer::new(&mut s);
            assert_eq!(
                lexer.next_token().unwrap().unwrap(),
                LexerToken::Kwd(k.chars().next().unwrap())
            );
            assert_eq!(lexer.next_token(), Ok(None));
        }
    }
}
