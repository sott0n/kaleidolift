use anyhow::{anyhow, Result};
use std::io::{Bytes, Read};
use std::iter::Peekable;

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    // Primary
    Number(f64),
    Identifier(String),

    // Commands
    Def,
    Extern,

    // Operations
    Plus,
    Minus,
    Star,
    Div,
    If,
    Then,
    Else,
    LessThan,
    MoreThan,
    Assign,
    While,

    // Other
    Semicolon,
    Comma,
    OpenParen,
    CloseParen,
    OpenBlock,
    CloseBlock,

    Eof,
}

pub struct Lexer<R: Read> {
    bytes: Peekable<Bytes<R>>,
}

impl<R: Read> Lexer<R> {
    pub fn new(reader: R) -> Self {
        Self {
            bytes: reader.bytes().peekable(),
        }
    }

    pub fn tokenize(&mut self) -> Result<Vec<Token>> {
        let mut tokens: Vec<Token> = vec![];
        loop {
            let token = self.next_token()?;
            if token == Token::Eof {
                tokens.push(token);
                break;
            };
            tokens.push(token);
        }
        Ok(tokens)
    }

    fn next_token(&mut self) -> Result<Token> {
        if let Some(&Ok(byte)) = self.bytes.peek() {
            return match byte {
                b' ' | b'\n' | b'\r' | b'\t' => {
                    self.bytes.next();
                    self.next_token()
                }
                b'a'..=b'z' | b'A'..=b'Z' => self.identifier(),
                b'0'..=b'9' | b'.' => self.number(),
                b'#' => self.comment(),
                _ => {
                    self.bytes.next();
                    let token = match byte {
                        b'+' => Token::Plus,
                        b'-' => Token::Minus,
                        b'*' => Token::Star,
                        b'/' => Token::Div,
                        b'<' => Token::LessThan,
                        b'>' => Token::MoreThan,
                        b';' => Token::Semicolon,
                        b',' => Token::Comma,
                        b'(' => Token::OpenParen,
                        b')' => Token::CloseParen,
                        b'{' => Token::OpenBlock,
                        b'}' => Token::CloseBlock,
                        b'=' => Token::Assign,
                        _ => return Err(anyhow!(format!("Unknown charactor: {}", byte))),
                    };
                    Ok(token)
                }
            };
        }

        match self.bytes.next() {
            Some(Ok(_)) => unreachable!(),
            Some(Err(e)) => Err(anyhow!(e)),
            None => Ok(Token::Eof),
        }
    }

    fn number(&mut self) -> Result<Token> {
        let integral = self.digits()?;
        if let Some('.') = self.peek_char()? {
            self.bytes.next();
            let decimal = self.digits()?;
            Ok(Token::Number(format!("{}.{}", integral, decimal).parse()?))
        } else {
            Ok(Token::Number(integral.parse()?))
        }
    }

    fn digits(&mut self) -> Result<String> {
        let mut buf = String::new();
        loop {
            if let Some(c) = self.peek_char()? {
                if c.is_numeric() {
                    self.bytes.next();
                    buf.push(c);
                    continue;
                }
            }
            break;
        }
        Ok(buf)
    }

    fn peek_char(&mut self) -> Result<Option<char>> {
        if let Some(&Ok(byte)) = self.bytes.peek() {
            return Ok(Some(byte as char));
        }

        match self.bytes.next() {
            Some(Ok(_)) => unreachable!(),
            Some(Err(e)) => Err(anyhow!(e)),
            None => Ok(None),
        }
    }

    fn identifier(&mut self) -> Result<Token> {
        let mut ident = String::new();
        loop {
            if let Some(c) = self.peek_char()? {
                if c.is_ascii_alphanumeric() {
                    self.bytes.next();
                    ident.push(c);
                    continue;
                }
            }
            break;
        }

        let token = match ident.as_str() {
            "def" => Token::Def,
            "extern" => Token::Extern,
            "if" => Token::If,
            "then" => Token::Then,
            "else" => Token::Else,
            "while" => Token::While,
            _ => Token::Identifier(ident),
        };
        Ok(token)
    }

    fn comment(&mut self) -> Result<Token> {
        loop {
            if let Some(c) = self.peek_char()? {
                self.bytes.next();
                if c == '\n' {
                    break;
                }
            } else {
                return Ok(Token::Eof);
            }
        }
        self.next_token()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::fs::File;

    #[test]
    fn test_arithmetic() {
        let f = File::open("tests/test_1.kal").unwrap();
        let mut lexer = Lexer::new(f);
        let tokens = lexer.tokenize().unwrap();

        assert_eq!(
            tokens,
            vec![
                Token::Def,
                Token::Identifier("compute".to_string()),
                Token::OpenParen,
                Token::CloseParen,
                Token::OpenBlock,
                Token::Number(9999.0),
                Token::Plus,
                Token::OpenParen,
                Token::Number(1.0),
                Token::Plus,
                Token::Number(22.0),
                Token::CloseParen,
                Token::Minus,
                Token::Number(1.0),
                Token::Star,
                Token::Number(3.0),
                Token::Div,
                Token::Number(2.0),
                Token::CloseBlock,
                Token::Identifier("compute".to_string()),
                Token::OpenParen,
                Token::CloseParen,
                Token::Eof
            ]
        );
    }

    #[test]
    fn test_less_more_than() {
        let f = File::open("tests/test_2.kal").unwrap();
        let mut lexer = Lexer::new(f);
        let tokens = lexer.tokenize().unwrap();

        assert_eq!(
            tokens,
            vec![
                Token::Def,
                Token::Identifier("than".to_string()),
                Token::OpenParen,
                Token::Identifier("x".to_string()),
                Token::CloseParen,
                Token::OpenBlock,
                Token::If,
                Token::Identifier("x".to_string()),
                Token::LessThan,
                Token::Number(20.0),
                Token::OpenBlock,
                Token::Number(1.0),
                Token::CloseBlock,
                Token::If,
                Token::Identifier("x".to_string()),
                Token::MoreThan,
                Token::Number(30.0),
                Token::OpenBlock,
                Token::Number(2.0),
                Token::CloseBlock,
                Token::Else,
                Token::OpenBlock,
                Token::Number(3.0),
                Token::CloseBlock,
                Token::CloseBlock,
                Token::Identifier("than".to_string()),
                Token::OpenParen,
                Token::Number(10.0),
                Token::CloseParen,
                Token::Semicolon,
                Token::Identifier("than".to_string()),
                Token::OpenParen,
                Token::Number(40.0),
                Token::CloseParen,
                Token::Semicolon,
                Token::Identifier("than".to_string()),
                Token::OpenParen,
                Token::Number(30.0),
                Token::CloseParen,
                Token::Semicolon,
                Token::Eof
            ]
        );
    }

    #[test]
    fn test_extern() {
        let f = File::open("tests/test_3.kal").unwrap();
        let mut lexer = Lexer::new(f);
        let tokens = lexer.tokenize().unwrap();

        assert_eq!(
            tokens,
            vec![
                Token::Extern,
                Token::Identifier("hello".to_string()),
                Token::OpenParen,
                Token::CloseParen,
                Token::Semicolon,
                Token::Def,
                Token::Identifier("world".to_string()),
                Token::OpenParen,
                Token::CloseParen,
                Token::OpenBlock,
                Token::Number(10.0),
                Token::CloseBlock,
                Token::Identifier("hello".to_string()),
                Token::OpenParen,
                Token::CloseParen,
                Token::Semicolon,
                Token::Identifier("world".to_string()),
                Token::OpenParen,
                Token::CloseParen,
                Token::Semicolon,
                Token::Eof
            ]
        );
    }
}
