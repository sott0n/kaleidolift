use anyhow::{anyhow, Result};
use std::io::{Bytes, Read};
use std::iter::Peekable;

#[derive(Debug, PartialEq)]
pub enum Token {
    // Primary
    Number(f64),

    // Operations
    Plus,

    // Other
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

    pub fn next_token(&mut self) -> Result<Token> {
        if let Some(&Ok(byte)) = self.bytes.peek() {
            return match byte {
                b' ' | b'\n' | b'\r' | b'\t' => {
                    self.bytes.next();
                    self.next_token()
                }
                b'0'..=b'9' | b'.' => self.number(),
                _ => {
                    self.bytes.next();
                    let token = match byte {
                        b'+' => Token::Plus,
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
}
