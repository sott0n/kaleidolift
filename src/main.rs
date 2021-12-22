mod lexer;

use anyhow::Result;
use lexer::{Lexer, Token};
use std::fs::File;

fn main() -> Result<()> {
    let file = File::open("tests/plus.kal")?;
    let mut lexer = Lexer::new(file);
    loop {
        let token = lexer.next_token()?;
        println!("{:?}", token);
        if token == Token::Eof {
            break;
        }
    }
    Ok(())
}
