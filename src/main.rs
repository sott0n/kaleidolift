mod lexer;

use anyhow::Result;
use lexer::Lexer;
use std::fs::File;

fn main() -> Result<()> {
    let file = File::open("tests/test_1.kal")?;
    let mut lexer = Lexer::new(file);
    let tokens = lexer.tokenize()?;

    println!("{:?}", tokens);
    Ok(())
}
