mod ast;
mod codegen;
mod lexer;
mod parser;

use anyhow::Result;
use std::env;
use std::fs::File;

use codegen::Generator;
use lexer::Lexer;
use parser::Parser;

enum Commands {
    Help,
    File(String),
}

fn arg_parse() -> Commands {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 {
        let cmd: Commands = match args[1].as_str() {
            "--help" | "-h" => Commands::Help,
            _ => Commands::File(args[1].to_string()),
        };
        cmd
    } else {
        Commands::Help
    }
}

fn help() {
    println!(
        "\
kaleidolift: A toy kaleidoscope language with cranelift backend.

USAGE:
    kaleidolift [COMMANDS]

COMMANDS:
    --help | -h     : Show this help.
    [FILE NAME]     : Given file, compile using cranelift.
"
    );
}

fn main() -> Result<()> {
    match arg_parse() {
        Commands::Help => help(),
        Commands::File(f) => {
            let f = File::open(f)?;
            let mut lexer = Lexer::new(f);
            let tokens = lexer.tokenize()?;
            let mut parser = Parser::new(&tokens);
            let ast = parser.parse()?;
            let mut generator = Generator::new(&ast);
            let result = generator.gen()?;

            println!("{}", result.unwrap());
        }
    }
    Ok(())
}
