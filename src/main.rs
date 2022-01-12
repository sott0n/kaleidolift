mod ast;
mod codegen;
mod lexer;
mod parser;

use anyhow::{anyhow, Result};
use std::env;
use std::fs::File;

use codegen::Generator;
use lexer::Lexer;
use parser::Parser;

#[derive(PartialEq, Eq)]
struct Commands {
    file: String,
    help: bool,
    token: bool,
    ast: bool,
    clif: bool,
}

fn arg_parse() -> Result<Commands> {
    let mut file = String::from("");
    let mut help = false;
    let mut token = false;
    let mut ast = false;
    let mut clif = false;

    let args: Vec<String> = env::args().collect();
    if args.len() > 1 {
        for arg in args[1..].iter() {
            match arg.as_str() {
                "--help" | "-h" => {
                    help = true;
                    break;
                }
                "--token" | "-t" => {
                    token = true;
                }
                "--ast" | "-a" => {
                    ast = true;
                }
                "--clif" | "-c" => {
                    clif = true;
                }
                _ => {
                    if arg.ends_with(".kal") {
                        file = arg.to_string();
                    } else {
                        return Err(anyhow!(format!(
                            "File '{}' does not end with '.kal'. See --help.",
                            arg
                        )));
                    }
                }
            };
        }
    } else {
        help = true;
    }

    Ok(Commands {
        file,
        help,
        token,
        ast,
        clif,
    })
}

fn help() {
    println!(
        "\
kaleidolift: A toy kaleidoscope language with cranelift backend.

USAGE:
    kaleidolift [COMMANDS] [FILE]

FILE: Given end with 'kal' file, compile using cranelift.

COMMANDS:
    --help   | -h     : Show this help.
    --token  | -t     : Show only tokens from lexer.
    --ast    | -a     : Show only AST from parser.
    --clif   | -c     : Show only Cranelift IR from codegen.
"
    );
}

fn main() -> Result<()> {
    let cmds = arg_parse().unwrap();
    if cmds.help {
        help();
        return Ok(());
    }

    let f = File::open(cmds.file)?;
    let mut lexer = Lexer::new(f);
    let tokens = lexer.tokenize()?;
    if cmds.token {
        println!("{:#?}", tokens);
        return Ok(());
    }

    let mut parser = Parser::new(&tokens);
    let ast = parser.parse()?;
    if cmds.ast {
        println!("{:#?}", ast);
        return Ok(());
    }

    let mut generator = Generator::new(&ast, cmds.clif);
    let result = generator.gen()?;

    println!("{}", result.unwrap());

    Ok(())
}
