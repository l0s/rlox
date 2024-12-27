mod grammar;
mod interpreter;
mod lexical_error;
mod scanner;
mod token;

use std::env::args;
use std::io::Write;
use std::process::exit;
use std::{fs, io};

use crate::lexical_error::LexicalError;
use crate::token::Token;
use interpreter::Interpreter;

fn main() {
    let arguments: Vec<String> = args().collect();
    if arguments.len() > 2 {
        println!("Usage: rlox [script]");
        exit(64);
    } else {
        let mut interpreter = Interpreter::default();
        if arguments.len() == 2 {
            run_file(&mut interpreter, &arguments[1]);
        } else {
            prompt(&mut interpreter);
        }
        if interpreter.error {
            exit(65);
        }
    }
}

fn run_file(interpreter: &mut Interpreter, path: &str) {
    let source =
        fs::read_to_string(path).unwrap_or_else(|_| panic!("Unable to read file at: {}", path));
    let result = interpreter.run(&source);
    report(result);
}

fn prompt(interpreter: &mut Interpreter) {
    let mut buffer = String::new();
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    stdout.write_all(b"> ").expect("Unable to write to stdout");
    stdout.flush().expect("Unable to flush stdout");
    while let Ok(bytes_read) = stdin.read_line(&mut buffer) {
        if bytes_read == 0 {
            // EOF
            break;
        }
        let result = interpreter.run(&buffer);
        report(result);
        stdout.write_all(b"> ").expect("Unable to write to stdout");
        stdout.flush().expect("Unable to flush stdout");
        buffer.clear();
    }
}

fn report(result: Result<Vec<Token>, Vec<LexicalError>>) {
    match result {
        Ok(tokens) => {
            for token in tokens {
                println!("{:?}", token);
            }
        }
        Err(errors) => {
            for error in errors {
                eprintln!("[line {}] Error: {}", error.line, error.message)
            }
        }
    }
}
