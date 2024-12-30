mod grammar;
mod interpreter;
mod lexical_error;
mod parser;
mod scanner;
mod token;

use std::env::args;
use std::io::Write;
use std::process::exit;
use std::{fs, io};

use interpreter::Interpreter;
use interpreter::InterpreterError;

fn main() {
    let arguments: Vec<String> = args().collect();
    if arguments.len() > 2 {
        println!("Usage: rlox [script]");
        exit(64);
    } else {
        let mut interpreter = Interpreter;
        let (lex_parse_errors, execution_errors) = if arguments.len() == 2 {
            run_file(&mut interpreter, &arguments[1])
        } else {
            prompt(&mut interpreter)
        };
        let exit_code = if lex_parse_errors > 0 {
            65
        } else if execution_errors > 0 {
            70
        } else {
            0
        };
        exit(exit_code);
    }
}

fn run_file(interpreter: &mut Interpreter, path: &str) -> (usize, usize) {
    let source =
        fs::read_to_string(path).unwrap_or_else(|_| panic!("Unable to read file at: {}", path));
    let result = interpreter.run(&source);
    report(result)
}

fn prompt(interpreter: &mut Interpreter) -> (usize, usize) {
    let mut lex_parse_errors = 0;
    let mut execution_errors = 0;

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
        let (line_lex_parse_errors, line_execution_errors) = report(result);
        lex_parse_errors += line_lex_parse_errors;
        execution_errors += line_execution_errors;
        stdout.write_all(b"> ").expect("Unable to write to stdout");
        stdout.flush().expect("Unable to flush stdout");
        buffer.clear();
    }

    (lex_parse_errors, execution_errors)
}

fn report(result: Result<(), InterpreterError>) -> (usize, usize) {
    match result {
        Err(error) => match error {
            InterpreterError::Lex(errors) => {
                let error_count = errors.len();
                for error in errors {
                    eprintln!("[line {}] Error: {}", error.line, error.message);
                }
                (error_count, 0)
            }
            InterpreterError::Parse(parse_error) => {
                eprintln!("Parse error: {:?}", parse_error);
                (1, 0)
            }
            InterpreterError::Execution(execution_error) => {
                eprintln!("Execution error: {:?}", execution_error);
                (0, 1)
            }
        },
        _ => (0, 0),
    }
}
