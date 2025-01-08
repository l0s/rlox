mod environment;
mod grammar;
mod interpreter;
mod lexical_error;
mod parser;
mod scanner;
mod side_effects;
mod token;

use std::cell::RefCell;
use std::env::args;
use std::io::Write;
use std::process::exit;
use std::rc::Rc;
use std::{fs, io};

use crate::parser::ParseError;
use crate::side_effects::{SideEffects, StandardSideEffects};
use interpreter::Interpreter;
use interpreter::InterpreterError;

fn main() {
    let arguments: Vec<String> = args().collect();
    if arguments.len() > 2 {
        println!("Usage: rlox [script]");
        exit(64);
    } else {
        let side_effects = Rc::new(RefCell::new(StandardSideEffects));
        let mut interpreter = Interpreter::new(side_effects.clone());
        let (lex_parse_errors, execution_errors) = if arguments.len() == 2 {
            run_file(&mut interpreter, &arguments[1])
        } else {
            prompt(&mut interpreter, side_effects.clone())
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

fn run_file(interpreter: &mut Interpreter<StandardSideEffects>, path: &str) -> (usize, usize) {
    let source =
        fs::read_to_string(path).unwrap_or_else(|_| panic!("Unable to read file at: {}", path));
    let result = interpreter.run(&source);
    report(result)
}

fn prompt<S: SideEffects>(
    interpreter: &mut Interpreter<S>,
    side_effects: Rc<RefCell<S>>,
) -> (usize, usize) {
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
        let (line_lex_parse_errors, line_execution_errors) =
            interpret_line(interpreter, side_effects.clone(), &buffer);
        lex_parse_errors += line_lex_parse_errors;
        execution_errors += line_execution_errors;
        stdout.write_all(b"> ").expect("Unable to write to stdout");
        stdout.flush().expect("Unable to flush stdout");
        buffer.clear();
    }

    (lex_parse_errors, execution_errors)
}

/// For use in REPL only: Execute a single line. Statements will be executed as expected.
/// Expressions will be evaluated and their result outputted as if there were an implicit print
/// statement.
///
/// Returns:
/// - the number of lexical or parsing errors
/// - the number or execution errors
fn interpret_line<S: SideEffects>(
    interpreter: &mut Interpreter<S>,
    side_effects: Rc<RefCell<S>>,
    buffer: &str,
) -> (usize, usize) {
    match interpreter.run(buffer) {
        Ok(_) => (0, 0),
        Err(interpreter_error) => match interpreter_error {
            InterpreterError::Parse(parse_error) => match parse_error {
                ParseError::UnterminatedStatement(expression) => match expression {
                    None => report(Err(InterpreterError::Parse(
                        ParseError::UnterminatedStatement(expression),
                    ))),
                    Some(expression) => match interpreter.evaluate(&expression) {
                        Ok(result) => {
                            side_effects.borrow_mut().println(&format!("{}", result));
                            (0, 0)
                        }
                        Err(error) => {
                            eprintln!("Evaluation error: {:?}", error);
                            (0, 1)
                        }
                    },
                },
                other => report(Err(InterpreterError::Parse(other))),
            },
            other => report(Err(other)),
        },
    }
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

#[cfg(test)]
mod tests {
    use super::interpret_line;
    use crate::interpreter::Interpreter;
    use crate::side_effects::SideEffects;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn can_interpret_statement() {
        // given
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let mut interpreter = Interpreter::new(side_effects.clone());
        let source = "print 1 + 2;\n"; // FIXME allow w/o newline

        // when
        let (lex_parse_errors, execution_errors) =
            interpret_line(&mut interpreter, side_effects.clone(), source);

        // then
        assert_eq!(lex_parse_errors, 0);
        assert_eq!(execution_errors, 0);
        assert_eq!(side_effects.borrow().lines.len(), 1);
        assert_eq!(side_effects.borrow().lines[0], "3e0");
    }

    #[test]
    fn can_interpret_expression() {
        // given
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let mut interpreter = Interpreter::new(side_effects.clone());
        let source = "1 + 2\n"; // FIXME allow w/o newline

        // when
        let (lex_parse_errors, execution_errors) =
            interpret_line(&mut interpreter, side_effects.clone(), source);

        // then
        assert_eq!(lex_parse_errors, 0);
        assert_eq!(execution_errors, 0);
        assert_eq!(side_effects.borrow().lines.len(), 1);
        assert_eq!(side_effects.borrow().lines[0], "3e0");
    }

    #[test]
    fn can_interpret_expression_with_side_effects() {
        // given
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let mut interpreter = Interpreter::new(side_effects.clone());
        interpret_line(&mut interpreter, side_effects.clone(), "var a = 1;\n");

        // when
        interpret_line(&mut interpreter, side_effects.clone(), "a = 2\n");
        interpret_line(&mut interpreter, side_effects.clone(), "print a;\n");

        // then
        assert_eq!(side_effects.borrow().lines.len(), 2);
        assert_eq!(side_effects.borrow().lines[0], "2e0");
        assert_eq!(side_effects.borrow().lines[1], "2e0");
    }

    #[derive(Default)]
    struct TestSideEffects {
        lines: Vec<String>,
    }

    impl SideEffects for TestSideEffects {
        fn println(&mut self, text: &str) {
            self.lines.push(text.to_string());
        }
    }
}
