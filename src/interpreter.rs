use crate::grammar::{EvaluationError, EvaluationResult};
use crate::lexical_error::LexicalError;
use crate::parser::{ParseError, Parser};
use crate::scanner::Scanner;
use InterpreterError::{Evaluation, Lex, Parse};

#[derive(Default)]
pub(crate) struct Interpreter {
    /// Indicates that a lexing or parsing error occurred
    pub error: bool,
    /// Indicates that an evaluation error occurred
    pub runtime_error: bool,
}

pub(crate) enum InterpreterError {
    Lex(Vec<LexicalError>),
    Parse(ParseError),
    Evaluation(EvaluationError),
}

impl Interpreter {
    pub fn run(&mut self, source: &str) -> Result<EvaluationResult, InterpreterError> {
        let mut scanner: Scanner = source.into();
        scanner.scan_tokens();
        if !scanner.errors.is_empty() {
            self.error |= true;
            Err(Lex(scanner.errors))
        } else {
            let mut parser: Parser = scanner.tokens.into();

            match parser.parse() {
                Ok(expression) => match expression.evaluate() {
                    Ok(result) => Ok(result),
                    Err(evaluation_error) => {
                        self.runtime_error |= true;
                        Err(Evaluation(evaluation_error))
                    }
                },
                Err(parse_error) => {
                    self.error |= true;
                    Err(Parse(parse_error))
                }
            }
        }
    }
}
