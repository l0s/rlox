use crate::grammar::Expression;
use crate::interpreter::InterpreterError::Parse;
use crate::lexical_error::LexicalError;
use crate::parser::{ParseError, Parser};
use crate::scanner::Scanner;

#[derive(Default)]
pub(crate) struct Interpreter {
    pub error: bool,
}

pub(crate) enum InterpreterError {
    Lex(Vec<LexicalError>),
    Parse(ParseError),
}

impl Interpreter {
    pub fn run(&mut self, source: &str) -> Result<Expression, InterpreterError> {
        let mut scanner: Scanner = source.into();
        scanner.scan_tokens();
        if !scanner.errors.is_empty() {
            self.error |= true;
            Err(InterpreterError::Lex(scanner.errors))
        } else {
            let mut parser: Parser = scanner.tokens.into();

            parser.parse().map_err(Parse)
        }
    }
}
