use crate::environment::Environment;
use crate::grammar::{ExecutionError, Statement};
use crate::interpreter::InterpreterError::Execution;
use crate::lexical_error::LexicalError;
use crate::parser::{ParseError, Parser};
use crate::scanner::Scanner;
use crate::side_effects::{SideEffects, StandardSideEffects};
use crate::token::Token;
use std::cell::RefCell;
use std::rc::Rc;
use InterpreterError::{Lex, Parse};

/// An interpreter takes source code and executes it
pub(crate) struct Interpreter<S: SideEffects> {
    environment: Rc<RefCell<Environment>>,
    side_effects: S,
}

impl Default for Interpreter<StandardSideEffects> {
    fn default() -> Self {
        Self {
            environment: Default::default(),
            side_effects: Default::default(),
        }
    }
}

pub(crate) enum InterpreterError {
    /// Errors occurred while tokenizing the input
    Lex(Vec<LexicalError>),
    /// The tokenized input is nonsensical
    Parse(ParseError),
    // Evaluation(EvaluationError),
    /// A statement could not be executed
    Execution(ExecutionError),
}

impl<S: SideEffects> Interpreter<S> {
    /// Execute a block of Lox source code
    ///
    /// Parameters:
    /// - `source`: Lox source code
    ///
    /// Returns:
    /// - `()`: If all the statements in the source code could be tokenized, parsed, and executed
    ///         successfully
    ///- `InterpreterError`: If a lexical, parsing, or execution error occurred
    pub fn run(&mut self, source: &str) -> Result<(), InterpreterError> {
        let scanner: Scanner = source.into();

        let tokens: Vec<Token> = scanner.try_into().map_err(Lex)?;
        let parser: Parser = tokens.into();
        let statements: Vec<Statement> = parser.try_into().map_err(Parse)?;
        for statement in statements {
            statement
                .execute(self.environment.clone(), &mut self.side_effects)
                .map_err(Execution)?;
        }

        Ok(())
    }
}
