use crate::environment::Environment;
use crate::grammar::{EvaluationError, EvaluationResult, ExecutionError, Expression, Statement};
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
    side_effects: Rc<RefCell<S>>,
}

impl Default for Interpreter<StandardSideEffects> {
    fn default() -> Self {
        Self::new(Rc::new(RefCell::new(Default::default())))
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
    pub fn new(side_effects: Rc<RefCell<S>>) -> Self {
        Self {
            environment: Default::default(),
            side_effects,
        }
    }

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
                .execute(self.environment.clone(), self.side_effects.clone())
                .map_err(Execution)?;
        }

        Ok(())
    }

    pub fn evaluate(
        &mut self,
        expression: &Expression,
    ) -> Result<EvaluationResult, EvaluationError> {
        expression.evaluate(&mut self.environment.borrow_mut())
    }
}
