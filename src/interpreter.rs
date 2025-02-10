use crate::environment::Environment;
use crate::grammar::{EvaluationError, EvaluationResult, Expression};
use crate::interpreter::InterpreterError::Execution;
use crate::lexical_error::LexicalError;
use crate::parser::{ParseError, Parser};
use crate::scanner::Scanner;
use crate::side_effects::{SideEffects, StandardSideEffects};
use crate::statement::{ExecutionError, Statement};
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

#[derive(Debug)]
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
            if let Err(execution_error) =
                statement.execute(self.environment.clone(), self.side_effects.clone())
            {
                self.side_effects
                    .borrow_mut()
                    .eprintln(&format!("{}", execution_error));
                return Err(Execution(execution_error));
            }
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

#[cfg(test)]
mod tests {
    use super::Interpreter;
    use crate::side_effects::SideEffects;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn can_interpret_fib() {
        // given
        let source = "
var a = 0;
var temp;

for (var b = 1; a < 10000; b = temp + b) {
  print a;
  temp = a;
  a = b;
}
";
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let mut interpreter = Interpreter::new(side_effects.clone());

        // when
        interpreter
            .run(source)
            .expect("Unable to execute source file");

        // then
        let side_effects = side_effects.borrow();
        assert_eq!(side_effects.lines.len(), 21);
        assert_eq!(side_effects.lines[20], "6.765e3");
    }

    #[derive(Default)]
    struct TestSideEffects {
        lines: Vec<String>,
    }

    impl SideEffects for TestSideEffects {
        fn println(&mut self, text: &str) {
            self.lines.push(text.to_string())
        }

        fn eprintln(&mut self, _text: &str) {
            unimplemented!()
        }
    }
}
