use crate::callable::Clock;
use crate::environment::Environment;
use crate::evaluation_result::EvaluationResult;
use crate::grammar::{EvaluationError, Expression};
use crate::interpreter::InterpreterError::Execution;
use crate::lexical_error::LexicalError;
use crate::parser::{ParseError, Parser};
use crate::scanner::Scanner;
use crate::side_effects::{SideEffects, StandardSideEffects};
use crate::statement::Statement;
use crate::token::Token;
use std::cell::RefCell;
use std::rc::Rc;
use InterpreterError::{Lex, Parse};

/// An interpreter takes source code and executes it
pub(crate) struct Interpreter {
    environment: Rc<RefCell<Environment>>,
    side_effects: Rc<RefCell<dyn SideEffects>>,
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new(Rc::new(RefCell::new(StandardSideEffects)))
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
    Execution(EvaluationError),
}

impl Interpreter {
    pub fn new(side_effects: Rc<RefCell<dyn SideEffects>>) -> Self {
        // globals
        let environment = Rc::new(RefCell::new(Environment::default()));
        environment
            .borrow_mut()
            .define(
                "clock".to_string(),
                Clock {
                    closure: environment.clone(),
                }
                .into(),
            )
            .expect("Unable to define `clock` native function");

        Self {
            environment,
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
    ///   successfully
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
        expression.evaluate(self.environment.clone(), self.side_effects.clone())
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

    #[test]
    fn break_prevents_future_iterations() {
        // given
        let source = "
for (var i = 0; i < 10; i = i - 1) { // infinite loop 😱
    print i;
    if (true) {
        print \"then clause\";
        break;
    } else {
        print \"else clause\";
    }
    print \"Don't print this\";
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
        assert_eq!(side_effects.lines.len(), 2);
        assert_eq!(side_effects.lines[0], "0e0");
        assert_eq!(side_effects.lines[1], "then clause");
    }

    #[test]
    fn continue_prevents_subsequent_statements() {
        // given
        let source = "
for (var i = 0; i < 3; i = i + 1) {
    print i;
    if (false) {
        print \"then clause\";
    } else {
        continue;
        print \"else clause\";
    }
    print \"Don't print this\";
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
        assert_eq!(side_effects.lines.len(), 3);
        assert_eq!(side_effects.lines[0], "0e0");
        assert_eq!(side_effects.lines[1], "1e0");
        assert_eq!(side_effects.lines[2], "2e0");
    }

    #[test]
    fn break_applies_to_inner_most_loop() {
        // given
        let source = "
for (var i = 0; i < 3; i = i + 1) {
    for (var j = 0; j < 3; j = j - 1) { // infinite loop 😱
        break;
        print \"inner\";
        print j;
    }
    print i;
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
        assert_eq!(side_effects.lines.len(), 3);
        assert_eq!(side_effects.lines[0], "0e0");
        assert_eq!(side_effects.lines[1], "1e0");
        assert_eq!(side_effects.lines[2], "2e0");
    }

    #[test]
    fn continue_applies_to_inner_most_loop() {
        // given
        let source = "
for (var i = 0; i < 3; i = i - 1) { // infinite loop 😱
    for (var j = 0; j < 3; j = j + 1) {
        print j;
        continue;
        print \"inner\";
    }
    break;
    print \"outer\";
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
        assert_eq!(side_effects.lines.len(), 3);
        assert_eq!(side_effects.lines[0], "0e0");
        assert_eq!(side_effects.lines[1], "1e0");
        assert_eq!(side_effects.lines[2], "2e0");
    }

    #[test]
    fn define_and_run_function() {
        // given
        let source = "
fun add(a, b, c) {
  print a + b + c;
}
add( 1, 2, 3 );
";
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let mut interpreter = Interpreter::new(side_effects.clone());

        // when
        interpreter
            .run(source)
            .expect("Unable to execute source file");

        // then
        let side_effects = side_effects.borrow();
        assert_eq!(side_effects.lines.len(), 1);
        assert_eq!(side_effects.lines[0], "6e0");
    }

    #[test]
    fn recursive_fib() {
        // given
        let source = "
fun fib(n) {
  if (n <= 1) return n;
  return fib(n - 2) + fib(n - 1);
}

for (var i = 0; i < 20; i = i + 1) {
  print fib(i);
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
        assert_eq!(side_effects.lines.len(), 20);
        assert_eq!(side_effects.lines[0], "0e0");
        assert_eq!(side_effects.lines[1], "1e0");
        assert_eq!(side_effects.lines[2], "1e0");
        assert_eq!(side_effects.lines[3], "2e0");
        assert_eq!(side_effects.lines[4], "3e0");
        assert_eq!(side_effects.lines[5], "5e0");
        assert_eq!(side_effects.lines[6], "8e0");
        assert_eq!(side_effects.lines[7], "13e0");
        assert_eq!(side_effects.lines[8], "21e0");
        assert_eq!(side_effects.lines[9], "34e0");
        assert_eq!(side_effects.lines[10], "55e0");
        assert_eq!(side_effects.lines[11], "89e0");
        assert_eq!(side_effects.lines[12], "144e0");
        assert_eq!(side_effects.lines[13], "233e0");
        assert_eq!(side_effects.lines[14], "377e0");
        assert_eq!(side_effects.lines[15], "610e0");
        assert_eq!(side_effects.lines[16], "987e0");
        assert_eq!(side_effects.lines[17], "1.597e3");
        assert_eq!(side_effects.lines[18], "2.584e3");
        assert_eq!(side_effects.lines[19], "4.181e3");
    }

    #[test]
    fn closure_capture() {
        // given
        let source = "
fun makeCounter() {
  var i = 0;
  fun count() {
    i = i + 1;
    print i;
  }

  return count;
}

var counter = makeCounter();
counter(); // 1e0
counter(); // 2e0
";
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let mut interpreter = Interpreter::new(side_effects.clone());

        // when
        interpreter
            .run(source)
            .expect("Unable to execute source file");

        // then
        let side_effects = side_effects.borrow();
        assert_eq!(side_effects.lines.len(), 2);
        assert_eq!(side_effects.lines[0], "1e0");
        assert_eq!(side_effects.lines[1], "2e0");
    }

    #[test]
    fn evaluate_lambda() {
        // given
        let source = "
fun thrice(fn) {
  for (var i = 1; i <= 3; i = i + 1) {
    fn(i);
  }
}

thrice(fun (a) {
  print a;
});
// \"1\".
// \"2\".
// \"3\".
";
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let mut interpreter = Interpreter::new(side_effects.clone());

        // when
        interpreter
            .run(source)
            .expect("Unable to execute source file");

        // then
        let side_effects = side_effects.borrow();
        assert_eq!(side_effects.lines.len(), 3);
        assert_eq!(side_effects.lines[0], "1e0");
        assert_eq!(side_effects.lines[1], "2e0");
        assert_eq!(side_effects.lines[2], "3e0");
    }

    #[test]
    fn can_pass_functions_as_arguments() {
        // given
        let source = "
fun thrice(fn) {
  for (var i = 1; i <= 3; i = i + 1) {
    fn(i);
  }
}

fun p(a) {
  print a;
}

thrice(p);
// \"1\".
// \"2\".
// \"3\".
";
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let mut interpreter = Interpreter::new(side_effects.clone());

        // when
        interpreter
            .run(source)
            .expect("Unable to execute source file");

        // then
        let side_effects = side_effects.borrow();
        assert_eq!(side_effects.lines.len(), 3);
        assert_eq!(side_effects.lines[0], "1e0");
        assert_eq!(side_effects.lines[1], "2e0");
        assert_eq!(side_effects.lines[2], "3e0");
    }

    #[derive(Default, Clone)]
    struct TestSideEffects {
        lines: Vec<String>,
    }

    impl SideEffects for TestSideEffects {
        fn println(&mut self, text: &str) {
            self.lines.push(text.to_string());
            eprintln!("-- {}", text);
        }

        fn eprintln(&mut self, text: &str) {
            eprintln!("ERROR: {}", text)
        }
    }
}
