use crate::environment::{Environment, ExistsError};
use crate::grammar::{EvaluationError, EvaluationResult, Expression};
use crate::side_effects::SideEffects;
use crate::statement::ExecutionError::{CannotRedefineVariable, Evaluation};
use either::Either;
use std::cell::RefCell;
use std::rc::Rc;

// #[derive(Clone, Debug)]
// pub(crate) struct Program {
//     statements: Vec<Statement>,
// }

/// A statement is an instruction that produces a side effect
#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) enum Statement {
    /// Evaluates expressions that have side effects
    Expression(Expression),

    /// A structured loop with its own scope
    For {
        /// An expression executed exactly once. If it declares a new variable, it will be scoped to
        /// the loop body.
        initializer: Option<Either<VariableDeclarationStatement, Expression>>,
        /// The loop body will continue to execute as long as this is true
        condition: Option<Expression>,
        /// An expression executed after the loop body to control iteration. The result is
        /// discarded.
        increment: Option<Expression>,
        /// The loop body
        statement: Box<Statement>,
    },

    /// A conditional or branching control flow
    If {
        condition: Expression,
        then_branch: Box<Statement>,
        else_branch: Option<Box<Statement>>,
    },

    /// Evaluates an expression and outputs the result
    Print(Expression),

    /// Execute a statement until some condition is no longer met
    While(Expression, Box<Statement>),

    /// A variable declaration with optional definition
    VariableDeclaration(VariableDeclarationStatement),

    Block(Vec<Statement>),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct VariableDeclarationStatement {
    pub identifier: String,
    /// If None, this is a variable declaration without assignment
    pub expression: Option<Expression>,
}

impl From<VariableDeclarationStatement> for Statement {
    fn from(value: VariableDeclarationStatement) -> Self {
        Self::VariableDeclaration(value)
    }
}

impl VariableDeclarationStatement {
    pub fn execute(&self, environment: Rc<RefCell<Environment>>) -> Result<(), ExecutionError> {
        let result = self
            .expression
            .clone()
            .map(|e| e.evaluate(&mut environment.borrow_mut()))
            .unwrap_or(Ok(EvaluationResult::Nil))
            .map_err(Evaluation)?;

        environment
            .borrow_mut()
            .define(self.identifier.clone(), result)
            .map_err(CannotRedefineVariable)?;

        Ok(())
    }
}

#[derive(Eq, PartialEq, Debug)]
pub(crate) enum ExecutionError {
    Evaluation(EvaluationError),
    CannotRedefineVariable(ExistsError),
}

impl Statement {
    pub fn execute<S: SideEffects>(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<S>>,
    ) -> Result<(), ExecutionError> {
        match self {
            Self::Expression(expression) => {
                expression
                    .evaluate(&mut environment.borrow_mut())
                    .map_err(Evaluation)?;
                Ok(())
            }
            Self::For {
                initializer,
                condition,
                increment,
                statement,
            } => {
                // For loops get their own scope
                let child = Rc::new(RefCell::new(Environment::new_nested_scope(
                    environment.clone(),
                )));
                match initializer {
                    Some(Either::Left(declaration)) => {
                        declaration.execute(child.clone())?;
                    }
                    Some(Either::Right(expression)) => {
                        expression
                            .evaluate(&mut child.borrow_mut())
                            .map_err(Evaluation)?;
                    }
                    None => {}
                }

                let evaluate_condition = || -> Result<bool, ExecutionError> {
                    Ok(if let Some(condition) = condition {
                        condition
                            .evaluate(&mut child.borrow_mut())
                            .map_err(Evaluation)?
                            .is_truthful()
                    } else {
                        true
                    })
                };

                while evaluate_condition()? {
                    match statement.as_ref() {
                        Self::Block(statements) => {
                            // avoid creating a new child scope when we already created one for the
                            // "for" loop
                            for statement in statements {
                                statement.execute(child.clone(), side_effects.clone())?;
                            }
                        }
                        _ => statement.execute(child.clone(), side_effects.clone())?,
                    }
                    if let Some(increment) = increment {
                        increment
                            .evaluate(&mut child.borrow_mut())
                            .map_err(Evaluation)?;
                    }
                }

                Ok(())
            }
            Self::Print(value) => {
                let result = value
                    .evaluate(&mut environment.borrow_mut())
                    .map_err(Evaluation)?;

                side_effects.borrow_mut().println(&format!("{}", result));

                Ok(())
            }
            Self::VariableDeclaration(declaration) => declaration.execute(environment.clone()),
            Self::While(condition, statement) => {
                while condition
                    .evaluate(&mut environment.borrow_mut())
                    .map_err(Evaluation)?
                    .is_truthful()
                {
                    statement.execute(environment.clone(), side_effects.clone())?;
                }
                Ok(())
            }
            Self::Block(statements) => {
                let child = Rc::new(RefCell::new(Environment::new_nested_scope(
                    environment.clone(),
                )));
                for statement in statements {
                    statement.execute(child.clone(), side_effects.clone())?;
                }
                Ok(())
            }
            Self::If {
                condition,
                then_branch,
                else_branch,
            } => {
                if condition
                    .evaluate(&mut environment.borrow_mut())
                    .map_err(Evaluation)?
                    .is_truthful()
                {
                    then_branch.execute(environment.clone(), side_effects.clone())
                } else if let Some(else_branch) = else_branch {
                    else_branch.execute(environment.clone(), side_effects.clone())
                } else {
                    Ok(())
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ExecutionError, Statement, VariableDeclarationStatement};
    use crate::environment::Environment;
    use crate::grammar::{BinaryOperator, EvaluationError, EvaluationResult, Expression};
    use crate::side_effects::{SideEffects, StandardSideEffects};
    use crate::statement::Statement::{Block, Print};
    use bigdecimal::{BigDecimal, One, Zero};
    use either::Left;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn unsuccessful_execution_test(statement: &Statement, expected: &ExecutionError) {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(StandardSideEffects::default()));

        // when
        let result = statement.execute(environment, side_effects);

        // then
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert_eq!(error, *expected);
    }

    macro_rules! unsuccessful_execution_tests {
        ($($name:ident: $value:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let (expression, expected) = $value;
                unsuccessful_execution_test(&expression, &expected);
            }
        )*
        }
    }

    unsuccessful_execution_tests! {
        use_variable_before_declaration: (
            Statement::Print(Expression::VariableReference("a".to_string())),
            ExecutionError::Evaluation(EvaluationError::Undefined),
        ),
        assignment_without_declaration: (
            Statement::Expression(Expression::Assignment("a".to_string(), Box::new(BigDecimal::one().into()))),
            ExecutionError::Evaluation(EvaluationError::Undefined),
        ),
    }

    #[test]
    fn print_variable() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let variable_definition = Statement::VariableDeclaration(VariableDeclarationStatement {
            identifier: "beverage".to_string(),
            expression: Some("espresso".to_string().into()),
        });
        let print_statement =
            Statement::Print(Expression::VariableReference("beverage".to_string()));

        // when
        variable_definition
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to define variable");
        print_statement
            .execute(environment, side_effects.clone())
            .expect("Unable to execute print statement");

        // then
        assert_eq!(side_effects.borrow().lines.len(), 1);
        assert_eq!(side_effects.borrow().lines[0], "espresso");
    }

    #[test]
    fn redefine_variable() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        let initial_definition = Statement::VariableDeclaration(VariableDeclarationStatement {
            identifier: "a".to_string(),
            expression: Some("before".to_string().into()),
        });
        let subsequent_definition = Statement::VariableDeclaration(VariableDeclarationStatement {
            identifier: "a".to_string(),
            expression: Some("after".to_string().into()),
        });
        let print_statement = Statement::Print(Expression::VariableReference("a".to_string()));

        // when
        initial_definition
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to define variable");
        print_statement
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to print initial variable value");
        subsequent_definition
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to redefine variable");
        print_statement
            .execute(environment, side_effects.clone())
            .expect("Unable to print subsequent variable value");

        // then
        assert_eq!(side_effects.borrow().lines.len(), 2);
        assert_eq!(side_effects.borrow().lines[0], "before");
        assert_eq!(side_effects.borrow().lines[1], "after");
    }

    #[test]
    fn uninitialized_variables_are_nil() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        let declaration = Statement::VariableDeclaration(VariableDeclarationStatement {
            identifier: "a".to_string(),
            expression: None,
        });
        let print_statement = Statement::Print(Expression::VariableReference("a".to_string()));

        // when
        declaration
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to declare variable");
        print_statement
            .execute(environment, side_effects.clone())
            .expect("Unable to print initial variable value");

        // then
        assert_eq!(side_effects.borrow().lines.len(), 1);
        assert_eq!(side_effects.borrow().lines[0], "nil");
    }

    #[test]
    fn math_on_variables() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        let define_a = Statement::VariableDeclaration(VariableDeclarationStatement {
            identifier: "a".to_string(),
            expression: Some(BigDecimal::one().into()),
        });
        let define_b = Statement::VariableDeclaration(VariableDeclarationStatement {
            identifier: "b".to_string(),
            expression: Some(BigDecimal::from(2).into()),
        });
        let print_statement = Statement::Print(Expression::Binary {
            operator: BinaryOperator::Add,
            left_value: Box::new(Expression::VariableReference("a".to_string())),
            right_value: Box::new(Expression::VariableReference("b".to_string())),
        });

        // when
        define_a
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to define a");
        define_b
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to define b");
        print_statement
            .execute(environment, side_effects.clone())
            .expect("Unable to print evaluation result");

        // then
        assert_eq!(side_effects.borrow().lines.len(), 1);
        assert_eq!(side_effects.borrow().lines[0], "3e0");
    }

    #[test]
    fn assignment_returns_value() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        let define_a = Statement::VariableDeclaration(VariableDeclarationStatement {
            identifier: "a".to_string(),
            expression: Some(BigDecimal::one().into()),
        });
        let print_statement = Statement::Print(Expression::Assignment(
            "a".to_string(),
            Box::new(BigDecimal::from(2).into()),
        ));

        // when
        define_a
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to define variable");
        print_statement
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to print expression");

        // then
        assert_eq!(side_effects.borrow().lines.len(), 1);
        assert_eq!(side_effects.borrow().lines[0], "2e0");
        assert_eq!(
            environment.borrow().get("a"),
            Ok(EvaluationResult::Number(BigDecimal::from(2).into()))
        );
    }

    #[test]
    fn then_clause_executed() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let conditional = Statement::If {
            condition: true.into(),
            then_branch: Box::new(Statement::Print("then clause".to_string().into())),
            else_branch: None,
        };

        // when
        conditional
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute conditional");

        // then
        assert_eq!(side_effects.borrow().lines.len(), 1);
        assert_eq!(side_effects.borrow().lines[0], "then clause");
    }

    #[test]
    fn no_clause_executed() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let conditional = Statement::If {
            condition: false.into(),
            then_branch: Box::new(Statement::Print("then clause".to_string().into())),
            else_branch: None,
        };

        // when
        conditional
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute conditional");

        // then
        assert!(side_effects.borrow().lines.is_empty());
    }

    #[test]
    fn else_clause_executed() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let conditional = Statement::If {
            condition: false.into(),
            then_branch: Box::new(Statement::Print("then clause".to_string().into())),
            else_branch: Some(Box::new(Statement::Print("else clause".to_string().into()))),
        };

        // when
        conditional
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute conditional");

        // then
        assert_eq!(side_effects.borrow().lines.len(), 1);
        assert_eq!(side_effects.borrow().lines[0], "else clause");
    }

    #[test]
    fn while_loop_terminates() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let declaration = Statement::VariableDeclaration(VariableDeclarationStatement {
            // var c = 0
            identifier: "c".to_string(),
            expression: Some(0u8.into()),
        });
        let reference = Box::new(Expression::VariableReference("c".to_string()));
        let increment = Statement::Expression(
            // c = c + 1
            Expression::Assignment(
                "c".to_string(),
                Box::new(Expression::Binary {
                    operator: BinaryOperator::Add,
                    left_value: reference.clone(),
                    right_value: Box::new(1u8.into()),
                }),
            ),
        );
        let condition = Expression::Binary {
            // c < 8
            operator: BinaryOperator::LessThan,
            left_value: reference.clone(),
            right_value: Box::new(8u8.into()),
        };
        let while_loop = Statement::While(condition, Box::new(increment)); // while c < 8 { c = c + 1 }

        // when
        declaration
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to declare variable.");
        while_loop
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute while loop.");

        // then
        let result = environment.borrow().get("c").expect("c is not defined");
        assert_eq!(result, EvaluationResult::Number(BigDecimal::from(8u8)));
    }

    #[test]
    fn block_for_loop_terminates() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        let initializer = VariableDeclarationStatement {
            identifier: "i".to_string(),
            expression: Expression::from(10u8).into(),
        };
        let condition = Expression::Binary {
            operator: BinaryOperator::GreaterThanOrEqual,
            left_value: Box::new(Expression::Assignment(
                "i".to_string(),
                Box::new(Expression::Binary {
                    operator: BinaryOperator::Subtract,
                    left_value: Box::new(Expression::VariableReference("i".to_string())),
                    right_value: Box::new(BigDecimal::one().into()),
                }),
            )),
            right_value: Box::new(BigDecimal::zero().into()),
        };
        let statement = Block(vec![Print(Expression::VariableReference("i".to_string()))]);

        let for_loop = Statement::For {
            initializer: Left(initializer).into(), // i = 10
            condition: condition.into(),           // (i = i - 1) >= 0
            increment: None,                       // <empty>
            statement: Box::new(statement),        // { print i };
        };

        // when
        for_loop
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute for loop.");

        // then
        let lines = &side_effects.borrow().lines;
        assert_eq!(lines.len(), 10);
        for (i, line) in lines.iter().enumerate() {
            assert_eq!(line, &format!("{}e0", 10 - i - 1));
        }
        assert!(
            environment.borrow().get("i").is_err(),
            "loop scope should have been discarded"
        );
    }

    #[test]
    fn for_loop_condition_can_increment() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        let initializer = VariableDeclarationStatement {
            identifier: "j".to_string(),
            expression: Expression::from(10u8).into(),
        };
        let condition = Expression::Binary {
            operator: BinaryOperator::GreaterThanOrEqual,
            left_value: Box::new(Expression::Assignment(
                "j".to_string(),
                Box::new(Expression::Binary {
                    operator: BinaryOperator::Subtract,
                    left_value: Box::new(Expression::VariableReference("j".to_string())),
                    right_value: Box::new(BigDecimal::one().into()),
                }),
            )),
            right_value: Box::new(BigDecimal::zero().into()),
        };
        let statement = Print(Expression::VariableReference("j".to_string()));

        let for_loop = Statement::For {
            initializer: Left(initializer).into(), // j = 10
            condition: condition.into(),           // (j = j - 1) >= 0
            increment: None,                       // <empty>
            statement: Box::new(statement),        // print j;
        };

        // when
        for_loop
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute for loop.");

        // then
        let lines = &side_effects.borrow().lines;
        assert_eq!(lines.len(), 10);
        for (i, line) in lines.iter().enumerate() {
            assert_eq!(line, &format!("{}e0", 10 - i - 1));
        }
        assert!(
            environment.borrow().get("j").is_err(),
            "loop scope should have been discarded"
        );
    }

    #[test]
    fn simple_for_loop() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        let initializer = VariableDeclarationStatement {
            identifier: "k".to_string(),
            expression: Expression::from(0u8).into(),
        };
        let condition = Expression::Binary {
            operator: BinaryOperator::LessThan,
            left_value: Box::new(Expression::VariableReference("k".to_string())),
            right_value: Box::new(10u8.into()),
        };
        let increment = Expression::Assignment(
            "k".to_string(),
            Box::new(Expression::Binary {
                operator: BinaryOperator::Add,
                left_value: Box::new(Expression::VariableReference("k".to_string())),
                right_value: Box::new(BigDecimal::one().into()),
            }),
        );
        let statement = Print(Expression::VariableReference("k".to_string()));

        let for_loop = Statement::For {
            initializer: Left(initializer).into(), // k = 0
            condition: condition.into(),           // k < 10
            increment: Some(increment),            // k = k + 1
            statement: Box::new(statement),        // print k;
        };

        // when
        for_loop
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute for loop.");

        // then
        let lines = &side_effects.borrow().lines;
        assert_eq!(lines.len(), 10);
        for (i, line) in lines.iter().enumerate() {
            assert_eq!(line, &format!("{}e0", i));
        }
        assert!(
            environment.borrow().get("k").is_err(),
            "loop scope should have been discarded"
        );
    }

    #[test]
    fn for_loop_modifies_existing_environment() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        let initializer = Statement::VariableDeclaration(VariableDeclarationStatement {
            identifier: "i".to_string(),
            expression: Expression::from(10u8).into(),
        });

        let condition = Expression::Binary {
            operator: BinaryOperator::GreaterThanOrEqual,
            left_value: Box::new(Expression::Assignment(
                "i".to_string(),
                Box::new(Expression::Binary {
                    operator: BinaryOperator::Subtract,
                    left_value: Box::new(Expression::VariableReference("i".to_string())),
                    right_value: Box::new(BigDecimal::one().into()),
                }),
            )),
            right_value: Box::new(BigDecimal::zero().into()),
        };
        let statement = Block(vec![Print(Expression::VariableReference("i".to_string()))]);

        let for_loop = Statement::For {
            initializer: None,
            condition: condition.into(),    // (i = i - 1) >= 0
            increment: None,                // <empty>
            statement: Box::new(statement), // { print i };
        };

        // when
        initializer
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to initialize counter");
        for_loop
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute for loop.");

        // then
        let lines = &side_effects.borrow().lines;
        assert_eq!(lines.len(), 10);
        for (i, line) in lines.iter().enumerate() {
            assert_eq!(line, &format!("{}e0", 10 - i - 1));
        }
        assert!(matches!(
            environment.borrow()
                .get("i")
                .expect("i should exist in environment"),
            EvaluationResult::Number(i)
            if i == BigDecimal::from(-1)
        ))
    }

    #[derive(Default)]
    struct TestSideEffects {
        lines: Vec<String>,
    }

    impl SideEffects for TestSideEffects {
        fn println(&mut self, text: &str) {
            self.lines.push(text.to_string());
        }

        // fn eprintln(&mut self, text: &str) {
        //     eprintln!("{}", text);
        // }
    }

    impl From<u8> for Expression {
        fn from(value: u8) -> Self {
            BigDecimal::from(value).into()
        }
    }
}
