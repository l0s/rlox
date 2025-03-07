use crate::callable::Callables;
use crate::environment::{Environment, LoopControl};
use crate::evaluation_result::EvaluationResult;
use crate::grammar::EvaluationError::{CannotRedefineVariable, NotInALoop};
use crate::grammar::{EvaluationError, Expression, FunctionDefinition};
use crate::side_effects::SideEffects;
use either::Either;
use std::cell::RefCell;
use std::rc::Rc;

// #[derive(Clone, Debug)]
// pub(crate) struct Program {
//     statements: Vec<Statement>,
// }

/// A statement is an instruction that produces a side effect and does not evaluate to a value.
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

    /// A function definition
    Function {
        name: String,
        parameter_names: Vec<String>,
        statements: Vec<Statement>,
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
    /// Exit a loop, skipping any remaining statements in an iteration and all subsequent iterations
    Break,
    /// Jump to the next iteration of a loop, skipping any remaining statements in the current
    /// iteration
    Continue,

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
    pub fn execute(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
    ) -> Result<(), EvaluationError> {
        let result = self
            .expression
            .clone()
            .map(|e| e.evaluate(environment.clone(), side_effects.clone()))
            .unwrap_or(Ok(EvaluationResult::Nil))?;

        environment
            .borrow_mut()
            .define(self.identifier.clone(), result)
            .map_err(CannotRedefineVariable)?;

        Ok(())
    }
}

impl Statement {
    /// Run the statement
    ///
    /// Parameters:
    /// - `environment` - the variable scope in which to execute the statement
    /// - `side_effects` - a handle to the outside world
    ///
    /// Returns:
    /// - `()` - if the statement was executed successfully
    /// - `EvaluationError` - if a non-recoverable error occurred
    pub fn execute(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
    ) -> Result<(), EvaluationError> {
        match self {
            Self::Expression(expression) => {
                self.execute_expression(environment, expression, side_effects)
            }
            Self::For {
                initializer,
                condition,
                increment,
                statement,
            } => self.execute_for_loop(
                environment,
                side_effects,
                initializer,
                condition,
                increment,
                statement.clone(),
            ),
            Self::Function {
                name,
                parameter_names,
                statements,
            } => {
                // TODO consider separating mechanism for defining variables and functions? Error might be misleading.
                environment
                    .borrow_mut()
                    .define(
                        name.clone(),
                        EvaluationResult::Function(Callables::UserDefinedFunction(
                            FunctionDefinition {
                                name: name.clone(),
                                parameter_names: parameter_names.clone(),
                                statements: statements.clone(),
                            },
                        )),
                    )
                    .map_err(CannotRedefineVariable)
            }
            Self::Print(value) => self.execute_print(environment, side_effects, value),
            Self::VariableDeclaration(declaration) => {
                declaration.execute(environment, side_effects)
            }
            Self::While(condition, statement) => {
                self.execute_while_loop(environment, side_effects, condition, statement.as_ref())
            }
            Self::Block(statements) => {
                let child = Rc::new(RefCell::new(Environment::new_nested_scope(environment)));
                self.execute_block(child, side_effects, statements)
            }
            Self::If {
                condition,
                then_branch,
                else_branch,
            } => self.execute_if_statement(
                environment,
                side_effects,
                condition,
                then_branch.as_ref(),
                else_branch.clone(),
            ),
            Self::Break => environment.borrow_mut().exit_loop().map_err(NotInALoop),
            Self::Continue => environment
                .borrow_mut()
                .jump_to_next_loop_iteration()
                .map_err(NotInALoop),
        }
    }

    fn execute_expression(
        &self,
        environment: Rc<RefCell<Environment>>,
        expression: &Expression,
        side_effects: Rc<RefCell<dyn SideEffects>>,
    ) -> Result<(), EvaluationError> {
        expression.evaluate(environment, side_effects)?;
        Ok(())
    }

    fn execute_for_loop(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        initializer: &Option<Either<VariableDeclarationStatement, Expression>>,
        condition: &Option<Expression>,
        increment: &Option<Expression>,
        statement: Box<Statement>,
    ) -> Result<(), EvaluationError> {
        // For loops get their own scope
        let loop_control = Rc::new(RefCell::new(LoopControl::default()));
        let environment = Rc::new(RefCell::new(Environment::new_nested_loop_scope(
            environment,
            loop_control.clone(),
        )));
        match initializer {
            Some(Either::Left(declaration)) => {
                declaration.execute(environment.clone(), side_effects.clone())?;
            }
            Some(Either::Right(expression)) => {
                expression.evaluate(environment.clone(), side_effects.clone())?;
            }
            None => {}
        }

        let evaluate_condition = || -> Result<bool, EvaluationError> {
            Ok(if let Some(condition) = condition {
                condition
                    .evaluate(environment.clone(), side_effects.clone())?
                    .is_truthful()
            } else {
                true
            })
        };

        while evaluate_condition()? {
            match statement.as_ref() {
                // If statement is a block, avoid creating a new nested scope since the loop already
                // defines its own scope
                Self::Block(statements) => {
                    self.execute_block(environment.clone(), side_effects.clone(), statements)?
                }
                _ => statement.execute(environment.clone(), side_effects.clone())?,
            }
            // Check if `break` or `continue` was called. Preemption of remaining statements is
            // handled in `execute_block(Environment, SideEffects, &[Statement])`.
            if loop_control.borrow().exit_loop {
                break;
            } else if loop_control.borrow().jump_to_next_iteration {
                loop_control.borrow_mut().jump_to_next_iteration = false;
            }
            if let Some(increment) = increment {
                increment.evaluate(environment.clone(), side_effects.clone())?;
            }
        }

        Ok(())
    }

    fn execute_print(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        value: &Expression,
    ) -> Result<(), EvaluationError> {
        let result = value.evaluate(environment, side_effects.clone())?;

        side_effects.borrow_mut().println(&format!("{}", result));

        Ok(())
    }

    fn execute_while_loop(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        condition: &Expression,
        statement: &Statement,
    ) -> Result<(), EvaluationError> {
        let loop_control = Rc::new(RefCell::new(LoopControl::default()));
        let environment = Rc::new(RefCell::new(Environment::new_nested_loop_scope(
            environment.clone(),
            loop_control.clone(),
        )));
        while condition
            .evaluate(environment.clone(), side_effects.clone())?
            .is_truthful()
        {
            statement.execute(environment.clone(), side_effects.clone())?;
            if loop_control.borrow().exit_loop {
                break;
            } else if loop_control.borrow().jump_to_next_iteration {
                loop_control.borrow_mut().jump_to_next_iteration = false;
            }
        }
        Ok(())
    }

    fn execute_block(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        statements: &[Statement],
    ) -> Result<(), EvaluationError> {
        for statement in statements {
            statement.execute(environment.clone(), side_effects.clone())?;
            if environment.borrow().should_exit_loop()
                || environment.borrow().should_jump_to_next_loop_iteration()
            {
                // stop executing remaining statements
                // loop control will be managed in the loop statement (for or while)
                break;
            }
        }
        Ok(())
    }

    fn execute_if_statement(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        condition: &Expression,
        then_branch: &Statement,
        else_branch: Option<Box<Statement>>,
    ) -> Result<(), EvaluationError> {
        if condition
            .evaluate(environment.clone(), side_effects.clone())?
            .is_truthful()
        {
            then_branch.execute(environment, side_effects)
        } else if let Some(else_branch) = else_branch {
            else_branch.execute(environment, side_effects)
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Statement::{Block, Break, Continue, For, Function, If, Print};
    use super::{Statement, VariableDeclarationStatement};
    use crate::callable::Callables;
    use crate::environment::{Environment, NotInALoopError};
    use crate::evaluation_result::EvaluationResult;
    use crate::grammar::{
        BinaryOperator, EvaluationError, Expression, FunctionDefinition, Literal,
    };
    use crate::side_effects::{SideEffects, StandardSideEffects};
    use bigdecimal::{BigDecimal, One, Zero};
    use either::Left;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn unsuccessful_execution_test(statement: &Statement, expected: &EvaluationError) {
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
            Print(Expression::VariableReference("a".to_string())),
            EvaluationError::Undefined,
        ),
        assignment_without_declaration: (
            Statement::Expression(Expression::Assignment("a".to_string(), Box::new(BigDecimal::one().into()))),
            EvaluationError::Undefined,
        ),
        break_outside_loop: (
            Break,
            EvaluationError::NotInALoop(NotInALoopError),
        ),
        continue_outside_loop: (
            Continue,
            EvaluationError::NotInALoop(NotInALoopError),
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
        let print_statement = Print(Expression::Assignment(
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
        let conditional = If {
            condition: false.into(),
            then_branch: Box::new(Print("then clause".to_string().into())),
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
        let conditional = If {
            condition: false.into(),
            then_branch: Box::new(Print("then clause".to_string().into())),
            else_branch: Some(Box::new(Print("else clause".to_string().into()))),
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

    #[test]
    fn break_exits_loop() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        let declaration = VariableDeclarationStatement {
            identifier: "i".to_string(),
            expression: Some(BigDecimal::zero().into()),
        };
        let condition = Expression::Binary {
            operator: BinaryOperator::LessThan,
            left_value: Box::new(Expression::VariableReference("i".to_string())),
            right_value: Box::new(BigDecimal::from(1_000).into()),
        };
        let increment = Expression::Assignment(
            "i".to_string(),
            Box::new(Expression::Binary {
                operator: BinaryOperator::Add,
                left_value: Box::new(Expression::VariableReference("i".to_string())),
                right_value: Box::new(BigDecimal::one().into()),
            }),
        );
        let block = Block(vec![
            Print(Expression::Literal(Literal::String("Print me".to_string()))),
            Break,
            Print(Expression::Literal(Literal::String(
                "Don't print me".to_string(),
            ))),
        ]);
        let for_loop = For {
            initializer: Some(Left(declaration)),
            condition: Some(condition),
            increment: Some(increment),
            statement: Box::new(block),
        };

        // when
        for_loop
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute for loop");

        // then
        let lines = &side_effects.borrow().lines;
        assert_eq!(lines.len(), 1);
        assert_eq!(lines[0], "Print me".to_string());
    }

    #[test]
    fn continue_skips_statements() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        let declaration = VariableDeclarationStatement {
            identifier: "i".to_string(),
            expression: Some(BigDecimal::zero().into()),
        };
        let condition = Expression::Binary {
            operator: BinaryOperator::LessThan,
            left_value: Box::new(Expression::VariableReference("i".to_string())),
            right_value: Box::new(BigDecimal::from(3).into()),
        };
        let increment = Expression::Assignment(
            "i".to_string(),
            Box::new(Expression::Binary {
                operator: BinaryOperator::Add,
                left_value: Box::new(Expression::VariableReference("i".to_string())),
                right_value: Box::new(BigDecimal::one().into()),
            }),
        );
        let block = Block(vec![
            Print(Expression::VariableReference("i".to_string())),
            Continue,
            Print(Expression::Literal(Literal::String(
                "Don't print me".to_string(),
            ))),
        ]);
        let for_loop = For {
            initializer: Some(Left(declaration)),
            condition: Some(condition),
            increment: Some(increment),
            statement: Box::new(block),
        };

        // when
        for_loop
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute for loop");

        // then
        let lines = &side_effects.borrow().lines;
        assert_eq!(lines.len(), 3);
        assert_eq!(lines[0], "0e0".to_string());
        assert_eq!(lines[1], "1e0".to_string());
        assert_eq!(lines[2], "2e0".to_string());
    }

    #[test]
    fn continue_still_increments() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        environment
            .borrow_mut()
            .define(
                "i".to_string(),
                EvaluationResult::Number(BigDecimal::zero().into()),
            )
            .expect("Unable to define variable");
        environment
            .borrow_mut()
            .define(
                "j".to_string(),
                EvaluationResult::Number(BigDecimal::zero().into()),
            )
            .expect("Unable to define variable");

        let condition = Expression::Binary {
            operator: BinaryOperator::LessThan,
            left_value: Box::new(Expression::VariableReference("i".to_string())),
            right_value: Box::new(BigDecimal::from(3).into()),
        };
        let increment = Expression::Assignment(
            "i".to_string(),
            Box::new(Expression::Binary {
                operator: BinaryOperator::Add,
                left_value: Box::new(Expression::VariableReference("i".to_string())),
                right_value: Box::new(BigDecimal::one().into()),
            }),
        );
        let block = Block(vec![
            Statement::Expression(Expression::Assignment(
                "j".to_string(),
                Box::new(Expression::Binary {
                    operator: BinaryOperator::Add,
                    left_value: Box::new(Expression::VariableReference("j".to_string())),
                    right_value: Box::new(Expression::Literal(Literal::Number(
                        BigDecimal::one().into(),
                    ))),
                }),
            )),
            If {
                condition: Expression::Binary {
                    operator: BinaryOperator::GreaterThanOrEqual,
                    left_value: Box::new(Expression::VariableReference("j".to_string())),
                    right_value: Box::new(Expression::Literal(Literal::Number(
                        BigDecimal::from(3).into(),
                    ))),
                },
                then_branch: Box::new(Break),
                else_branch: None,
            },
            Continue,
            Print(Expression::Literal(Literal::String(
                "Don't print me".to_string(),
            ))),
        ]);
        let for_loop = For {
            initializer: None,
            condition: Some(condition),
            increment: Some(increment),
            statement: Box::new(block),
        };

        // when
        for_loop
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute for loop");

        // then
        assert_eq!(
            environment.borrow().get("i").expect("variable missing"),
            EvaluationResult::Number(BigDecimal::from(2).into())
        );
        assert_eq!(
            environment.borrow().get("j").expect("variable missing"),
            EvaluationResult::Number(BigDecimal::from(3).into())
        );
        assert!(side_effects.borrow().lines.is_empty());
    }
    #[test]
    fn define_function() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let function_declaration = Function {
            name: "print_value".to_string(),
            parameter_names: vec!["x".to_string()],
            statements: vec![Print(Expression::VariableReference("x".to_string()))],
        };

        // when
        function_declaration
            .execute(environment.clone(), side_effects.clone())
            .expect("Unable to execute function definition");

        // then
        let function = environment
            .borrow()
            .get("print_value")
            .expect("Function not defined in environment");

        assert!(matches!(
            function,
            EvaluationResult::Function(
                Callables::UserDefinedFunction(
                    FunctionDefinition {
                        name,
                        parameter_names,
                        statements
                    }
                )
            )
            if name == "print_value"
                && parameter_names.len() == 1
                && statements.len() == 1
                && parameter_names[0] == "x"
                && matches!(
                    &statements[0],
                    Print(Expression::VariableReference(parameter_name))
                    if parameter_name == "x"
                )
        ))
    }

    #[test]
    fn cannot_define_function_if_name_taken() {
        // given
        let globals = Rc::new(RefCell::new(Environment::default()));
        let environment = Rc::new(RefCell::new(Environment::new_nested_scope(globals.clone())));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        environment
            .borrow_mut()
            .define(
                "foo".to_string(),
                EvaluationResult::String("bar".to_string()),
            )
            .expect("Unable to define variable");

        let function_definition = Function {
            name: "foo".to_string(),
            parameter_names: vec![],
            statements: vec![],
        };

        // when
        let result = function_definition
            .execute(environment, side_effects)
            .expect_err("Expected evaluation error");

        // then
        assert!(matches!(result, EvaluationError::CannotRedefineVariable(_)))
    }

    #[test]
    fn evaluation_error_propagates() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let statement = Statement::Expression(Expression::Binary {
            operator: BinaryOperator::Divide,
            left_value: Box::new(Expression::Literal(Literal::Number(1.into()))),
            right_value: Box::new(Expression::Literal(Literal::Number(0.into()))),
        });

        // when
        let result = statement
            .execute(environment, side_effects)
            .expect_err("Expected error");

        // then
        assert!(matches!(result, EvaluationError::DivideByZero));
    }

    #[derive(Default, Clone)]
    struct TestSideEffects {
        lines: Vec<String>,
    }

    impl SideEffects for TestSideEffects {
        fn println(&mut self, text: &str) {
            self.lines.push(text.to_string());
        }

        fn eprintln(&mut self, text: &str) {
            eprintln!("{}", text);
        }
    }

    impl From<u8> for Expression {
        fn from(value: u8) -> Self {
            BigDecimal::from(value).into()
        }
    }
}
