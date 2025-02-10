use crate::environment::{Environment, ExistsError, LoopControl, NotInALoopError};
use crate::grammar::{EvaluationError, EvaluationResult, Expression};
use crate::side_effects::SideEffects;
use either::Either;
use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
use ExecutionError::{CannotRedefineVariable, Evaluation, NotInALoop};

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
    /// Attempted to use a `break` or `continue` statement outside the context of a loop.
    NotInALoop(NotInALoopError),
}

impl Display for ExecutionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Evaluation(e) => write!(f, "Evaluation error: {}", e),
            CannotRedefineVariable(e) => write!(f, "Cannot redefine variable: {}", e),
            // FIXME Display dependent on Debug
            NotInALoop(e) => write!(
                f,
                "Encountered `break` or `continue` outside a loop: {:?}",
                e
            ),
        }
    }
}

impl Statement {
    pub fn execute<S: SideEffects>(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<S>>,
    ) -> Result<(), ExecutionError> {
        match self {
            Self::Expression(expression) => self.execute_expression(environment, expression),
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
            Self::Print(value) => self.execute_print(environment, side_effects, value),
            Self::VariableDeclaration(declaration) => declaration.execute(environment),
            Self::While(condition, statement) => {
                self.execute_while_loop(environment, side_effects, condition, statement.as_ref())
            }
            Self::Block(statements) => {
                let child = Rc::new(RefCell::new(Environment::new_nested_scope(
                    environment.clone(),
                )));
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
            Statement::Break => environment.borrow_mut().exit_loop().map_err(NotInALoop),
            Statement::Continue => environment
                .borrow_mut()
                .jump_to_next_loop_iteration()
                .map_err(NotInALoop),
        }
    }

    fn execute_expression(
        &self,
        environment: Rc<RefCell<Environment>>,
        expression: &Expression,
    ) -> Result<(), ExecutionError> {
        expression
            .evaluate(&mut environment.borrow_mut())
            .map_err(Evaluation)?;
        Ok(())
    }

    fn execute_for_loop<S: SideEffects>(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<S>>,
        initializer: &Option<Either<VariableDeclarationStatement, Expression>>,
        condition: &Option<Expression>,
        increment: &Option<Expression>,
        statement: Box<Statement>,
    ) -> Result<(), ExecutionError> {
        // For loops get their own scope
        let loop_control = Rc::new(RefCell::new(LoopControl::default()));
        let environment = Rc::new(RefCell::new(Environment::new_nested_loop_scope(
            environment.clone(),
            loop_control.clone(),
        )));
        match initializer {
            Some(Either::Left(declaration)) => {
                declaration.execute(environment.clone())?;
            }
            Some(Either::Right(expression)) => {
                expression
                    .evaluate(&mut environment.borrow_mut())
                    .map_err(Evaluation)?;
            }
            None => {}
        }

        let evaluate_condition = || -> Result<bool, ExecutionError> {
            Ok(if let Some(condition) = condition {
                condition
                    .evaluate(&mut environment.borrow_mut())
                    .map_err(Evaluation)?
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
            if loop_control.borrow().exit_loop {
                break;
            } else if loop_control.borrow().jump_to_next_iteration {
                loop_control.borrow_mut().jump_to_next_iteration = false;
            }
            if let Some(increment) = increment {
                increment
                    .evaluate(&mut environment.borrow_mut())
                    .map_err(Evaluation)?;
            }
        }

        Ok(())
    }

    fn execute_print<S: SideEffects>(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<S>>,
        value: &Expression,
    ) -> Result<(), ExecutionError> {
        let result = value
            .evaluate(&mut environment.borrow_mut())
            .map_err(Evaluation)?;

        side_effects.borrow_mut().println(&format!("{}", result));

        Ok(())
    }

    fn execute_while_loop<S: SideEffects>(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<S>>,
        condition: &Expression,
        statement: &Statement,
    ) -> Result<(), ExecutionError> {
        let loop_control = Rc::new(RefCell::new(LoopControl::default()));
        let environment = Rc::new(RefCell::new(Environment::new_nested_loop_scope(
            environment.clone(),
            loop_control.clone(),
        )));
        while condition
            .evaluate(&mut environment.borrow_mut())
            .map_err(Evaluation)?
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

    fn execute_block<S: SideEffects>(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<S>>,
        statements: &[Statement],
    ) -> Result<(), ExecutionError> {
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

    fn execute_if_statement<S: SideEffects>(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<S>>,
        condition: &Expression,
        then_branch: &Statement,
        else_branch: Option<Box<Statement>>,
    ) -> Result<(), ExecutionError> {
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

#[cfg(test)]
mod tests {
    use super::Statement::{Block, Break, Continue, For, Print};
    use super::{ExecutionError, Statement, VariableDeclarationStatement};
    use crate::environment::{Environment, NotInALoopError};
    use crate::grammar::{BinaryOperator, EvaluationError, EvaluationResult, Expression, Literal};
    use crate::side_effects::{SideEffects, StandardSideEffects};
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
            Print(Expression::VariableReference("a".to_string())),
            ExecutionError::Evaluation(EvaluationError::Undefined),
        ),
        assignment_without_declaration: (
            Statement::Expression(Expression::Assignment("a".to_string(), Box::new(BigDecimal::one().into()))),
            ExecutionError::Evaluation(EvaluationError::Undefined),
        ),
        break_outside_loop: (
            Break,
            ExecutionError::NotInALoop(NotInALoopError),
        ),
        continue_outside_loop: (
            Continue,
            ExecutionError::NotInALoop(NotInALoopError),
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
            right_value: Box::new(BigDecimal::from(1_000_000).into()),
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

    #[derive(Default)]
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
