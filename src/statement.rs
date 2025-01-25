use crate::environment::{Environment, ExistsError};
use crate::grammar::{EvaluationError, EvaluationResult, Expression};
use crate::side_effects::SideEffects;
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

    /// A conditional or branching control flow
    If {
        condition: Expression,
        then_branch: Box<Statement>,
        else_branch: Option<Box<Statement>>,
    },

    /// Evaluates an expression and outputs the result
    Print(Expression),

    /// A variable declaration with optional definition
    VariableDeclaration {
        identifier: String,
        /// If None, this is a variable declaration without assignment
        expression: Option<Expression>,
    },

    Block(Vec<Statement>),
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
                    .map_err(ExecutionError::Evaluation)?;
                Ok(())
            }
            Self::Print(value) => {
                let result = value
                    .evaluate(&mut environment.borrow_mut())
                    .map_err(ExecutionError::Evaluation)?;

                side_effects.borrow_mut().println(&format!("{}", result));

                Ok(())
            }
            Self::VariableDeclaration {
                identifier,
                expression,
            } => {
                let result = expression
                    .clone() // TODO can we avoid cloning?
                    .map(|e| e.evaluate(&mut environment.borrow_mut()))
                    .unwrap_or(Ok(EvaluationResult::Nil))
                    .map_err(ExecutionError::Evaluation)?;

                environment
                    .borrow_mut()
                    .define(identifier.clone(), result)
                    .map_err(ExecutionError::CannotRedefineVariable)?;

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
            Statement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                if condition
                    .evaluate(&mut environment.borrow_mut())
                    .map_err(ExecutionError::Evaluation)?
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
    use super::{ExecutionError, Statement};
    use crate::environment::Environment;
    use crate::grammar::BinaryOperator::Add;
    use crate::grammar::{EvaluationError, EvaluationResult, Expression};
    use crate::side_effects::{SideEffects, StandardSideEffects};
    use bigdecimal::{BigDecimal, One};
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
        let variable_definition = Statement::VariableDeclaration {
            identifier: "beverage".to_string(),
            expression: Some("espresso".to_string().into()),
        };
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

        let initial_definition = Statement::VariableDeclaration {
            identifier: "a".to_string(),
            expression: Some("before".to_string().into()),
        };
        let subsequent_definition = Statement::VariableDeclaration {
            identifier: "a".to_string(),
            expression: Some("after".to_string().into()),
        };
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

        let declaration = Statement::VariableDeclaration {
            identifier: "a".to_string(),
            expression: None,
        };
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

        let define_a = Statement::VariableDeclaration {
            identifier: "a".to_string(),
            expression: Some(BigDecimal::one().into()),
        };
        let define_b = Statement::VariableDeclaration {
            identifier: "b".to_string(),
            expression: Some(BigDecimal::from(2).into()),
        };
        let print_statement = Statement::Print(Expression::Binary {
            operator: Add,
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

        let define_a = Statement::VariableDeclaration {
            identifier: "a".to_string(),
            expression: Some(BigDecimal::one().into()),
        };
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
}
