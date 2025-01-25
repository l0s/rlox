use crate::environment::{Environment, ExistsError};
use crate::side_effects::SideEffects;
use bigdecimal::{BigDecimal, Zero};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::rc::Rc;
use std::str::FromStr;
use EvaluationError::{DivideByZero, NilValue, TypeMismatch, Undefined};

#[derive(Clone, Debug)]
pub(crate) struct Program {
    statements: Vec<Statement>,
}

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

/// An expression evaluates to a value
#[derive(Clone, Eq, PartialEq)]
pub(crate) enum Expression {
    Literal(Literal),
    Logical {
        operator: BinaryOperator,
        left_value: Box<Expression>,
        right_value: Box<Expression>,
    },
    Unary(UnaryOperator, Box<Expression>),
    Binary {
        operator: BinaryOperator,
        left_value: Box<Expression>,
        right_value: Box<Expression>,
    },
    Grouping(Box<Expression>),
    VariableReference(String),
    /// Assign a new value to an existing variable
    Assignment(String, Box<Expression>),
}

impl Expression {
    pub fn evaluate(
        &self,
        environment: &mut Environment,
    ) -> Result<EvaluationResult, EvaluationError> {
        match self {
            Expression::Literal(literal) => Ok(literal.clone().into()),
            Expression::Logical {
                operator,
                left_value,
                right_value,
            } => operator.evaluate(environment, left_value, right_value),
            Expression::Unary(operator, operand) => operator.evaluate(environment, operand),
            Expression::Binary {
                operator,
                left_value,
                right_value,
            } => operator.evaluate(environment, left_value, right_value),
            Expression::Grouping(expression) => expression.evaluate(environment),
            Expression::VariableReference(name) => {
                if let Ok(value) = environment.get(name) {
                    Ok(value)
                } else {
                    Err(Undefined)
                }
            }
            Expression::Assignment(identifier, expression) => {
                let result = expression.evaluate(environment)?;
                environment
                    .assign(identifier.clone(), result.clone())
                    .map_err(|_| Undefined)?;
                Ok(result)
            }
        }
    }
}

impl Debug for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Literal(literal) => match literal {
                Literal::Number(number) => f.write_str(&number.to_string()),
                Literal::String(string) => f.write_str(string),
                Literal::True => f.write_str("true"),
                Literal::False => f.write_str("false"),
                Literal::Nil => f.write_str("nil"),
            },
            Self::Logical {
                operator,
                left_value,
                right_value,
            } => match operator {
                BinaryOperator::And => {
                    write!(f, "( AND {:?} {:?} )", left_value, right_value)
                }
                BinaryOperator::Or => {
                    write!(f, "( OR {:?} {:?} )", left_value, right_value)
                }
                _ => {
                    write!(f, "(Invalid Logical Operator {:?})", operator)
                }
            },
            Self::Unary(operator, expression) => match operator {
                UnaryOperator::Negative => write!(f, "(- {:?})", expression),
                UnaryOperator::Not => write!(f, "(! {:?})", expression),
            },
            Self::Binary {
                operator,
                left_value,
                right_value,
            } => {
                let symbol = match operator {
                    BinaryOperator::Equal => "==",
                    BinaryOperator::NotEqual => "!=",
                    BinaryOperator::LessThan => "<",
                    BinaryOperator::GreaterThan => ">",
                    BinaryOperator::LessThanOrEqual => "<=",
                    BinaryOperator::GreaterThanOrEqual => ">=",
                    BinaryOperator::Add => "+",
                    BinaryOperator::Subtract => "-",
                    BinaryOperator::Multiply => "*",
                    BinaryOperator::Divide => "/",
                    BinaryOperator::And => "AND",
                    BinaryOperator::Or => "OR",
                };
                write!(f, "({} {:?} {:?})", symbol, left_value, right_value)
            }
            Self::Grouping(expression) => write!(f, "(group {:?})", expression),
            Self::VariableReference(name) => write!(f, "(var {})", name),
            Self::Assignment(identifier, expression) => {
                write!(f, "(set {} {:?})", identifier, expression)
            }
        }
    }
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum EvaluationError {
    TypeMismatch,
    NilValue,
    DivideByZero,
    /// The expression refers to an undefined variable
    Undefined,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum BinaryOperator {
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    Add,
    Subtract,
    Multiply,
    Divide,
    /// Conjunction
    And,
    /// Disjunction
    Or,
}

impl BinaryOperator {
    pub fn evaluate(
        &self,
        environment: &mut Environment,
        left_value: &Expression,
        right_value: &Expression,
    ) -> Result<EvaluationResult, EvaluationError> {
        match self {
            BinaryOperator::Equal => Ok(EvaluationResult::Boolean(
                left_value.evaluate(environment)? == right_value.evaluate(environment)?,
            )),
            BinaryOperator::NotEqual => Ok(EvaluationResult::Boolean(
                left_value.evaluate(environment)? != right_value.evaluate(environment)?,
            )),
            BinaryOperator::LessThan => {
                Self::evaluate_inequality(environment, left_value, right_value, &[Ordering::Less])
            }
            BinaryOperator::GreaterThan => Self::evaluate_inequality(
                environment,
                left_value,
                right_value,
                &[Ordering::Greater],
            ),
            BinaryOperator::LessThanOrEqual => Self::evaluate_inequality(
                environment,
                left_value,
                right_value,
                &[Ordering::Less, Ordering::Equal],
            ),
            BinaryOperator::GreaterThanOrEqual => Self::evaluate_inequality(
                environment,
                left_value,
                right_value,
                &[Ordering::Greater, Ordering::Equal],
            ),
            BinaryOperator::Add => {
                let left = left_value.evaluate(environment)?;
                let right = right_value.evaluate(environment)?;
                fn as_string(evaluation_result: &EvaluationResult) -> String {
                    // Note: this logic differs from `Display`
                    match evaluation_result {
                        EvaluationResult::Number(value) => value.to_engineering_notation(),
                        EvaluationResult::String(value) => value.to_string(),
                        EvaluationResult::Boolean(value) => value.to_string(),
                        EvaluationResult::Nil => "".to_string(),
                    }
                }
                match (left, right) {
                    // If both numbers, perform addition
                    (EvaluationResult::Number(x), EvaluationResult::Number(y)) => {
                        Ok(EvaluationResult::Number(x.add(y)))
                    }
                    // If either is a string, concatenate
                    (EvaluationResult::String(prefix), suffix) => Ok(EvaluationResult::String(
                        format!("{}{}", prefix, as_string(&suffix)),
                    )),
                    (prefix, EvaluationResult::String(suffix)) => Ok(EvaluationResult::String(
                        format!("{}{}", as_string(&prefix), suffix),
                    )),
                    (EvaluationResult::Nil, _) | (_, EvaluationResult::Nil) => Err(NilValue),
                    (_, _) => Err(TypeMismatch),
                }
            }
            BinaryOperator::Subtract => {
                Self::perform_arithmetic(environment, left_value, right_value, |x, y| x.sub(y))
            }
            BinaryOperator::Multiply => {
                Self::perform_arithmetic(environment, left_value, right_value, |x, y| x.mul(y))
            }
            BinaryOperator::Divide => {
                let left = left_value.evaluate(environment)?;
                let right = right_value.evaluate(environment)?;
                match (left, right) {
                    (
                        EvaluationResult::Number(numerator),
                        EvaluationResult::Number(denominator),
                    ) => {
                        if denominator == BigDecimal::zero() {
                            Err(DivideByZero)
                        } else {
                            Ok(EvaluationResult::Number(numerator.div(denominator)))
                        }
                    }
                    (EvaluationResult::Nil, _) | (_, EvaluationResult::Nil) => Err(NilValue),
                    (_, _) => Err(TypeMismatch),
                }
            }
            BinaryOperator::And => {
                let left = left_value.evaluate(environment)?;
                if !left.is_truthful() {
                    Ok(left)
                } else {
                    Ok(right_value.evaluate(environment)?)
                }
            }
            BinaryOperator::Or => {
                let left = left_value.evaluate(environment)?;
                if left.is_truthful() {
                    Ok(left)
                } else {
                    Ok(right_value.evaluate(environment)?)
                }
            }
        }
    }

    fn perform_arithmetic(
        environment: &mut Environment,
        left_value: &Expression,
        right_value: &Expression,
        operation: fn(BigDecimal, BigDecimal) -> BigDecimal,
    ) -> Result<EvaluationResult, EvaluationError> {
        let left = left_value.evaluate(environment)?;
        let right = right_value.evaluate(environment)?;
        match (left, right) {
            (EvaluationResult::Number(x), EvaluationResult::Number(y)) => {
                Ok(EvaluationResult::Number(operation(x, y)))
            }
            (EvaluationResult::Nil, _) | (_, EvaluationResult::Nil) => Err(NilValue),
            (_, _) => Err(TypeMismatch),
        }
    }

    fn evaluate_inequality(
        environment: &mut Environment,
        left_value: &Expression,
        right_value: &Expression,
        expected: &[Ordering],
    ) -> Result<EvaluationResult, EvaluationError> {
        match (
            left_value.evaluate(environment)?,
            right_value.evaluate(environment)?,
        ) {
            // TODO will this fail early (short circuit) if one of these is NaN?
            (EvaluationResult::Number(x), EvaluationResult::Number(y)) => {
                Ok(EvaluationResult::Boolean(expected.contains(&x.cmp(&y))))
            }
            (EvaluationResult::Nil, _) | (_, EvaluationResult::Nil) => Err(NilValue),
            (_, _) => Err(TypeMismatch),
        }
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub(crate) enum UnaryOperator {
    Negative,
    Not,
}

impl UnaryOperator {
    pub fn evaluate(
        &self,
        environment: &mut Environment,
        input: &Expression,
    ) -> Result<EvaluationResult, EvaluationError> {
        match self {
            UnaryOperator::Negative => {
                let operand = input.evaluate(environment)?;
                if let EvaluationResult::Number(operand) = operand {
                    Ok(EvaluationResult::Number(operand.neg()))
                } else {
                    Err(TypeMismatch)
                }
            }
            UnaryOperator::Not => {
                let operand = input.evaluate(environment)?;
                Ok(EvaluationResult::Boolean(!operand.is_truthful()))
            }
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) enum Literal {
    Number(BigDecimal),
    String(String),
    True,
    False,
    Nil,
}

impl From<Literal> for EvaluationResult {
    fn from(value: Literal) -> Self {
        match value {
            Literal::Number(value) => EvaluationResult::Number(value),
            Literal::String(value) => EvaluationResult::String(value),
            Literal::True => EvaluationResult::Boolean(true),
            Literal::False => EvaluationResult::Boolean(false),
            Literal::Nil => EvaluationResult::Nil,
        }
    }
}

impl FromStr for Literal {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::String(s.to_string()))
    }
}

impl FromStr for Expression {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::Literal(s.parse()?))
    }
}

impl From<String> for Literal {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<String> for Expression {
    fn from(value: String) -> Self {
        Self::Literal(value.into())
    }
}

impl From<BigDecimal> for Literal {
    fn from(value: BigDecimal) -> Self {
        Self::Number(value)
    }
}

impl From<BigDecimal> for Expression {
    fn from(value: BigDecimal) -> Self {
        Self::Literal(value.into())
    }
}

impl From<bool> for Literal {
    fn from(value: bool) -> Self {
        if value {
            Self::True
        } else {
            Self::False
        }
    }
}

impl From<bool> for Expression {
    fn from(value: bool) -> Self {
        Self::Literal(value.into())
    }
}

impl From<Literal> for Expression {
    fn from(value: Literal) -> Self {
        Self::Literal(value)
    }
}

#[derive(Eq, PartialEq, Debug, Clone)]
pub(crate) enum EvaluationResult {
    Number(BigDecimal),
    String(String),
    Boolean(bool),
    Nil,
}

impl Display for EvaluationResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(value) => value.write_engineering_notation(f),
            Self::String(value) => f.write_str(value),
            Self::Boolean(value) => write!(f, "{}", value),
            Self::Nil => f.write_str("nil"),
        }
    }
}

impl EvaluationResult {
    fn is_truthful(&self) -> bool {
        match self {
            EvaluationResult::Number(_) => true,
            EvaluationResult::String(_) => true,
            EvaluationResult::Boolean(value) => *value,
            EvaluationResult::Nil => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::BinaryOperator::{
        Add, Divide, Equal, GreaterThan, GreaterThanOrEqual, LessThan, LessThanOrEqual, Multiply,
        NotEqual, Subtract,
    };
    use super::EvaluationError::{DivideByZero, NilValue, TypeMismatch};
    use super::Literal::Nil;
    use super::{
        EvaluationError, EvaluationResult, ExecutionError, Expression, Statement, UnaryOperator,
    };
    use crate::environment::Environment;
    use crate::side_effects::{SideEffects, StandardSideEffects};
    use bigdecimal::{BigDecimal, FromPrimitive, One, Zero};
    use std::cell::RefCell;
    use std::ops::{Neg, Sub};
    use std::rc::Rc;
    use std::str::FromStr;

    #[test]
    fn ast_prefix_printer() {
        // given
        let ast = Expression::Binary {
            operator: Multiply,
            left_value: Box::new(Expression::Unary(
                UnaryOperator::Negative,
                Box::new(BigDecimal::from_str("123").unwrap().into()),
            )),
            right_value: Box::new(Expression::Grouping(Box::new(
                BigDecimal::from_str("45.67").unwrap().into(),
            ))),
        };

        // when
        let result = format!("{:?}", ast);

        // then
        assert_eq!(result, "(* (- 123) (group 45.67))".to_string());
    }

    fn successful_evaluation_test(expression: &Expression, expected: &EvaluationResult) {
        // given
        let mut environment = Environment::default();

        // when
        let result = expression.evaluate(&mut environment).unwrap();

        // then
        assert_eq!(
            result, *expected,
            "expression {:?} did not yield result: {:?}",
            expression, expected
        );
    }

    fn unsuccessful_evaluation_test(expression: &Expression, expected: &EvaluationError) {
        // given
        let mut environment = Environment::default();

        // when
        let result = expression.evaluate(&mut environment).unwrap_err();

        // then
        assert_eq!(
            result, *expected,
            "expression {:?} did not yield error: {:?}",
            expression, expected
        );
    }

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

    macro_rules! successful_evaluation_tests {
        ($($name:ident: $value:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let (expression, expected) = $value;
                successful_evaluation_test(&expression, &expected);
            }
        )*
        }
    }

    successful_evaluation_tests! {
        number_literal: (BigDecimal::from_str("2.718281828").unwrap().into(), EvaluationResult::Number(BigDecimal::from_str("2.718281828").unwrap())),
        string_literal: ("🎄".to_string().into(), EvaluationResult::String("🎄".to_string())),
        pi_less_than_tau: (
            Expression::Binary {
                operator: LessThan,
                left_value: Box::new(BigDecimal::from_str("3.14159").unwrap().into()),
                right_value: Box::new(BigDecimal::from_str("6.283185307179586").unwrap().into()),
            },
            EvaluationResult::Boolean(true),
        ),
        pi_lte_tau: (
            Expression::Binary {
                operator: LessThanOrEqual,
                left_value: Box::new(BigDecimal::from_str("3.14159").unwrap().into()),
                right_value: Box::new(BigDecimal::from_str("6.283185307179586").unwrap().into()),
            },
            EvaluationResult::Boolean(true),
        ),
        tau_greater_than_pi: (
            Expression::Binary {
                operator: GreaterThan,
                left_value: Box::new(BigDecimal::from_str("6.283185307179586").unwrap().into()),
                right_value: Box::new(BigDecimal::from_str("3.14159").unwrap().into()),
            },
            EvaluationResult::Boolean(true),
        ),
        tau_gte_pi: (
            Expression::Binary {
                operator: GreaterThanOrEqual,
                left_value: Box::new(BigDecimal::from_str("6.283185307179586").unwrap().into()),
                right_value: Box::new(BigDecimal::from_str("3.14159").unwrap().into()),
            },
            EvaluationResult::Boolean(true),
        ),
        e_equals_e: (
            Expression::Binary {
                operator: Equal,
                left_value: Box::new(BigDecimal::from_f64(std::f64::consts::E).unwrap().into()),
                right_value: Box::new(BigDecimal::from_f64(std::f64::consts::E).unwrap().into()),
            },
            EvaluationResult::Boolean(true),
        ),
        e_lte_e: (
            Expression::Binary {
                operator: LessThanOrEqual,
                left_value: Box::new(BigDecimal::from_f64(std::f64::consts::E).unwrap().into()),
                right_value: Box::new(BigDecimal::from_f64(std::f64::consts::E).unwrap().into()),
            },
            EvaluationResult::Boolean(true),
        ),
        e_gte_e: (
            Expression::Binary {
                operator: GreaterThanOrEqual,
                left_value: Box::new(BigDecimal::from_f64(std::f64::consts::E).unwrap().into()),
                right_value: Box::new(BigDecimal::from_f64(std::f64::consts::E).unwrap().into()),
            },
            EvaluationResult::Boolean(true),
        ),
        number_inequality: (
            Expression::Binary {
                operator: NotEqual,
                left_value: Box::new(BigDecimal::from_f64(std::f64::consts::LN_2).unwrap().into()),
                right_value: Box::new(BigDecimal::from_f64(std::f64::consts::SQRT_2).unwrap().into()),
            },
            EvaluationResult::Boolean(true),
        ),
        string_not_equal_to_number: (
            Expression::Binary {
                operator: Equal,
                left_value: Box::new("🥧".to_string().into()),
                right_value: Box::new(BigDecimal::from_str("3.14159").unwrap().into()),
            },
            EvaluationResult::Boolean(false),
        ),
        string_equality: (
            Expression::Binary {
                operator: Equal,
                left_value: Box::new("🐺".to_string().into()),
                right_value: Box::new("🐺".to_string().into()),
            },
            EvaluationResult::Boolean(true),
        ),
        string_inequality: (
            Expression::Binary {
                operator: NotEqual,
                left_value: Box::new("🦑".to_string().into()),
                right_value: Box::new("🐙".to_string().into()),
            },
            EvaluationResult::Boolean(true),
        ),
        boolean_equality: (
            Expression::Binary {
                operator: Equal,
                left_value: Box::new(false.into()),
                right_value: Box::new(false.into()),
            },
            EvaluationResult::Boolean(true),
        ),
        boolean_inequality: (
            Expression::Binary {
                operator: NotEqual,
                left_value: Box::new(true.into()),
                right_value: Box::new(false.into()),
            },
            EvaluationResult::Boolean(true),
        ),
        string_concatenation: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new("😒".to_string().into()),
                right_value: Box::new("😥".to_string().into()),
            },
            EvaluationResult::String("😒😥".to_string()),
        ),
        nil_is_falsey: (
            Expression::Unary(UnaryOperator::Not, Box::new(Expression::Literal(Nil))),
            EvaluationResult::Boolean(true),
        ),
        zero_is_truthy: (
            Expression::Unary(UnaryOperator::Not, Box::new(BigDecimal::zero().into())),
            EvaluationResult::Boolean(false),
        ),
        one_is_truthy: (
            Expression::Unary(UnaryOperator::Not, Box::new(BigDecimal::one().into())),
            EvaluationResult::Boolean(false),
        ),
        string_is_truthy: (
            Expression::Unary(UnaryOperator::Not, Box::new("🥯".to_string().into())),
            EvaluationResult::Boolean(false),
        ),
        concatenate_boolean_and_string: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new(true.into()),
                right_value: Box::new("🥐".to_string().into()),
            },
            EvaluationResult::String("true🥐".to_string()),
        ),
        concatenate_string_and_boolean: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new("🥐".to_string().into()),
                right_value: Box::new(false.into()),
            },
            EvaluationResult::String("🥐false".to_string()),
        ),
        concatenate_number_and_string: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new(BigDecimal::from(4).into()),
                right_value: Box::new("🥐".to_string().into()),
            },
            EvaluationResult::String("4e0🥐".to_string()),
        ),
        concatenate_string_and_number: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new("🥐".to_string().into()),
                right_value: Box::new(BigDecimal::from(4).into()),
            },
            EvaluationResult::String("🥐4e0".to_string()),
        ),
        concatenate_nil_and_string: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new(Nil.into()),
                right_value: Box::new("🥐".to_string().into()),
            },
            EvaluationResult::String("🥐".to_string()),
        ),
        concatenate_string_and_nil: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new("🥐".to_string().into()),
                right_value: Box::new(Nil.into()),
            },
            EvaluationResult::String("🥐".to_string()),
        ),
        negate_positive: (
            Expression::Unary(UnaryOperator::Negative, Box::new(BigDecimal::one().into())),
            EvaluationResult::Number(BigDecimal::one().neg().into()),
        ),
        negate_negative: (
            Expression::Unary(UnaryOperator::Negative, Box::new(BigDecimal::one().neg().into())),
            EvaluationResult::Number(BigDecimal::one().into()),
        ),
    }

    macro_rules! unsuccessful_evaluation_tests {
        ($($name:ident: $value:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let (expression, expected) = $value;
                unsuccessful_evaluation_test(&expression, &expected);
            }
        )*
        }
    }

    unsuccessful_evaluation_tests! {
        divide_by_zero: (
            Expression::Binary {
                operator: Divide,
                left_value: Box::new(BigDecimal::one().into()),
                right_value: Box::new(BigDecimal::zero().into()),
            },
            DivideByZero,
        ),
        unexpected_nil: (
            Expression::Binary {
                operator: Multiply,
                left_value: Box::new(BigDecimal::one().into()),
                right_value: Box::new(Expression::Literal(Nil)),
            },
            NilValue,
        ),
        type_mismatch: (
            Expression::Binary {
                operator: LessThan,
                left_value: Box::new(BigDecimal::from_str("3.14159").unwrap().into()),
                right_value: Box::new("🥧".to_string().into()),
            },
            TypeMismatch,
        ),
        cannot_negate_cupcake: (
            Expression::Binary {
                operator: Multiply,
                left_value: Box::new(BigDecimal::from_str("2").unwrap().into()),
                right_value: Box::new(Expression::Grouping(Box::new(Expression::Binary {
                    operator: Divide,
                    left_value: Box::new(BigDecimal::from_str("3").unwrap().into()),
                    right_value: Box::new(Expression::Unary(UnaryOperator::Negative, Box::new("🧁".to_string().into()))),
                })))
            },
            TypeMismatch,
        ),
        cannot_concatenate_nils: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new(Nil.into()),
                right_value: Box::new(Nil.into()),
            },
            NilValue,
        ),
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
    fn addition() {
        // given
        let mut environment = Environment::default();
        let expression = Expression::Binary {
            operator: Add,
            left_value: Box::new(BigDecimal::from_f64(std::f64::consts::PI).unwrap().into()),
            right_value: Box::new(BigDecimal::from_f64(std::f64::consts::PI).unwrap().into()),
        };

        // when
        let result = expression
            .evaluate(&mut environment)
            .expect("unable to evaluate addition expression");

        // then
        assert!(matches!(
            result,
            EvaluationResult::Number(number)
            if number.clone().sub(BigDecimal::from_f64(std::f64::consts::TAU).unwrap()).abs() < BigDecimal::from_f64(0.0000000001).unwrap()
        ))
    }

    #[test]
    fn subtraction() {
        // given
        let mut environment = Environment::default();
        let expression = Expression::Binary {
            operator: Subtract,
            left_value: Box::new(BigDecimal::from_f64(std::f64::consts::TAU).unwrap().into()),
            right_value: Box::new(BigDecimal::from_f64(std::f64::consts::PI).unwrap().into()),
        };

        // when
        let result = expression
            .evaluate(&mut environment)
            .expect("unable to evaluate subtraction expression");

        // then
        assert!(matches!(
            result,
            EvaluationResult::Number(number)
            if number.clone().sub(BigDecimal::from_f64(std::f64::consts::PI).unwrap()).abs() < BigDecimal::from_f64(0.0000000001).unwrap()
        ))
    }

    #[test]
    fn multiplication() {
        // given
        let mut environment = Environment::default();
        let expression = Expression::Binary {
            operator: Multiply,
            left_value: Box::new(BigDecimal::from(2).into()),
            right_value: Box::new(BigDecimal::from_f64(std::f64::consts::PI).unwrap().into()),
        };

        // when
        let result = expression
            .evaluate(&mut environment)
            .expect("unable to evaluate multiplication expression");

        // then
        assert!(matches!(
            result,
            EvaluationResult::Number(number)
            if number.clone().sub(BigDecimal::from_f64(std::f64::consts::TAU).unwrap()).abs() < BigDecimal::from_f64(0.0000000001).unwrap()
        ))
    }

    #[test]
    fn division() {
        // given
        let mut environment = Environment::default();
        let expression = Expression::Binary {
            operator: Divide,
            left_value: Box::new(BigDecimal::from_f64(std::f64::consts::TAU).unwrap().into()),
            right_value: Box::new(BigDecimal::from(2).into()),
        };

        // when
        let result = expression
            .evaluate(&mut environment)
            .expect("unable to evaluate division expression");

        // then
        assert!(matches!(
            result,
            EvaluationResult::Number(number)
            if number.clone().sub(BigDecimal::from_f64(std::f64::consts::PI).unwrap()).abs() < BigDecimal::from_f64(0.0000000001).unwrap()
        ))
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
        let mut side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

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
