use crate::environment::Environment;
use bigdecimal::{BigDecimal, Zero};
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::str::FromStr;
use EvaluationError::{DivideByZero, NilValue, TypeMismatch, Undefined};

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

impl Display for EvaluationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeMismatch => write!(f, "TypeMismatch"),
            NilValue => write!(f, "Attempted to use nil value"),
            DivideByZero => write!(f, "Attempted to divide by zero"),
            Undefined => write!(f, "Expression refers to an undefined variable"),
        }
    }
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
    pub fn is_truthful(&self) -> bool {
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
    use super::{EvaluationError, EvaluationResult, Expression, UnaryOperator};
    use crate::environment::Environment;
    use bigdecimal::{BigDecimal, FromPrimitive, One, Zero};
    use std::ops::{Neg, Sub};
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
}
