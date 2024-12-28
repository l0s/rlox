use bigdecimal::{BigDecimal, Zero};
use std::fmt::{Debug, Display, Formatter};
use std::ops::Neg;
use std::str::FromStr;
use EvaluationError::{DivideByZero, NilValue, TypeMismatch};

#[derive(Clone, Eq, PartialEq)]
pub(crate) enum Expression {
    Literal(Literal),
    Unary(UnaryOperator, Box<Expression>),
    Binary {
        operator: BinaryOperator,
        left_value: Box<Expression>,
        right_value: Box<Expression>,
    },
    Grouping(Box<Expression>),
}

impl Expression {
    pub fn evaluate(&self) -> Result<EvaluationResult, EvaluationError> {
        match self.result_type() {
            None => Ok(EvaluationResult::Nil),
            Some(data_type) => data_type.evaluate(self),
        }
    }

    pub fn result_type(&self) -> Option<DataType> {
        match self {
            Self::Literal(literal) => match literal {
                Literal::Number(_) => Some(DataType::Number),
                Literal::String(_) => Some(DataType::String),
                Literal::True => Some(DataType::Boolean),
                Literal::False => Some(DataType::Boolean),
                Literal::Nil => None,
            },
            Self::Unary(operator, expression) => operator.result_type(expression.result_type()),
            Self::Binary {
                operator,
                left_value: _left_value,
                right_value: _right_value,
            } => Some(operator.result_type()),
            Self::Grouping(expression) => expression.result_type(),
        }
    }

    pub fn evaluate_boolean(&self) -> Result<bool, EvaluationError> {
        match self {
            Self::Literal(literal) => match literal {
                Literal::Number(_) => Err(TypeMismatch),
                Literal::String(_) => Err(TypeMismatch),
                Literal::True => Ok(true),
                Literal::False => Ok(false),
                Literal::Nil => Err(NilValue),
            },
            Self::Unary(operator, argument) => {
                if *operator == UnaryOperator::Not {
                    argument.evaluate_boolean().map(|result| !result)
                } else {
                    Err(TypeMismatch)
                }
            }
            Self::Binary {
                operator,
                left_value,
                right_value,
            } => operator.evaluate_boolean(left_value, right_value),
            Self::Grouping(expression) => expression.evaluate_boolean(),
        }
    }

    pub fn evaluate_number(&self) -> Result<BigDecimal, EvaluationError> {
        match self {
            Self::Literal(literal) => match literal {
                Literal::Number(number) => Ok(number.clone()),
                Literal::Nil => Err(NilValue),
                _ => Err(TypeMismatch),
            },
            Self::Unary(operator, argument) => {
                if *operator == UnaryOperator::Negative {
                    argument.evaluate_number().map(BigDecimal::neg)
                } else {
                    Err(TypeMismatch)
                }
            }
            Self::Binary {
                operator,
                left_value,
                right_value,
            } => operator.evaluate_number(left_value, right_value),
            Self::Grouping(expression) => expression.evaluate_number(),
        }
    }

    pub fn evaluate_string(&self) -> Result<String, EvaluationError> {
        match self {
            Self::Literal(literal) => match literal {
                Literal::String(value) => Ok(value.clone()),
                Literal::Nil => Err(NilValue),
                _ => Err(TypeMismatch),
            },
            Self::Unary(_, _) => Err(TypeMismatch),
            Self::Binary {
                operator,
                left_value,
                right_value,
            } => operator.evaluate_string(left_value, right_value),
            Self::Grouping(expression) => expression.evaluate_string(),
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
            Self::Unary(operator, expression) => match operator {
                UnaryOperator::Negative => f.write_fmt(format_args!("(- {:?})", expression)),
                UnaryOperator::Not => f.write_fmt(format_args!("(! {:?})", expression)),
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
                };
                f.write_fmt(format_args!(
                    "({} {:?} {:?})",
                    symbol, left_value, right_value
                ))
            }
            Self::Grouping(expression) => f.write_fmt(format_args!("(group {:?})", expression)),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum EvaluationError {
    TypeMismatch,
    NilValue,
    DivideByZero,
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
}

impl BinaryOperator {
    pub fn evaluate_boolean(
        &self,
        left_value: &Expression,
        right_value: &Expression,
    ) -> Result<bool, EvaluationError> {
        match self {
            Self::Equal => {
                match (left_value.result_type(), right_value.result_type()) {
                    (None, None) => Ok(true),
                    (None, Some(_)) | (Some(_), None) => Ok(false),
                    (Some(DataType::String), Some(DataType::String)) => {
                        Ok(left_value.evaluate_string()? == right_value.evaluate_string()?)
                    }
                    (Some(DataType::Number), Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number()? == right_value.evaluate_number()?)
                    }
                    (Some(DataType::Boolean), Some(DataType::Boolean)) => {
                        Ok(left_value.evaluate_boolean()? == right_value.evaluate_boolean()?)
                    }
                    _ => Ok(false), // two different types, cannot be equal to each other
                }
            }
            Self::NotEqual => {
                match (left_value.result_type(), right_value.result_type()) {
                    (None, None) => Ok(false),
                    (None, Some(_)) | (Some(_), None) => Ok(true),
                    (Some(DataType::String), Some(DataType::String)) => {
                        Ok(left_value.evaluate_string()? != right_value.evaluate_string()?)
                    }
                    (Some(DataType::Number), Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number()? != right_value.evaluate_number()?)
                    }
                    (Some(DataType::Boolean), Some(DataType::Boolean)) => {
                        Ok(left_value.evaluate_boolean()? != right_value.evaluate_boolean()?)
                    }
                    _ => Ok(true), // two different types, cannot be equal to each other
                }
            }
            Self::LessThan => {
                match (left_value.result_type(), right_value.result_type()) {
                    (None, _) | (_, None) => Err(NilValue),
                    (Some(DataType::Number), Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number()? < right_value.evaluate_number()?)
                    }
                    (Some(_), Some(_)) => Err(TypeMismatch), // both values must be numbers
                }
            }
            Self::GreaterThan => {
                match (left_value.result_type(), right_value.result_type()) {
                    (None, _) | (_, None) => Err(NilValue),
                    (Some(DataType::Number), Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number()? > right_value.evaluate_number()?)
                    }
                    (Some(_), Some(_)) => Err(TypeMismatch), // both values must be numbers
                }
            }
            Self::LessThanOrEqual => {
                match (left_value.result_type(), right_value.result_type()) {
                    (None, _) | (_, None) => Err(NilValue),
                    (Some(DataType::Number), Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number()? <= right_value.evaluate_number()?)
                    }
                    (Some(_), Some(_)) => Err(TypeMismatch), // both values must be numbers
                }
            }
            Self::GreaterThanOrEqual => {
                match (left_value.result_type(), right_value.result_type()) {
                    (None, _) | (_, None) => Err(NilValue),
                    (Some(DataType::Number), Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number()? >= right_value.evaluate_number()?)
                    }
                    (Some(_), Some(_)) => Err(TypeMismatch), // both values must be numbers
                }
            }
            _ => Err(TypeMismatch),
        }
    }

    pub fn evaluate_number(
        &self,
        left_value: &Expression,
        right_value: &Expression,
    ) -> Result<BigDecimal, EvaluationError> {
        match self {
            Self::Add => Ok(left_value.evaluate_number()? + right_value.evaluate_number()?),
            Self::Subtract => Ok(left_value.evaluate_number()? - right_value.evaluate_number()?),
            Self::Multiply => Ok(left_value.evaluate_number()? * right_value.evaluate_number()?),
            Self::Divide => {
                let right_value = right_value.evaluate_number()?;
                if right_value.is_zero() {
                    Err(DivideByZero)
                } else {
                    Ok(left_value.evaluate_number()? / right_value)
                }
            }
            _ => Err(TypeMismatch),
        }
    }

    pub fn evaluate_string(
        &self,
        _left_value: &Expression,
        _right_value: &Expression,
    ) -> Result<String, EvaluationError> {
        // none of the binary operators produce string results
        Err(TypeMismatch)
    }

    pub fn result_type(&self) -> DataType {
        match self {
            Self::Equal => DataType::Boolean,
            Self::NotEqual => DataType::Boolean,
            Self::LessThan => DataType::Boolean,
            Self::GreaterThan => DataType::Boolean,
            Self::LessThanOrEqual => DataType::Boolean,
            Self::GreaterThanOrEqual => DataType::Boolean,
            Self::Add => DataType::Number,
            Self::Subtract => DataType::Number,
            Self::Multiply => DataType::Number,
            Self::Divide => DataType::Number,
        }
    }
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Equal => f.write_str("Equal"),
            Self::NotEqual => f.write_str("NotEqual"),
            Self::LessThan => f.write_str("LessThan"),
            Self::GreaterThan => f.write_str("GreaterThan"),
            Self::LessThanOrEqual => f.write_str("LessThanOrEqual"),
            Self::GreaterThanOrEqual => f.write_str("GreaterThanOrEqual"),
            Self::Add => f.write_str("Add"),
            Self::Subtract => f.write_str("Subtract"),
            Self::Multiply => f.write_str("Multiply"),
            Self::Divide => f.write_str("Divide"),
        }
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub(crate) enum UnaryOperator {
    Negative,
    Not,
}

impl UnaryOperator {
    pub fn result_type(&self, input_type: Option<DataType>) -> Option<DataType> {
        input_type
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

impl FromStr for Literal {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::String(s.to_string()))
    }
}

impl From<String> for Literal {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<BigDecimal> for Literal {
    fn from(value: BigDecimal) -> Self {
        Self::Number(value)
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

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub(crate) enum DataType {
    Number,
    String,
    Boolean,
}

impl DataType {
    pub fn evaluate(&self, expression: &Expression) -> Result<EvaluationResult, EvaluationError> {
        match self {
            Self::Number => Ok(EvaluationResult::Number(expression.evaluate_number()?)),
            Self::String => Ok(EvaluationResult::String(expression.evaluate_string()?)),
            Self::Boolean => Ok(EvaluationResult::Boolean(expression.evaluate_boolean()?)),
        }
    }
}

#[derive(Eq, PartialEq, Debug, Clone)]
pub(crate) enum EvaluationResult {
    Number(BigDecimal),
    String(String),
    Boolean(bool),
    Nil,
}

#[cfg(test)]
mod tests {
    use super::BinaryOperator::{Divide, Equal, LessThan, Multiply};
    use super::Expression::{Binary, Grouping, Unary};
    use super::Literal::Nil;
    use super::UnaryOperator::Negative;
    use crate::grammar::EvaluationError::{DivideByZero, NilValue, TypeMismatch};
    use crate::grammar::{EvaluationError, EvaluationResult, Expression, Literal};
    use bigdecimal::{BigDecimal, One, Zero};
    use std::str::FromStr;

    #[test]
    fn ast_prefix_printer() {
        // given
        let ast = Binary {
            operator: Multiply,
            left_value: Box::new(Unary(
                Negative,
                Box::new(Expression::Literal(Literal::Number(
                    BigDecimal::from_str("123").unwrap(),
                ))),
            )),
            right_value: Box::new(Grouping(Box::new(Expression::Literal(Literal::Number(
                BigDecimal::from_str("45.67").unwrap(),
            ))))),
        };

        // when
        let result = format!("{:?}", ast);

        // then
        assert_eq!(result, "(* (- 123) (group 45.67))".to_string());
    }

    fn successful_evaluation_test(expression: &Expression, expected: &EvaluationResult) {
        // given
        // when
        let result = expression.evaluate().unwrap();

        // then
        assert_eq!(
            result, *expected,
            "expression {:?} did not yield result: {:?}",
            expression, expected
        );
    }

    fn unsuccessful_evaluation_test(expression: &Expression, expected: &EvaluationError) {
        // given
        // when
        let result = expression.evaluate().unwrap_err();

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
        number_literal: (Expression::Literal(Literal::Number(BigDecimal::from_str("2.718281828").unwrap())), EvaluationResult::Number(BigDecimal::from_str("2.718281828").unwrap())),
        string_literal: (Expression::Literal(Literal::String("🎄".to_string())), EvaluationResult::String("🎄".to_string())),
        pi_less_than_tau: (
            Binary {
                operator: LessThan,
                left_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::from_str("3.14159").unwrap()))),
                right_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::from_str("6.283185307179586").unwrap()))),
            },
            EvaluationResult::Boolean(true),
        ),
        string_not_equal_to_number: (
            Binary {
                operator: Equal,
                left_value: Box::new(Expression::Literal(Literal::String("🥧".to_string()))),
                right_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::from_str("3.14159").unwrap()))),
            },
            EvaluationResult::Boolean(false),
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
            Binary {
                operator: Divide,
                left_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::one()))),
                right_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::zero()))),
            },
            DivideByZero,
        ),
        unexpected_nil: (
            Binary {
                operator: Multiply,
                left_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::one()))),
                right_value: Box::new(Expression::Literal(Nil)),
            },
            NilValue,
        ),
        type_mismatch: (
            Binary {
                operator: LessThan,
                left_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::from_str("3.14159").unwrap()))),
                right_value: Box::new(Expression::Literal(Literal::String("🥧".to_string()))),
            },
            TypeMismatch,
        ),
    }
}
