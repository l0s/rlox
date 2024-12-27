use bigdecimal::{BigDecimal, Zero};
use std::fmt::{Debug, Display, Formatter};
use std::ops::Neg;
use DataType::{BooleanType, NumberType, StringType};
use EvaluationError::{DivideByZero, NilValue, TypeMismatch};
use EvaluationResult::{BooleanResult, NilResult, NumberResult, StringResult};

pub(crate) enum Expression {
    LiteralExpression(Literal),
    UnaryExpression(UnaryOperator, Box<Expression>),
    BinaryExpression {
        operator: BinaryOperator,
        left_value: Box<Expression>,
        right_value: Box<Expression>,
    },
    Grouping(Box<Expression>),
}

impl Expression {
    pub fn evaluate(&self) -> Result<EvaluationResult, EvaluationError> {
        match self.result_type() {
            None => Ok(NilResult),
            Some(data_type) => data_type.evaluate(self),
        }
    }

    pub fn result_type(&self) -> Option<DataType> {
        match self {
            Self::LiteralExpression(literal) => match literal {
                Literal::NumberLiteral(_) => Some(NumberType),
                Literal::StringLiteral(_) => Some(StringType),
                Literal::True => Some(BooleanType),
                Literal::False => Some(BooleanType),
                Literal::Nil => None,
            },
            Self::UnaryExpression(operator, expression) => {
                operator.result_type(expression.result_type())
            }
            Self::BinaryExpression {
                operator,
                left_value: _left_value,
                right_value: _right_value,
            } => Some(operator.result_type()),
            Self::Grouping(expression) => expression.result_type(),
        }
    }

    pub fn evaluate_boolean(&self) -> Result<bool, EvaluationError> {
        match self {
            Self::LiteralExpression(literal) => match literal {
                Literal::NumberLiteral(_) => Err(TypeMismatch),
                Literal::StringLiteral(_) => Err(TypeMismatch),
                Literal::True => Ok(true),
                Literal::False => Ok(false),
                Literal::Nil => Err(NilValue),
            },
            Self::UnaryExpression(operator, argument) => {
                if *operator == UnaryOperator::Not {
                    argument.evaluate_boolean().map(|result| !result)
                } else {
                    Err(TypeMismatch)
                }
            }
            Self::BinaryExpression {
                operator,
                left_value,
                right_value,
            } => operator.evaluate_boolean(left_value, right_value),
            Self::Grouping(expression) => expression.evaluate_boolean(),
        }
    }

    pub fn evaluate_number(&self) -> Result<BigDecimal, EvaluationError> {
        match self {
            Self::LiteralExpression(literal) => match literal {
                Literal::NumberLiteral(number) => Ok(number.clone()),
                Literal::Nil => Err(NilValue),
                _ => Err(TypeMismatch),
            },
            Self::UnaryExpression(operator, argument) => {
                if *operator == UnaryOperator::Negative {
                    argument.evaluate_number().map(BigDecimal::neg)
                } else {
                    Err(TypeMismatch)
                }
            }
            Self::BinaryExpression {
                operator,
                left_value,
                right_value,
            } => operator.evaluate_number(left_value, right_value),
            Self::Grouping(expression) => expression.evaluate_number(),
        }
    }

    pub fn evaluate_string(&self) -> Result<String, EvaluationError> {
        match self {
            Self::LiteralExpression(literal) => match literal {
                Literal::StringLiteral(value) => Ok(value.clone()),
                Literal::Nil => Err(NilValue),
                _ => Err(TypeMismatch),
            },
            Self::UnaryExpression(_, _) => Err(TypeMismatch),
            Self::BinaryExpression {
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
            Self::LiteralExpression(literal) => match literal {
                Literal::NumberLiteral(number) => f.write_str(&number.to_string()),
                Literal::StringLiteral(string) => f.write_str(string),
                Literal::True => f.write_str("true"),
                Literal::False => f.write_str("false"),
                Literal::Nil => f.write_str("nil"),
            },
            Self::UnaryExpression(operator, expression) => match operator {
                UnaryOperator::Negative => f.write_fmt(format_args!("(- {:?})", expression)),
                UnaryOperator::Not => f.write_fmt(format_args!("(! {:?})", expression)),
            },
            Self::BinaryExpression {
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
                    BinaryOperator::Plus => "+",
                    BinaryOperator::Minus => "-",
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

#[derive(Debug, Eq, PartialEq)]
pub enum EvaluationError {
    TypeMismatch,
    NilValue,
    DivideByZero,
}

pub(crate) enum BinaryOperator {
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    Plus,
    Minus,
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
                    (Some(StringType), Some(StringType)) => {
                        Ok(left_value.evaluate_string()? == right_value.evaluate_string()?)
                    }
                    (Some(NumberType), Some(NumberType)) => {
                        Ok(left_value.evaluate_number()? == right_value.evaluate_number()?)
                    }
                    (Some(BooleanType), Some(BooleanType)) => {
                        Ok(left_value.evaluate_boolean()? == right_value.evaluate_boolean()?)
                    }
                    _ => Ok(false), // two different types, cannot be equal to each other
                }
            }
            Self::NotEqual => {
                match (left_value.result_type(), right_value.result_type()) {
                    (None, None) => Ok(false),
                    (None, Some(_)) | (Some(_), None) => Ok(true),
                    (Some(StringType), Some(StringType)) => {
                        Ok(left_value.evaluate_string()? != right_value.evaluate_string()?)
                    }
                    (Some(NumberType), Some(NumberType)) => {
                        Ok(left_value.evaluate_number()? != right_value.evaluate_number()?)
                    }
                    (Some(BooleanType), Some(BooleanType)) => {
                        Ok(left_value.evaluate_boolean()? != right_value.evaluate_boolean()?)
                    }
                    _ => Ok(true), // two different types, cannot be equal to each other
                }
            }
            Self::LessThan => {
                match (left_value.result_type(), right_value.result_type()) {
                    (None, _) | (_, None) => Err(NilValue),
                    (Some(NumberType), Some(NumberType)) => {
                        Ok(left_value.evaluate_number()? < right_value.evaluate_number()?)
                    }
                    (Some(_), Some(_)) => Err(TypeMismatch), // both values must be numbers
                }
            }
            Self::GreaterThan => {
                match (left_value.result_type(), right_value.result_type()) {
                    (None, _) | (_, None) => Err(NilValue),
                    (Some(NumberType), Some(NumberType)) => {
                        Ok(left_value.evaluate_number()? > right_value.evaluate_number()?)
                    }
                    (Some(_), Some(_)) => Err(TypeMismatch), // both values must be numbers
                }
            }
            Self::LessThanOrEqual => {
                match (left_value.result_type(), right_value.result_type()) {
                    (None, _) | (_, None) => Err(NilValue),
                    (Some(NumberType), Some(NumberType)) => {
                        Ok(left_value.evaluate_number()? <= right_value.evaluate_number()?)
                    }
                    (Some(_), Some(_)) => Err(TypeMismatch), // both values must be numbers
                }
            }
            Self::GreaterThanOrEqual => {
                match (left_value.result_type(), right_value.result_type()) {
                    (None, _) | (_, None) => Err(NilValue),
                    (Some(NumberType), Some(NumberType)) => {
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
            Self::Plus => Ok(left_value.evaluate_number()? + right_value.evaluate_number()?),
            Self::Minus => Ok(left_value.evaluate_number()? - right_value.evaluate_number()?),
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
            Self::Equal => BooleanType,
            Self::NotEqual => BooleanType,
            Self::LessThan => BooleanType,
            Self::GreaterThan => BooleanType,
            Self::LessThanOrEqual => BooleanType,
            Self::GreaterThanOrEqual => BooleanType,
            Self::Plus => NumberType,
            Self::Minus => NumberType,
            Self::Multiply => NumberType,
            Self::Divide => NumberType,
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
            Self::Plus => f.write_str("Plus"),
            Self::Minus => f.write_str("Minus"),
            Self::Multiply => f.write_str("Multiply"),
            Self::Divide => f.write_str("Divide"),
        }
    }
}

#[derive(Eq, PartialEq)]
pub(crate) enum UnaryOperator {
    Negative,
    Not,
}

impl UnaryOperator {
    pub fn result_type(&self, input_type: Option<DataType>) -> Option<DataType> {
        input_type
    }
}

pub(crate) enum Literal {
    NumberLiteral(BigDecimal),
    StringLiteral(String),
    True,
    False,
    Nil,
}

#[derive(Eq, PartialEq)]
pub(crate) enum DataType {
    NumberType,
    StringType,
    BooleanType,
}

impl DataType {
    pub fn evaluate(&self, expression: &Expression) -> Result<EvaluationResult, EvaluationError> {
        match self {
            NumberType => Ok(NumberResult(expression.evaluate_number()?)),
            StringType => Ok(StringResult(expression.evaluate_string()?)),
            BooleanType => Ok(BooleanResult(expression.evaluate_boolean()?)),
        }
    }
}

#[derive(Eq, PartialEq, Debug)]
pub(crate) enum EvaluationResult {
    NumberResult(BigDecimal),
    StringResult(String),
    BooleanResult(bool),
    NilResult,
}

#[cfg(test)]
mod tests {
    use super::BinaryOperator::{Divide, Equal, LessThan, Multiply};
    use super::EvaluationResult::{BooleanResult, NumberResult, StringResult};
    use super::Expression::{BinaryExpression, Grouping, LiteralExpression, UnaryExpression};
    use super::Literal::{False, Nil, NumberLiteral, StringLiteral, True};
    use super::UnaryOperator::Negative;
    use crate::grammar::EvaluationError::{DivideByZero, NilValue, TypeMismatch};
    use crate::grammar::{EvaluationError, EvaluationResult, Expression};
    use bigdecimal::{BigDecimal, One, Zero};
    use std::str::FromStr;

    #[test]
    fn ast_prefix_printer() {
        // given
        let ast = BinaryExpression {
            operator: Multiply,
            left_value: Box::new(UnaryExpression(
                Negative,
                Box::new(LiteralExpression(NumberLiteral(
                    BigDecimal::from_str("123").unwrap(),
                ))),
            )),
            right_value: Box::new(Grouping(Box::new(LiteralExpression(NumberLiteral(
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
        number_literal: (LiteralExpression(NumberLiteral(BigDecimal::from_str("2.718281828").unwrap())), NumberResult(BigDecimal::from_str("2.718281828").unwrap())),
        string_literal: (LiteralExpression(StringLiteral("🎄".to_string())), StringResult("🎄".to_string())),
        pi_less_than_tau: (
            BinaryExpression {
                operator: LessThan,
                left_value: Box::new(LiteralExpression(NumberLiteral(BigDecimal::from_str("3.14159").unwrap()))),
                right_value: Box::new(LiteralExpression(NumberLiteral(BigDecimal::from_str("6.283185307179586").unwrap()))),
            },
            BooleanResult(true),
        ),
        string_not_equal_to_number: (
            BinaryExpression {
                operator: Equal,
                left_value: Box::new(LiteralExpression(StringLiteral("🥧".to_string()))),
                right_value: Box::new(LiteralExpression(NumberLiteral(BigDecimal::from_str("3.14159").unwrap()))),
            },
            BooleanResult(false),
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
            BinaryExpression {
                operator: Divide,
                left_value: Box::new(LiteralExpression(NumberLiteral(BigDecimal::one()))),
                right_value: Box::new(LiteralExpression(NumberLiteral(BigDecimal::zero()))),
            },
            DivideByZero,
        ),
        unexpected_nil: (
            BinaryExpression {
                operator: Multiply,
                left_value: Box::new(LiteralExpression(NumberLiteral(BigDecimal::one()))),
                right_value: Box::new(LiteralExpression(Nil)),
            },
            NilValue,
        ),
        type_mismatch: (
            BinaryExpression {
                operator: LessThan,
                left_value: Box::new(LiteralExpression(NumberLiteral(BigDecimal::from_str("3.14159").unwrap()))),
                right_value: Box::new(LiteralExpression(StringLiteral("🥧".to_string()))),
            },
            TypeMismatch,
        ),
    }
}
