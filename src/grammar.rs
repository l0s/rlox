use crate::environment::{Environment, ExistsError};
use crate::side_effects::SideEffects;
use bigdecimal::{BigDecimal, Zero};
use std::fmt::{Debug, Display, Formatter};
use std::ops::Neg;
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

    /// Evaluates an expression and outputs the result
    Print(Expression),

    /// A variable declaration with optional definition
    VariableDeclaration {
        identifier: String,
        /// If None, this is a variable declaration without assignment
        expression: Option<Expression>,
    },
}

#[derive(Eq, PartialEq, Debug)]
pub(crate) enum ExecutionError {
    Evaluation(EvaluationError),
    CannotRedefineVariable(ExistsError),
}

impl Statement {
    pub fn execute<S: SideEffects>(
        &self,
        environment: &mut Environment,
        side_effects: &mut S,
    ) -> Result<(), ExecutionError> {
        match self {
            Self::Expression(expression) => {
                expression
                    .evaluate(environment)
                    .map_err(ExecutionError::Evaluation)?;
                Ok(())
            }
            Self::Print(value) => {
                let result = value
                    .evaluate(environment)
                    .map_err(ExecutionError::Evaluation)?;

                side_effects.println(&format!("{}", result));

                Ok(())
            }
            Self::VariableDeclaration {
                identifier,
                expression,
            } => {
                let result = expression
                    .clone() // TODO can we avoid cloning?
                    .map(|e| e.evaluate(environment))
                    .unwrap_or(Ok(EvaluationResult::Nil))
                    .map_err(ExecutionError::Evaluation)?;

                environment
                    .define(identifier.clone(), result)
                    .map_err(ExecutionError::CannotRedefineVariable)?;

                Ok(())
            }
        }
    }
}

/// An expression evaluates to a value
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
    VariableReference(String),
    /// Assign a new value to an existing variable
    Assignment(String, Box<Expression>),
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub(crate) enum ResultType {
    /// The expression will be non-nil and has a result type
    Some(DataType),
    /// The expression will evaluate to Nil and therefore has no result type
    None,
    /// No result type can be determined because the expression refers to an undefined variable
    Undefined,
}

impl ResultType {
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
}

impl Expression {
    pub fn evaluate(
        &self,
        environment: &mut Environment,
    ) -> Result<EvaluationResult, EvaluationError> {
        match self.result_type(environment) {
            ResultType::None => Ok(EvaluationResult::Nil),
            ResultType::Some(data_type) => data_type.evaluate(self, environment),
            ResultType::Undefined => Err(Undefined),
        }
    }

    pub fn result_type(&self, environment: &Environment) -> ResultType {
        match self {
            Self::Literal(literal) => match literal {
                Literal::Number(_) => ResultType::Some(DataType::Number),
                Literal::String(_) => ResultType::Some(DataType::String),
                Literal::True | Literal::False => ResultType::Some(DataType::Boolean),
                Literal::Nil => ResultType::None,
            },
            Self::Unary(operator, expression) => operator.result_type(environment, expression),
            Self::Binary {
                operator,
                left_value,
                right_value,
            } => operator.result_type(environment, left_value, right_value),
            Self::Grouping(expression) => expression.result_type(environment),
            Self::VariableReference(name) => {
                if let Ok(value) = environment.get(name) {
                    if let Some(data_type) = value.data_type() {
                        ResultType::Some(data_type)
                    } else {
                        ResultType::None
                    }
                } else {
                    ResultType::Undefined
                }
            }
            Self::Assignment(_, expression) => expression.result_type(environment),
        }
    }

    pub fn evaluate_boolean(&self, environment: &mut Environment) -> Result<bool, EvaluationError> {
        match self {
            Self::Literal(literal) => match literal {
                Literal::False | Literal::Nil => Ok(false),
                _ => Ok(true),
            },
            Self::Unary(operator, argument) => {
                if *operator == UnaryOperator::Not {
                    argument.evaluate_boolean(environment).map(|result| !result)
                } else {
                    Err(TypeMismatch)
                }
            }
            Self::Binary {
                operator,
                left_value,
                right_value,
            } => operator.evaluate_boolean(environment, left_value, right_value),
            Self::Grouping(expression) => expression.evaluate_boolean(environment),
            Self::VariableReference(name) => {
                if let Ok(value) = environment.get(name) {
                    match value {
                        EvaluationResult::Number(_) | EvaluationResult::String(_) => Ok(true),
                        EvaluationResult::Boolean(value) => Ok(value),
                        EvaluationResult::Nil => Ok(false),
                    }
                } else {
                    Ok(false)
                }
            }
            Self::Assignment(identifier, expression) => {
                let result = expression.evaluate_boolean(environment)?;
                environment
                    .assign(identifier.clone(), EvaluationResult::Boolean(result))
                    .map_err(|_| Undefined)?;
                Ok(result)
            }
        }
    }

    pub fn evaluate_number(
        &self,
        environment: &mut Environment,
    ) -> Result<BigDecimal, EvaluationError> {
        match self {
            Self::Literal(literal) => match literal {
                Literal::Number(number) => Ok(number.clone()),
                Literal::Nil => Err(NilValue),
                _ => Err(TypeMismatch),
            },
            Self::Unary(operator, argument) => {
                if *operator == UnaryOperator::Negative {
                    argument.evaluate_number(environment).map(BigDecimal::neg)
                } else {
                    Err(TypeMismatch)
                }
            }
            Self::Binary {
                operator,
                left_value,
                right_value,
            } => operator.evaluate_number(environment, left_value, right_value),
            Self::Grouping(expression) => expression.evaluate_number(environment),
            Self::VariableReference(name) => {
                if let Ok(value) = environment.get(name) {
                    if let EvaluationResult::Number(value) = value {
                        Ok(value.clone())
                    } else {
                        Err(TypeMismatch)
                    }
                } else {
                    Err(NilValue)
                }
            }
            Self::Assignment(identifier, expression) => {
                let result = expression.evaluate_number(environment)?;
                environment
                    .assign(identifier.clone(), EvaluationResult::Number(result.clone()))
                    .map_err(|_| Undefined)?;
                Ok(result)
            }
        }
    }

    pub fn evaluate_string(
        &self,
        environment: &mut Environment,
    ) -> Result<String, EvaluationError> {
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
            } => operator.evaluate_string(environment, left_value, right_value),
            Self::Grouping(expression) => expression.evaluate_string(environment),
            Self::VariableReference(name) => match environment.get(name) {
                Ok(value) => {
                    if let EvaluationResult::String(value) = value {
                        Ok(value.clone())
                    } else {
                        Err(TypeMismatch)
                    }
                }
                Err(_) => Err(Undefined),
            },
            Self::Assignment(identifier, expression) => {
                let result = expression.evaluate_string(environment)?;
                environment
                    .assign(identifier.clone(), EvaluationResult::String(result.clone()))
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
}

impl BinaryOperator {
    pub fn evaluate_boolean(
        &self,
        environment: &mut Environment,
        left_value: &Expression,
        right_value: &Expression,
    ) -> Result<bool, EvaluationError> {
        match self {
            Self::Equal => {
                match (
                    left_value.result_type(environment),
                    right_value.result_type(environment),
                ) {
                    (ResultType::None, ResultType::None) => Ok(true),
                    (ResultType::None, ResultType::Some(_))
                    | (ResultType::Some(_), ResultType::None) => Ok(false),
                    (ResultType::Some(DataType::String), ResultType::Some(DataType::String)) => {
                        Ok(left_value.evaluate_string(environment)?
                            == right_value.evaluate_string(environment)?)
                    }
                    (ResultType::Some(DataType::Number), ResultType::Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number(environment)?
                            == right_value.evaluate_number(environment)?)
                    }
                    (ResultType::Some(DataType::Boolean), ResultType::Some(DataType::Boolean)) => {
                        Ok(left_value.evaluate_boolean(environment)?
                            == right_value.evaluate_boolean(environment)?)
                    }
                    _ => Ok(false), // two different types, cannot be equal to each other
                }
            }
            Self::NotEqual => {
                match (
                    left_value.result_type(environment),
                    right_value.result_type(environment),
                ) {
                    (ResultType::None, ResultType::None) => Ok(false),
                    (ResultType::None, ResultType::Some(_))
                    | (ResultType::Some(_), ResultType::None) => Ok(true),
                    (ResultType::Some(DataType::String), ResultType::Some(DataType::String)) => {
                        Ok(left_value.evaluate_string(environment)?
                            != right_value.evaluate_string(environment)?)
                    }
                    (ResultType::Some(DataType::Number), ResultType::Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number(environment)?
                            != right_value.evaluate_number(environment)?)
                    }
                    (ResultType::Some(DataType::Boolean), ResultType::Some(DataType::Boolean)) => {
                        Ok(left_value.evaluate_boolean(environment)?
                            != right_value.evaluate_boolean(environment)?)
                    }
                    _ => Ok(true), // two different types, cannot be equal to each other
                }
            }
            Self::LessThan => {
                match (
                    left_value.result_type(environment),
                    right_value.result_type(environment),
                ) {
                    (ResultType::None, _) | (_, ResultType::None) => Err(NilValue),
                    (ResultType::Some(DataType::Number), ResultType::Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number(environment)?
                            < right_value.evaluate_number(environment)?)
                    }
                    (ResultType::Some(_), ResultType::Some(_)) => Err(TypeMismatch), // both values must be numbers
                    (ResultType::Undefined, _) | (_, ResultType::Undefined) => Err(Undefined),
                }
            }
            Self::GreaterThan => {
                match (
                    left_value.result_type(environment),
                    right_value.result_type(environment),
                ) {
                    (ResultType::None, _) | (_, ResultType::None) => Err(NilValue),
                    (ResultType::Some(DataType::Number), ResultType::Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number(environment)?
                            > right_value.evaluate_number(environment)?)
                    }
                    (ResultType::Some(_), ResultType::Some(_)) => Err(TypeMismatch), // both values must be numbers
                    (ResultType::Undefined, _) | (_, ResultType::Undefined) => Err(Undefined),
                }
            }
            Self::LessThanOrEqual => {
                match (
                    left_value.result_type(environment),
                    right_value.result_type(environment),
                ) {
                    (ResultType::None, _) | (_, ResultType::None) => Err(NilValue),
                    (ResultType::Some(DataType::Number), ResultType::Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number(environment)?
                            <= right_value.evaluate_number(environment)?)
                    }
                    (ResultType::Some(_), ResultType::Some(_)) => Err(TypeMismatch), // both values must be numbers
                    (ResultType::Undefined, _) | (_, ResultType::Undefined) => Err(Undefined),
                }
            }
            Self::GreaterThanOrEqual => {
                match (
                    left_value.result_type(environment),
                    right_value.result_type(environment),
                ) {
                    (ResultType::None, _) | (_, ResultType::None) => Err(NilValue),
                    (ResultType::Some(DataType::Number), ResultType::Some(DataType::Number)) => {
                        Ok(left_value.evaluate_number(environment)?
                            >= right_value.evaluate_number(environment)?)
                    }
                    (ResultType::Some(_), ResultType::Some(_)) => Err(TypeMismatch), // both values must be numbers
                    (ResultType::Undefined, _) | (_, ResultType::Undefined) => Err(Undefined),
                }
            }
            _ => Err(TypeMismatch),
        }
    }

    pub fn evaluate_number(
        &self,
        environment: &mut Environment,
        left_value: &Expression,
        right_value: &Expression,
    ) -> Result<BigDecimal, EvaluationError> {
        match self {
            Self::Add => Ok(left_value.evaluate_number(environment)?
                + right_value.evaluate_number(environment)?),
            Self::Subtract => Ok(left_value.evaluate_number(environment)?
                - right_value.evaluate_number(environment)?),
            Self::Multiply => Ok(left_value.evaluate_number(environment)?
                * right_value.evaluate_number(environment)?),
            Self::Divide => {
                let right_value = right_value.evaluate_number(environment)?;
                if right_value.is_zero() {
                    Err(DivideByZero)
                } else {
                    Ok(left_value.evaluate_number(environment)? / right_value)
                }
            }
            _ => Err(TypeMismatch),
        }
    }

    pub fn evaluate_string(
        &self,
        environment: &mut Environment,
        left_value: &Expression,
        right_value: &Expression,
    ) -> Result<String, EvaluationError> {
        if self == &Self::Add {
            let left_type = left_value.result_type(environment);
            let right_type = right_value.result_type(environment);
            if left_type == ResultType::Some(DataType::String)
                || right_type == ResultType::Some(DataType::String)
            {
                let mut convert_to_string = |expression: &Expression,
                                             data_type: ResultType|
                 -> Result<String, EvaluationError> {
                    Ok(match data_type {
                        ResultType::None => "".to_string(),
                        ResultType::Some(value) => match value {
                            DataType::Number => {
                                expression.evaluate_number(environment)?.to_string()
                            }
                            DataType::String => expression.evaluate_string(environment)?,
                            DataType::Boolean => {
                                expression.evaluate_boolean(environment)?.to_string()
                            }
                        },
                        ResultType::Undefined => Err(Undefined)?,
                    })
                };

                let left_string = convert_to_string(left_value, left_type)?;
                let right_string = convert_to_string(right_value, right_type)?;
                return Ok(format!("{}{}", left_string, right_string));
            } else if left_type.is_none() && right_type.is_none() {
                return Err(NilValue);
            }
        }
        // none of the other binary operators produce string results
        Err(TypeMismatch)
    }

    pub fn result_type(
        &self,
        environment: &Environment,
        left_value: &Expression,
        right_value: &Expression,
    ) -> ResultType {
        match self {
            Self::Equal => ResultType::Some(DataType::Boolean),
            Self::NotEqual => ResultType::Some(DataType::Boolean),
            Self::LessThan => ResultType::Some(DataType::Boolean),
            Self::GreaterThan => ResultType::Some(DataType::Boolean),
            Self::LessThanOrEqual => ResultType::Some(DataType::Boolean),
            Self::GreaterThanOrEqual => ResultType::Some(DataType::Boolean),
            Self::Add => {
                if (*left_value).result_type(environment) == ResultType::Some(DataType::String)
                    || (*right_value).result_type(environment) == ResultType::Some(DataType::String)
                {
                    ResultType::Some(DataType::String)
                } else {
                    ResultType::Some(DataType::Number)
                }
            }
            Self::Subtract => ResultType::Some(DataType::Number),
            Self::Multiply => ResultType::Some(DataType::Number),
            Self::Divide => ResultType::Some(DataType::Number),
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
    pub fn result_type(&self, _environment: &Environment, _input: &Expression) -> ResultType {
        match self {
            UnaryOperator::Negative => ResultType::Some(DataType::Number),
            UnaryOperator::Not => ResultType::Some(DataType::Boolean),
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
    pub fn evaluate(
        &self,
        expression: &Expression,
        environment: &mut Environment,
    ) -> Result<EvaluationResult, EvaluationError> {
        match self {
            Self::Number => Ok(EvaluationResult::Number(
                expression.evaluate_number(environment)?,
            )),
            Self::String => Ok(EvaluationResult::String(
                expression.evaluate_string(environment)?,
            )),
            Self::Boolean => Ok(EvaluationResult::Boolean(
                expression.evaluate_boolean(environment)?,
            )),
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

impl EvaluationResult {
    fn data_type(&self) -> Option<DataType> {
        match self {
            Self::Number(_) => Some(DataType::Number),
            Self::String(_) => Some(DataType::String),
            Self::Boolean(_) => Some(DataType::Boolean),
            Self::Nil => None,
        }
    }
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

#[cfg(test)]
mod tests {

    use super::BinaryOperator::{Add, Divide, Equal, LessThan, Multiply};
    use super::EvaluationError::{DivideByZero, NilValue, TypeMismatch};
    use super::Literal::Nil;
    use super::{
        BinaryOperator, EvaluationError, EvaluationResult, ExecutionError, Expression, Literal,
        Statement, UnaryOperator,
    };
    use crate::environment::Environment;
    use crate::side_effects::{SideEffects, StandardSideEffects};
    use bigdecimal::{BigDecimal, One, Zero};
    use std::str::FromStr;

    #[test]
    fn ast_prefix_printer() {
        // given
        let ast = Expression::Binary {
            operator: Multiply,
            left_value: Box::new(Expression::Unary(
                UnaryOperator::Negative,
                Box::new(Expression::Literal(Literal::Number(
                    BigDecimal::from_str("123").unwrap(),
                ))),
            )),
            right_value: Box::new(Expression::Grouping(Box::new(Expression::Literal(
                Literal::Number(BigDecimal::from_str("45.67").unwrap()),
            )))),
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
        let mut environment = Environment::default();
        let mut side_effects = StandardSideEffects::default();

        // when
        let result = statement.execute(&mut environment, &mut side_effects);

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
        number_literal: (Expression::Literal(Literal::Number(BigDecimal::from_str("2.718281828").unwrap())), EvaluationResult::Number(BigDecimal::from_str("2.718281828").unwrap())),
        string_literal: (Expression::Literal(Literal::String("🎄".to_string())), EvaluationResult::String("🎄".to_string())),
        pi_less_than_tau: (
            Expression::Binary {
                operator: LessThan,
                left_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::from_str("3.14159").unwrap()))),
                right_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::from_str("6.283185307179586").unwrap()))),
            },
            EvaluationResult::Boolean(true),
        ),
        string_not_equal_to_number: (
            Expression::Binary {
                operator: Equal,
                left_value: Box::new(Expression::Literal(Literal::String("🥧".to_string()))),
                right_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::from_str("3.14159").unwrap()))),
            },
            EvaluationResult::Boolean(false),
        ),
        string_concatenation: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new(Expression::Literal(Literal::String("😒".to_string()))),
                right_value: Box::new(Expression::Literal(Literal::String("😥".to_string()))),
            },
            EvaluationResult::String("😒😥".to_string()),
        ),
        nil_is_falsey: (
            Expression::Unary(UnaryOperator::Not, Box::new(Expression::Literal(Nil))),
            EvaluationResult::Boolean(true),
        ),
        zero_is_truthy: (
            Expression::Unary(UnaryOperator::Not, Box::new(Expression::Literal(Literal::Number(BigDecimal::zero())))),
            EvaluationResult::Boolean(false),
        ),
        one_is_truthy: (
            Expression::Unary(UnaryOperator::Not, Box::new(Expression::Literal(Literal::Number(BigDecimal::one())))),
            EvaluationResult::Boolean(false),
        ),
        string_is_truthy: (
            Expression::Unary(UnaryOperator::Not, Box::new(Expression::Literal(Literal::String("🥯".to_string())))),
            EvaluationResult::Boolean(false),
        ),
        concatenate_string_and_number: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new(Expression::Literal(Literal::String("🥐".to_string()))),
                right_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::from(4)))),
            },
            EvaluationResult::String("🥐4".to_string()),
        ),
        concatenate_nil_and_string: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new(Expression::Literal(Nil)),
                right_value: Box::new(Expression::Literal(Literal::String("🥐".to_string()))),
            },
            EvaluationResult::String("🥐".to_string()),
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
                left_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::one()))),
                right_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::zero()))),
            },
            DivideByZero,
        ),
        unexpected_nil: (
            Expression::Binary {
                operator: Multiply,
                left_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::one()))),
                right_value: Box::new(Expression::Literal(Nil)),
            },
            NilValue,
        ),
        type_mismatch: (
            Expression::Binary {
                operator: LessThan,
                left_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::from_str("3.14159").unwrap()))),
                right_value: Box::new(Expression::Literal(Literal::String("🥧".to_string()))),
            },
            TypeMismatch,
        ),
        cannot_negate_cupcake: (
            Expression::Binary {
                operator: Multiply,
                left_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::from_str("2").unwrap()))),
                right_value: Box::new(Expression::Grouping(Box::new(Expression::Binary {
                    operator: Divide,
                    left_value: Box::new(Expression::Literal(Literal::Number(BigDecimal::from_str("3").unwrap()))),
                    right_value: Box::new(Expression::Unary(UnaryOperator::Negative, Box::new(Expression::Literal(Literal::String("🧁".to_string()))))),
                })))
            },
            TypeMismatch,
        ),
        cannot_concatenate_nils: (
            Expression::Binary {
                operator: Add,
                left_value: Box::new(Expression::Literal(Nil)),
                right_value: Box::new(Expression::Literal(Nil)),
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
            Statement::Expression(Expression::Assignment("a".to_string(), Box::new(Expression::Literal(BigDecimal::one().into())))),
            ExecutionError::Evaluation(EvaluationError::Undefined),
        ),
    }

    #[test]
    fn print_variable() {
        // given
        let mut environment = Environment::default();
        let mut side_effects = TestSideEffects::default();
        let variable_definition = Statement::VariableDeclaration {
            identifier: "beverage".to_string(),
            expression: Some(Expression::Literal(Literal::String("espresso".to_string()))),
        };
        let print_statement =
            Statement::Print(Expression::VariableReference("beverage".to_string()));

        // when
        variable_definition
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to define variable");
        print_statement
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to execute print statement");

        // then
        assert_eq!(side_effects.lines.len(), 1);
        assert_eq!(side_effects.lines[0], "espresso");
    }

    #[test]
    fn redefine_variable() {
        // given
        let mut environment = Environment::default();
        let mut side_effects = TestSideEffects::default();

        let initial_definition = Statement::VariableDeclaration {
            identifier: "a".to_string(),
            expression: Some(Expression::Literal(Literal::String("before".to_string()))),
        };
        let subsequent_definition = Statement::VariableDeclaration {
            identifier: "a".to_string(),
            expression: Some(Expression::Literal(Literal::String("after".to_string()))),
        };
        let print_statement = Statement::Print(Expression::VariableReference("a".to_string()));

        // when
        initial_definition
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to define variable");
        print_statement
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to print initial variable value");
        subsequent_definition
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to redefine variable");
        print_statement
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to print subsequent variable value");

        // then
        assert_eq!(side_effects.lines.len(), 2);
        assert_eq!(side_effects.lines[0], "before");
        assert_eq!(side_effects.lines[1], "after");
    }

    #[test]
    fn uninitialized_variables_are_nil() {
        // given
        let mut environment = Environment::default();
        let mut side_effects = TestSideEffects::default();

        let declaration = Statement::VariableDeclaration {
            identifier: "a".to_string(),
            expression: None,
        };
        let print_statement = Statement::Print(Expression::VariableReference("a".to_string()));

        // when
        declaration
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to declare variable");
        print_statement
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to print initial variable value");

        // then
        assert_eq!(side_effects.lines.len(), 1);
        assert_eq!(side_effects.lines[0], "nil");
    }

    #[test]
    fn math_on_variables() {
        // given
        let mut environment = Environment::default();
        let mut side_effects = TestSideEffects::default();

        let define_a = Statement::VariableDeclaration {
            identifier: "a".to_string(),
            expression: Some(Expression::Literal(Literal::Number(BigDecimal::one()))),
        };
        let define_b = Statement::VariableDeclaration {
            identifier: "b".to_string(),
            expression: Some(Expression::Literal(Literal::Number(BigDecimal::from(2)))),
        };
        let print_statement = Statement::Print(Expression::Binary {
            operator: BinaryOperator::Add,
            left_value: Box::new(Expression::VariableReference("a".to_string())),
            right_value: Box::new(Expression::VariableReference("b".to_string())),
        });

        // when
        define_a
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to define a");
        define_b
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to define b");
        print_statement
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to print evaluation result");

        // then
        assert_eq!(side_effects.lines.len(), 1);
        assert_eq!(side_effects.lines[0], "3e0");
    }

    #[test]
    fn assignment_returns_value() {
        // given
        let mut environment = Environment::default();
        let mut side_effects = TestSideEffects::default();

        let define_a = Statement::VariableDeclaration {
            identifier: "a".to_string(),
            expression: Some(Expression::Literal(BigDecimal::one().into())),
        };
        let print_statement = Statement::Print(Expression::Assignment(
            "a".to_string(),
            Box::new(Expression::Literal(BigDecimal::from(2).into())),
        ));

        // when
        define_a
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to define variable");
        print_statement
            .execute(&mut environment, &mut side_effects)
            .expect("Unable to print expression");

        // then
        assert_eq!(side_effects.lines.len(), 1);
        assert_eq!(side_effects.lines[0], "2e0");
        assert_eq!(
            environment.get("a"),
            Ok(EvaluationResult::Number(BigDecimal::from(2).into()))
        );
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
