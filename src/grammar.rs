use crate::callable::Callable;
use crate::environment::{Environment, ExistsError, NotInALoopError};
use crate::evaluation_result::EvaluationResult;
use crate::grammar::EvaluationError::{
    CannotRedefineVariable, IncorrectNumberOfArguments, NotAFunction, NotInALoop,
};
use crate::side_effects::SideEffects;
use crate::statement::Statement;
use bigdecimal::{BigDecimal, Zero};
use itertools::Itertools;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::rc::Rc;
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
    /// A function invocation
    Call {
        /// The function being executed
        callee: Box<Expression>,
        arguments: Vec<Expression>,
    },
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
    /// Resolve the expression to a value
    ///
    /// Parameters:
    /// - `environment` - the current scope for referencing and modifying variables
    /// - `side_effects` - target for external side effects
    ///
    /// Returns:
    /// - `Ok(EvaluationResult)` - if the expression could be resolved successfully. The result type
    ///     will vary depending on the expression type and the input types
    /// - `EvaluationError` - if the expression could not be resolved
    pub fn evaluate(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
    ) -> Result<EvaluationResult, EvaluationError> {
        match self {
            Self::Literal(literal) => Ok(literal.clone().into()),
            Self::Logical {
                operator,
                left_value,
                right_value,
            } => operator.evaluate(environment, side_effects, left_value, right_value),
            Self::Unary(operator, operand) => operator.evaluate(environment, side_effects, operand),
            Self::Call { callee, arguments } => {
                let callee = callee.evaluate(environment.clone(), side_effects.clone())?;
                callee.invoke(environment, side_effects, arguments)
            }
            Self::Binary {
                operator,
                left_value,
                right_value,
            } => operator.evaluate(environment, side_effects, left_value, right_value),
            Self::Grouping(expression) => expression.evaluate(environment, side_effects),
            Self::VariableReference(name) => {
                if let Ok(value) = environment.borrow().get(name) {
                    Ok(value)
                } else {
                    Err(Undefined)
                }
            }
            Self::Assignment(identifier, expression) => {
                let result = expression.evaluate(environment.clone(), side_effects)?;
                environment
                    .borrow_mut()
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
            Self::Call { callee, arguments } => {
                if arguments.is_empty() {
                    write!(f, "( {:?} )", callee)
                } else {
                    let arguments = arguments
                        .iter()
                        .map(|argument| format!("{:?}", argument))
                        .join(", ");
                    write!(f, "( {:?}: {} )", callee, arguments)
                }
            }
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
            Self::VariableReference(name) => write!(f, "(get {})", name),
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
    /// Function call specifies the wrong number of arguments
    IncorrectNumberOfArguments(usize, usize),
    /// Tried to invoke a value that is not a function
    NotAFunction,
    CannotRedefineVariable(ExistsError),
    /// Attempted to use a `break` or `continue` statement outside the context of a loop.
    NotInALoop(NotInALoopError),
}

impl Display for EvaluationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeMismatch => write!(f, "TypeMismatch"),
            NilValue => write!(f, "Attempted to use nil value"),
            DivideByZero => write!(f, "Attempted to divide by zero"),
            Undefined => write!(f, "Expression refers to an undefined variable"),
            IncorrectNumberOfArguments(expected, found) => write!(
                f,
                "Incorrect argument count, expected: {}, found: {}",
                expected, found
            ),
            NotAFunction => write!(f, "Expression is not a function"),
            CannotRedefineVariable(error) => write!(f, "Cannot redefine variable: {}", error),
            // FIXME Display dependent on Debug
            NotInALoop(e) => write!(
                f,
                "Encountered `break` or `continue` outside a loop: {:?}",
                e
            ),
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
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        left_value: &Expression,
        right_value: &Expression,
    ) -> Result<EvaluationResult, EvaluationError> {
        match self {
            Self::Equal => Ok(EvaluationResult::Boolean(
                left_value.evaluate(environment.clone(), side_effects.clone())?
                    == right_value.evaluate(environment, side_effects)?,
            )),
            Self::NotEqual => Ok(EvaluationResult::Boolean(
                left_value.evaluate(environment.clone(), side_effects.clone())?
                    != right_value.evaluate(environment, side_effects)?,
            )),
            Self::LessThan => Self::evaluate_inequality(
                environment,
                side_effects,
                left_value,
                right_value,
                &[Ordering::Less],
            ),
            Self::GreaterThan => Self::evaluate_inequality(
                environment,
                side_effects,
                left_value,
                right_value,
                &[Ordering::Greater],
            ),
            Self::LessThanOrEqual => Self::evaluate_inequality(
                environment,
                side_effects,
                left_value,
                right_value,
                &[Ordering::Less, Ordering::Equal],
            ),
            Self::GreaterThanOrEqual => Self::evaluate_inequality(
                environment,
                side_effects,
                left_value,
                right_value,
                &[Ordering::Greater, Ordering::Equal],
            ),
            Self::Add => {
                let left = left_value.evaluate(environment.clone(), side_effects.clone())?;
                let right = right_value.evaluate(environment, side_effects)?;
                fn as_string(evaluation_result: &EvaluationResult) -> String {
                    // Note: this logic differs from `Display`
                    match evaluation_result {
                        EvaluationResult::Number(value) => value.to_engineering_notation(),
                        EvaluationResult::String(value) => value.to_string(),
                        EvaluationResult::Boolean(value) => value.to_string(),
                        EvaluationResult::Nil | EvaluationResult::Unit => "".to_string(),
                        EvaluationResult::Function(definition) => definition.to_string(),
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
            Self::Subtract => Self::perform_arithmetic(
                environment,
                side_effects,
                left_value,
                right_value,
                |x, y| x.sub(y),
            ),
            Self::Multiply => Self::perform_arithmetic(
                environment,
                side_effects,
                left_value,
                right_value,
                |x, y| x.mul(y),
            ),
            Self::Divide => {
                let left = left_value.evaluate(environment.clone(), side_effects.clone())?;
                let right = right_value.evaluate(environment, side_effects)?;
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
            Self::And => {
                let left = left_value.evaluate(environment.clone(), side_effects.clone())?;
                if !left.is_truthful() {
                    Ok(left)
                } else {
                    Ok(right_value.evaluate(environment, side_effects)?)
                }
            }
            Self::Or => {
                let left = left_value.evaluate(environment.clone(), side_effects.clone())?;
                if left.is_truthful() {
                    Ok(left)
                } else {
                    Ok(right_value.evaluate(environment, side_effects)?)
                }
            }
        }
    }

    fn perform_arithmetic(
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        left_value: &Expression,
        right_value: &Expression,
        operation: fn(BigDecimal, BigDecimal) -> BigDecimal,
    ) -> Result<EvaluationResult, EvaluationError> {
        match left_value.evaluate(environment.clone(), side_effects.clone())? {
            EvaluationResult::Number(x) => {
                match right_value.evaluate(environment, side_effects)? {
                    EvaluationResult::Number(y) => Ok(EvaluationResult::Number(operation(x, y))),
                    EvaluationResult::Nil => Err(NilValue),
                    _ => Err(TypeMismatch),
                }
            }
            EvaluationResult::Nil => Err(NilValue),
            _ => Err(TypeMismatch),
        }
    }

    fn evaluate_inequality(
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        left_value: &Expression,
        right_value: &Expression,
        expected: &[Ordering],
    ) -> Result<EvaluationResult, EvaluationError> {
        match left_value.evaluate(environment.clone(), side_effects.clone())? {
            EvaluationResult::Number(x) => {
                match right_value.evaluate(environment, side_effects)? {
                    EvaluationResult::Number(y) => {
                        Ok(EvaluationResult::Boolean(expected.contains(&x.cmp(&y))))
                    }
                    EvaluationResult::Nil => Err(NilValue),
                    _ => Err(TypeMismatch),
                }
            }
            EvaluationResult::Nil => Err(NilValue),
            _ => Err(TypeMismatch),
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
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        input: &Expression,
    ) -> Result<EvaluationResult, EvaluationError> {
        match self {
            Self::Negative => {
                let operand = input.evaluate(environment, side_effects)?;
                if let EvaluationResult::Number(operand) = operand {
                    Ok(EvaluationResult::Number(operand.neg()))
                } else {
                    Err(TypeMismatch)
                }
            }
            Self::Not => {
                let operand = input.evaluate(environment, side_effects)?;
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
pub(crate) struct FunctionDefinition {
    pub(crate) name: String,
    pub(crate) parameter_names: Vec<String>,
    pub(crate) statements: Vec<Statement>,
}

impl Callable for FunctionDefinition {
    fn arity(&self) -> usize {
        self.parameter_names.len()
    }

    fn parameter_name(&self, index: usize) -> String {
        self.parameter_names[index].clone()
    }

    fn unchecked_call(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
    ) -> Result<EvaluationResult, EvaluationError> {
        for statement in &self.statements {
            statement.execute(environment.clone(), side_effects.clone())?;
        }

        // TODO need to extract return value if one exists
        Ok(EvaluationResult::Unit)
    }
}

impl Display for FunctionDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.parameter_names.is_empty() {
            write!(f, "( {} )", self.name)
        } else {
            write!(f, "( {}: {} )", self.name, self.parameter_names.join(", "))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::BinaryOperator::{
        Add, Divide, Equal, GreaterThan, GreaterThanOrEqual, LessThan, LessThanOrEqual, Multiply,
        NotEqual, Subtract,
    };
    use super::EvaluationError::{DivideByZero, NilValue, NotAFunction, TypeMismatch};
    use super::Literal::Nil;
    use super::{BinaryOperator, EvaluationError, Expression, FunctionDefinition, UnaryOperator};
    use crate::callable::Callables;
    use crate::environment::Environment;
    use crate::evaluation_result::EvaluationResult;
    use crate::side_effects::SideEffects;
    use crate::statement::Statement;
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
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        // when
        let result = expression.evaluate(environment, side_effects).unwrap();

        // then
        assert_eq!(
            result, *expected,
            "expression {:?} did not yield result: {:?}",
            expression, expected
        );
    }

    fn unsuccessful_evaluation_test(expression: &Expression, expected: &EvaluationError) {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));

        // when
        let result = expression.evaluate(environment, side_effects).unwrap_err();

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
        cannot_invoke_non_function: (
            Expression::Call {
                callee: Box::new("not_a_function".to_string().into()),
                arguments: vec![],
            },
            NotAFunction,
        ),
    }

    #[test]
    fn addition() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let expression = Expression::Binary {
            operator: Add,
            left_value: Box::new(BigDecimal::from_f64(std::f64::consts::PI).unwrap().into()),
            right_value: Box::new(BigDecimal::from_f64(std::f64::consts::PI).unwrap().into()),
        };

        // when
        let result = expression
            .evaluate(environment, side_effects)
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
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let expression = Expression::Binary {
            operator: Subtract,
            left_value: Box::new(BigDecimal::from_f64(std::f64::consts::TAU).unwrap().into()),
            right_value: Box::new(BigDecimal::from_f64(std::f64::consts::PI).unwrap().into()),
        };

        // when
        let result = expression
            .evaluate(environment, side_effects)
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
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let expression = Expression::Binary {
            operator: Multiply,
            left_value: Box::new(BigDecimal::from(2).into()),
            right_value: Box::new(BigDecimal::from_f64(std::f64::consts::PI).unwrap().into()),
        };

        // when
        let result = expression
            .evaluate(environment, side_effects)
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
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let expression = Expression::Binary {
            operator: Divide,
            left_value: Box::new(BigDecimal::from_f64(std::f64::consts::TAU).unwrap().into()),
            right_value: Box::new(BigDecimal::from(2).into()),
        };

        // when
        let result = expression
            .evaluate(environment, side_effects)
            .expect("unable to evaluate division expression");

        // then
        assert!(matches!(
            result,
            EvaluationResult::Number(number)
            if number.clone().sub(BigDecimal::from_f64(std::f64::consts::PI).unwrap()).abs() < BigDecimal::from_f64(0.0000000001).unwrap()
        ))
    }

    #[test]
    fn function_call() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(TestSideEffects::default()));
        let definition = FunctionDefinition {
            name: "add".to_string(),
            parameter_names: vec!["a".to_string(), "b".to_string(), "c".to_string()],
            statements: vec![Statement::Print(Expression::Binary {
                operator: BinaryOperator::Add,
                left_value: Box::new(Expression::Binary {
                    operator: BinaryOperator::Add,
                    left_value: Box::new(Expression::VariableReference("a".to_string())),
                    right_value: Box::new(Expression::VariableReference("b".to_string())),
                }),
                right_value: Box::new(Expression::VariableReference("c".to_string())),
            })],
        };
        environment
            .borrow_mut()
            .define(
                "add".to_string(),
                EvaluationResult::Function(Callables::UserDefinedFunction(definition)),
            )
            .expect("Unable to define function");
        let function_call = Expression::Call {
            callee: Box::new(Expression::VariableReference("add".to_string())),
            arguments: vec![1.into(), 2.into(), 3.into()],
        };

        // when
        let result = function_call
            .evaluate(environment, side_effects.clone())
            .expect("Unable to execute function");

        // then
        assert!(matches!(result, EvaluationResult::Unit));
        assert_eq!(side_effects.borrow().lines.len(), 1);
        assert_eq!(side_effects.borrow().lines[0], "6e0");
    }

    #[derive(Clone, Default)]
    struct TestSideEffects {
        lines: Vec<String>,
    }

    impl SideEffects for TestSideEffects {
        fn println(&mut self, text: &str) {
            self.lines.push(text.to_string());
        }

        fn eprintln(&mut self, text: &str) {
            self.lines.push(text.to_string());
        }
    }
}
