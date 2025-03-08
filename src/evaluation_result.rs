use crate::callable::{Callable, Callables};
use crate::environment::Environment;
use crate::grammar::EvaluationError::NotAFunction;
use crate::grammar::{EvaluationError, Expression, FunctionDefinition, Literal};
use crate::side_effects::SideEffects;
use bigdecimal::BigDecimal;
use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::rc::Rc;

#[derive(Eq, PartialEq, Debug, Clone)]
pub(crate) enum EvaluationResult {
    Number(BigDecimal),
    String(String),
    Boolean(bool),
    Nil,
    Function(Callables),
    /// The type returned by a function that does not return a value
    Unit,
}

impl EvaluationResult {
    pub fn is_truthful(&self) -> bool {
        match self {
            Self::Number(_) => true,
            Self::String(_) => true,
            Self::Boolean(value) => *value,
            Self::Nil => false,
            Self::Function { .. } => true,
            Self::Unit => false,
        }
    }

    pub fn invoke(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        arguments: &[Expression],
    ) -> Result<EvaluationResult, EvaluationError> {
        match self {
            Self::Function(definition) => definition.call(environment, side_effects, arguments),
            _ => Err(NotAFunction),
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
            Self::Function(definition) => write!(f, "{}", definition),
            Self::Unit => write!(f, "()"),
        }
    }
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

impl From<FunctionDefinition> for EvaluationResult {
    fn from(value: FunctionDefinition) -> Self {
        EvaluationResult::Function(Callables::UserDefinedFunction(value))
    }
}

#[cfg(test)]
mod tests {
    use super::EvaluationResult;
    use crate::callable::Callables;
    use crate::environment::Environment;
    use crate::grammar::FunctionDefinition;
    use bigdecimal::{BigDecimal, One, Zero};
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn truthful_results() {
        let results = [
            EvaluationResult::Number(BigDecimal::zero()),
            EvaluationResult::Number(BigDecimal::one()),
            EvaluationResult::String("".to_string()),
            EvaluationResult::Boolean(true),
            EvaluationResult::Function(Callables::UserDefinedFunction(FunctionDefinition {
                parameter_names: vec!["source_code".to_string()],
                statements: vec![],
                closure: Rc::new(RefCell::new(Environment::default())),
            })),
        ];
        for result in results {
            assert!(result.is_truthful());
        }
    }

    #[test]
    fn untruthful_results() {
        let results = [
            EvaluationResult::Boolean(false),
            EvaluationResult::Unit,
            EvaluationResult::Nil,
        ];
        for result in results {
            assert!(!result.is_truthful());
        }
    }
}
