use crate::environment::Environment;
use crate::evaluation_result::EvaluationResult;
use crate::grammar::EvaluationError::{CannotRedefineVariable, IncorrectNumberOfArguments};
use crate::grammar::{EvaluationError, Expression, FunctionDefinition};
use crate::side_effects::SideEffects;
use bigdecimal::BigDecimal;
use std::cell::RefCell;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Neg;
use std::rc::Rc;
use std::time::SystemTime;

pub(crate) trait Callable: Display + CallableClone {
    /// The number of function parameters.
    fn arity(&self) -> usize;

    /// Retrieve a parameter name by index.
    ///
    /// Parameters:
    /// - `index` - The 0-indexed parameter, must be less than `arity()`
    fn parameter_name(&self, index: usize) -> String;

    fn closure(&self) -> Rc<RefCell<Environment>>;

    /// Invoke this callable with expressions as arguments
    ///
    /// Parameters:
    /// - `environment` - The current execution environment for evaluating the arguments. The
    ///   invocation will spawn a new environment that captures the variables at the time it was
    ///   defined.
    /// - `side_effects` - Functions may produce side effects
    /// - `arguments` - The arguments as expressions. They will be evaluated and placed in a
    ///   temporary environment before the function body is invoked.
    ///
    /// Returns:
    /// - `Ok(EvaluationResult)` - If the function was executed successfully
    /// - `Err(EvaluationError)` - If the number of arguments is incorrect _or_ the function could
    ///   not be evaluated
    fn call(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        arguments: &[Expression],
    ) -> Result<EvaluationResult, EvaluationError> {
        if arguments.len() != self.arity() {
            // TODO should we support currying?
            // i.e. should we allow passing in fewer arguments to produce a new function?
            return Err(IncorrectNumberOfArguments(arguments.len(), self.arity()));
        }
        let arguments = arguments
            .iter()
            .map(|argument| argument.evaluate(environment.clone(), side_effects.clone()))
            .collect::<Result<Vec<EvaluationResult>, EvaluationError>>()?;
        self.call_with_arguments(side_effects, &arguments)
    }

    /// Invoke this callable with evaluated arguments
    ///
    /// Parameters:
    /// - `side_effects` - Functions may produce side effects
    /// - `arguments` - The evaluated arguments. They will be evaluated and placed in the
    ///   temporary environment before the function body is invoked.
    ///
    /// Returns:
    /// - `Ok(EvaluationResult)` - If the function was executed successfully
    /// - `Err(EvaluationError)` - If the number of arguments is incorrect _or_ the function could
    ///   not be evaluated
    fn call_with_arguments(
        &self,
        side_effects: Rc<RefCell<dyn SideEffects>>,
        arguments: &[EvaluationResult],
    ) -> Result<EvaluationResult, EvaluationError> {
        if arguments.len() != self.arity() {
            // TODO should we support currying?
            // i.e. should we allow passing in fewer arguments to produce a new function?
            return Err(IncorrectNumberOfArguments(arguments.len(), self.arity()));
        }
        let mut environment = Environment::new_nested_function_scope(self.closure());
        for (i, argument) in arguments.iter().enumerate() {
            // TODO when parsing function definition, ensure there are no duplicate parameter names
            let parameter_name = self.parameter_name(i);
            environment
                .define(parameter_name, argument.clone())
                .map_err(CannotRedefineVariable)?;
        }
        match self.unchecked_call(Rc::new(RefCell::new(environment)), side_effects) {
            Ok(result) => Ok(result),
            Err(EvaluationError::Return(expression)) => match expression {
                None => Ok(EvaluationResult::Unit),
                Some(result) => Ok(result),
            },
            Err(e) => Err(e),
        }
    }

    /// Invoke the function without performing any argument validation (including arity check).
    ///
    /// Parameters:
    /// - `environment` - A new environment specific to this function. It includes all the
    ///   (evaluated) arguments to the function and the captured variables from the time the
    ///   function was defined.
    /// - `side_effects` - Functions may produce side effects
    ///
    /// Returns:
    /// - `Ok(EvaluationResult)` - If the function was executed successfully
    /// - `Err(EvaluationError)` - If the function could not be evaluated
    fn unchecked_call(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
    ) -> Result<EvaluationResult, EvaluationError>;
}

pub(crate) trait CallableClone {
    fn clone_box(&self) -> Box<dyn Callable>;
}

impl<T> CallableClone for T
where
    T: 'static + Callable + Clone,
{
    fn clone_box(&self) -> Box<dyn Callable> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn Callable> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

#[derive(Clone)]
pub(crate) enum Callables {
    UserDefinedFunction(FunctionDefinition),
    NativeFunction(String, Box<dyn Callable>),
}

impl Eq for Callables {}

impl PartialEq for Callables {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Callables::UserDefinedFunction(x), Callables::UserDefinedFunction(y)) => x.eq(y),
            (Callables::NativeFunction(x, _), Callables::NativeFunction(y, _)) => x.eq(y),
            (_, _) => false,
        }
    }
}

impl Display for Callables {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Callables::UserDefinedFunction(definition) => write!(f, "{}", definition),
            Callables::NativeFunction(name, _callable) => write!(f, "<native {} function>", name),
        }
    }
}

impl Debug for Callables {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl Callable for Callables {
    fn arity(&self) -> usize {
        match self {
            Callables::UserDefinedFunction(definition) => definition.arity(),
            Callables::NativeFunction(_name, callable) => callable.arity(),
        }
    }

    fn parameter_name<'s>(&self, index: usize) -> String {
        match self {
            Callables::UserDefinedFunction(definition) => definition.parameter_name(index),
            Callables::NativeFunction(_name, callable) => callable.parameter_name(index),
        }
    }

    fn closure(&self) -> Rc<RefCell<Environment>> {
        match self {
            Callables::UserDefinedFunction(definition) => definition.closure.clone(),
            Callables::NativeFunction(_name, callable) => callable.closure().clone(),
        }
    }

    fn unchecked_call(
        &self,
        environment: Rc<RefCell<Environment>>,
        side_effects: Rc<RefCell<dyn SideEffects>>,
    ) -> Result<EvaluationResult, EvaluationError> {
        match self {
            Callables::UserDefinedFunction(definition) => {
                definition.unchecked_call(environment, side_effects)
            }
            Callables::NativeFunction(_name, callable) => {
                callable.unchecked_call(environment, side_effects)
            }
        }
    }
}

#[derive(Default, Clone)]
pub(crate) struct Clock {
    pub(crate) closure: Rc<RefCell<Environment>>,
}

impl Display for Clock {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<native clock fn>")
    }
}

impl From<Clock> for EvaluationResult {
    fn from(value: Clock) -> Self {
        EvaluationResult::Function(Callables::NativeFunction(
            "clock".to_string(),
            Box::new(value),
        ))
    }
}

impl Callable for Clock {
    fn arity(&self) -> usize {
        0
    }

    fn parameter_name<'s>(&self, _index: usize) -> String {
        unreachable!()
    }

    fn closure(&self) -> Rc<RefCell<Environment>> {
        self.closure.clone()
    }

    fn unchecked_call(
        &self,
        _environment: Rc<RefCell<Environment>>,
        _side_effects: Rc<RefCell<dyn SideEffects>>,
    ) -> Result<EvaluationResult, EvaluationError> {
        let seconds = match SystemTime::now().duration_since(SystemTime::UNIX_EPOCH) {
            Ok(value) => BigDecimal::from(value.as_secs()),
            Err(error) => {
                // system clock is set to some value before the epoch
                BigDecimal::from(error.duration().as_secs()).neg()
            }
        };
        Ok(EvaluationResult::Number(seconds))
    }
}

#[cfg(test)]
mod tests {
    use super::Callables::{NativeFunction, UserDefinedFunction};
    use super::{Callable, Clock};
    use crate::environment::Environment;
    use crate::evaluation_result::EvaluationResult;
    use crate::grammar::{EvaluationError, Expression, FunctionDefinition};
    use crate::side_effects::StandardSideEffects;
    use bigdecimal::Signed;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn too_many_parameters() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(StandardSideEffects::default()));

        let function = FunctionDefinition {
            parameter_names: vec!["x".to_string(), "y".to_string(), "z".to_string()],
            statements: vec![],
            closure: environment.clone(),
        };
        let arguments = vec![
            Expression::Literal("a".to_string().into()),
            Expression::Literal("b".to_string().into()),
            Expression::Literal("c".to_string().into()),
            Expression::Literal("d".to_string().into()),
        ];

        // when
        let result = function
            .call(environment, side_effects, &arguments)
            .expect_err("Expect error due to too many arguments");

        // then
        assert!(matches!(result,
            EvaluationError::IncorrectNumberOfArguments(actual, expected)
            if actual == 4 && expected == 3));
    }

    #[test]
    fn too_few_parameters() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(StandardSideEffects::default()));

        let function = FunctionDefinition {
            parameter_names: vec!["x".to_string(), "y".to_string(), "z".to_string()],
            statements: vec![],
            closure: environment.clone(),
        };
        let arguments = vec![
            Expression::Literal("a".to_string().into()),
            Expression::Literal("b".to_string().into()),
        ];

        // when
        let result = function
            .call(environment, side_effects, &arguments)
            .expect_err("Expect error due to too many arguments");

        // then
        assert!(matches!(result,
            EvaluationError::IncorrectNumberOfArguments(actual, expected)
            if actual == 2 && expected == 3));
    }

    #[test]
    fn duplicate_parameter_names() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(StandardSideEffects::default()));
        let function = FunctionDefinition {
            parameter_names: vec!["x".to_string(), "x".to_string()],
            statements: vec![],
            closure: environment.clone(),
        };
        let arguments = vec![
            Expression::Literal("a".to_string().into()),
            Expression::Literal("b".to_string().into()),
        ];

        // when
        let result = function
            .call(environment, side_effects, &arguments)
            .expect_err("Expected error due to duplicate parameter names");

        // then
        assert!(matches!(result, EvaluationError::CannotRedefineVariable(_)));
    }

    #[test]
    fn equivalent_functions_are_equal() {
        // given
        let x = UserDefinedFunction(FunctionDefinition {
            parameter_names: vec![],
            statements: vec![],
            closure: Rc::new(RefCell::new(Environment::default())),
        });
        let y = UserDefinedFunction(FunctionDefinition {
            parameter_names: vec![],
            statements: vec![],
            closure: Rc::new(RefCell::new(Environment::default())),
        });

        // when
        let result = x.eq(&y);

        // then
        assert!(result);
    }

    #[test]
    fn equivalent_native_functions_are_equal() {
        // given
        let x = NativeFunction("clock".to_string(), Box::new(Clock::default()));
        let y = NativeFunction("clock".to_string(), Box::new(Clock::default()));

        // when
        let result = x.eq(&y);

        // then
        assert!(result);
    }

    #[test]
    fn clock_returns_time() {
        // given
        let environment = Rc::new(RefCell::new(Environment::default()));
        let side_effects = Rc::new(RefCell::new(StandardSideEffects::default()));
        let callable = NativeFunction("clock".to_string(), Box::new(Clock::default()));

        // when
        let result = callable
            .call(environment, side_effects, &[])
            .expect("Unable to invoke clock");

        // then
        assert!(matches!(result, EvaluationResult::Number(value) if value.is_positive()));
    }
}
