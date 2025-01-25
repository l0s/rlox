use crate::grammar::EvaluationResult;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::rc::Rc;

/// The scope for variables
#[derive(Default)]
pub(crate) struct Environment {
    /// If `None`, then the environment is the global scope, otherwise
    parent: Option<Rc<RefCell<Self>>>,
    values: HashMap<String, EvaluationResult>,
}

/// Attempted to reference a variable that has never been declared
#[derive(Eq, PartialEq, Debug)]
pub(crate) struct UndefinedError;

/// Attempted to redefine a variable that already exists in the local scope
///
/// Note: redefining a variable is allowed in the global scope only.
#[derive(Eq, PartialEq, Debug)]
pub(crate) struct ExistsError;

impl Environment {
    /// Define a new variable or, if this is the global scope, redefine an existing variable.
    ///
    /// Returns:
    /// - `Ok(())` - if the operation succeeds
    /// - `Err(ExistsError)` - if this is not the global scope and a variable with the same name is already defined.
    pub fn define(&mut self, name: String, value: EvaluationResult) -> Result<(), ExistsError> {
        if self.parent.is_some() && self.values.contains_key(&name) {
            return Err(ExistsError);
        }
        self.values.insert(name, value);
        Ok(())
    }

    /// Set a new value for an already-defined variable
    ///
    /// Returns:
    /// - `Ok(())` if the operation succeeds
    /// - `Err(UndefinedError)` if no such variable is defined
    pub fn assign(&mut self, name: String, value: EvaluationResult) -> Result<(), UndefinedError> {
        match self.values.entry(name.clone()) {
            Entry::Occupied(mut y) => {
                y.insert(value);
                Ok(())
            }
            Entry::Vacant(_) => {
                if let Some(parent) = self.parent.clone() {
                    parent.borrow_mut().assign(name, value)
                } else {
                    Err(UndefinedError)
                }
            }
        }
    }

    /// Retrieve a variable's value from the local scope or any parent scope
    ///
    /// Returns:
    /// - `Some(EvaluationResult)` if the variable is defined
    /// - `Err(UndefinedError)` if the variable has never been defined in this or any parent scope
    pub fn get(&self, name: &str) -> Result<EvaluationResult, UndefinedError> {
        if let Some(result) = self.values.get(name) {
            Ok(result.clone())
        } else if let Some(parent) = self.parent.clone() {
            parent.borrow().get(name)
        } else {
            Err(UndefinedError)
        }
    }

    pub fn new_nested_scope(parent: Rc<RefCell<Self>>) -> Self {
        Self {
            parent: Some(parent),
            values: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Environment, ExistsError};
    use crate::grammar::EvaluationResult;
    use bigdecimal::{BigDecimal, One};
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn can_redefine_global_variable() {
        // given
        let mut global_scope = Environment::default();
        global_scope
            .define("x".to_string(), EvaluationResult::Nil)
            .expect("Unable to define variable.");

        // when
        global_scope
            .define("x".to_string(), EvaluationResult::Number(BigDecimal::one()))
            .expect("Unable to redefine variable.");

        // then
        assert_eq!(
            global_scope.get("x").expect("x is undefined"),
            EvaluationResult::Number(BigDecimal::one())
        );
    }

    #[test]
    fn cannot_redefine_local_variable() {
        // given
        let global_scope = Environment::default();
        let mut local_scope = Environment::new_nested_scope(Rc::new(RefCell::new(global_scope)));
        local_scope
            .define("x".to_string(), EvaluationResult::Nil)
            .expect("Unable to define variable.");

        // when
        let result = local_scope
            .define("x".to_string(), EvaluationResult::Number(BigDecimal::one()))
            .expect_err("Able to redefine variable in local scope.");

        // then
        assert_eq!(result, ExistsError);
    }

    #[test]
    fn can_shadow_global_variable_from_local_scope() {
        // given
        let mut global_scope = Environment::default();
        global_scope
            .define("x".to_string(), EvaluationResult::Nil)
            .expect("Unable to define variable.");
        let mut local_scope = Environment::new_nested_scope(Rc::new(RefCell::new(global_scope)));

        // when
        let result =
            local_scope.define("x".to_string(), EvaluationResult::Number(BigDecimal::one()));

        // then
        assert!(result.is_ok(), "Unable to shadow global variable");
    }
}
