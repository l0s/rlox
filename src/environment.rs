use crate::grammar::EvaluationResult;
use std::collections::HashMap;

#[derive(Default)]
pub(crate) struct Environment {
    values: HashMap<String, EvaluationResult>,
}

impl Environment {
    pub fn define(&mut self, name: String, value: EvaluationResult) {
        self.values.insert(name, value);
    }

    pub fn get(&self, name: &str) -> Option<&EvaluationResult> {
        self.values.get(name)
    }

    pub fn exists(&self, name: &str) -> bool {
        self.get(name).is_some()
    }
}
