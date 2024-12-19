use crate::lexical_error::LexicalError;
use crate::scanner::Scanner;
use crate::token::Token;

#[derive(Default)]
pub(crate) struct Interpreter {
    pub error: bool,
}

impl Interpreter {
    pub fn run(&mut self, source: &str) -> Result<Vec<Token>, Vec<LexicalError>> {
        let mut scanner: Scanner = source.into();
        scanner.scan_tokens();
        if !scanner.errors.is_empty() {
            self.error |= true;
            Err(scanner.errors)
        } else {
            Ok(scanner.tokens)
        }
    }
}
