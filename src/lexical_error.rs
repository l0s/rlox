#[derive(Debug)]
pub(crate) struct LexicalError {
    pub line: usize,
    pub message: String,
}
