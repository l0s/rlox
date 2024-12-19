use bigdecimal::BigDecimal;

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub(crate) enum TokenType {
    // single-character tokens
    OpenParenthesis,
    CloseParenthesis,
    OpenBrace,
    CloseBrace,
    Comma,
    Period,
    Minus,
    Plus,
    Semicolon,
    ForwardSlash,
    Asterisk,

    // one or two character tokens
    /// "!" - unary operator to negate a Boolean value
    Not,
    /// "!=" - binary operator to test if two values are not the same
    NotEqual,
    /// "=" - used to set the value of a variable
    Assignment,
    /// "==" - used to test if two values are the same
    Equal,
    GreaterThan,
    GreaterThanOrEqual,
    LessThan,
    LessThanOrEqual,

    // literals
    Identifier,
    StringLiteral,
    NumberLiteral,

    // keywords
    And,
    Class,
    Else,
    False,
    Function,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Variable,
    While,

    LineComment,

    Eof,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Token {
    pub token_type: TokenType,
    pub lexeme: String,
    pub literal_string: Option<String>,
    pub literal_number: Option<BigDecimal>,
    pub line: usize,
}

impl Token {
    pub fn new(token_type: TokenType, lexeme: String, line: usize) -> Self {
        Self {
            token_type,
            lexeme,
            literal_string: None,
            literal_number: None,
            line,
        }
    }

    pub fn new_string(lexeme: String, literal: String, line: usize) -> Self {
        Self {
            token_type: TokenType::StringLiteral,
            lexeme,
            literal_string: Some(literal),
            literal_number: None,
            line,
        }
    }

    pub fn new_number(lexeme: String, literal: BigDecimal, line: usize) -> Self {
        Self {
            token_type: TokenType::NumberLiteral,
            lexeme,
            literal_string: None,
            literal_number: Some(literal),
            line,
        }
    }
}
