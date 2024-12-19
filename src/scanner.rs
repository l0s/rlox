use std::iter::Iterator;
use std::str::FromStr;

use bigdecimal::BigDecimal;
use itertools::Itertools;
use phf::phf_map;
use unicode_segmentation::UnicodeSegmentation;

use crate::lexical_error::LexicalError;
use crate::token::{Token, TokenType};

#[derive(Debug)]
pub(crate) struct Scanner<'a> {
    graphemes: Vec<&'a str>,
    pub tokens: Vec<Token>,
    start: usize,
    current: usize,
    line: usize,
    pub errors: Vec<LexicalError>,
}

impl<'a> From<&'a str> for Scanner<'a> {
    fn from(value: &'a str) -> Self {
        Self {
            graphemes: value.graphemes(true).collect(),
            tokens: vec![],
            start: 0,
            current: 0,
            line: 1,
            errors: vec![],
        }
    }
}

static KEYWORDS: phf::Map<&'static str, TokenType> = phf_map! {
    "and" => TokenType::And,
    "class" => TokenType::Class,
    "else" => TokenType::Else,
    "false" => TokenType::False,
    "for" => TokenType::For,
    "fun" => TokenType::Function,
    "if" => TokenType::If,
    "nil" => TokenType::Nil,
    "or" => TokenType::Or,
    "print" => TokenType::Print,
    "return" => TokenType::Return,
    "super" => TokenType::Super,
    "this" => TokenType::This,
    "true" => TokenType::True,
    "var" => TokenType::Variable,
    "while" => TokenType::While,
};

impl<'a> Scanner<'a> {
    pub fn scan_tokens(&mut self) {
        while !self.at_end() {
            // We are at the beginning of the next lexeme
            self.start = self.current;
            self.scan_token();
        }

        self.tokens
            .push(Token::new(TokenType::Eof, String::from(""), self.line));
    }

    ///
    /// Advances `current`, but not `start`
    fn scan_token(&mut self) {
        let c = self.advance();
        let lexeme = self.current_lexeme();
        let scan_result = match c {
            // single-character lexemes
            "(" => Ok(Some(Token::new(
                TokenType::OpenParenthesis,
                lexeme,
                self.line,
            ))),
            ")" => Ok(Some(Token::new(
                TokenType::CloseParenthesis,
                lexeme,
                self.line,
            ))),
            "{" => Ok(Some(Token::new(TokenType::OpenBrace, lexeme, self.line))),
            "}" => Ok(Some(Token::new(TokenType::CloseBrace, lexeme, self.line))),
            "," => Ok(Some(Token::new(TokenType::Comma, lexeme, self.line))),
            "." => Ok(Some(Token::new(TokenType::Period, lexeme, self.line))),
            "-" => Ok(Some(Token::new(TokenType::Minus, lexeme, self.line))),
            "+" => Ok(Some(Token::new(TokenType::Plus, lexeme, self.line))),
            ";" => Ok(Some(Token::new(TokenType::Semicolon, lexeme, self.line))),
            "*" => Ok(Some(Token::new(TokenType::Asterisk, lexeme, self.line))),
            // one or two-character lexemes
            "!" => Ok(Some(Token::new(
                self.conditional_advance("=", TokenType::NotEqual, TokenType::Not),
                lexeme,
                self.line,
            ))),
            "=" => Ok(Some(Token::new(
                self.conditional_advance("=", TokenType::Equal, TokenType::Assignment),
                lexeme,
                self.line,
            ))),
            "<" => Ok(Some(Token::new(
                self.conditional_advance("=", TokenType::LessThanOrEqual, TokenType::LessThan),
                lexeme,
                self.line,
            ))),
            ">" => Ok(Some(Token::new(
                self.conditional_advance(
                    "=",
                    TokenType::GreaterThanOrEqual,
                    TokenType::GreaterThan,
                ),
                lexeme,
                self.line,
            ))),
            // 1+ length lexemes
            "/" => {
                let token_type =
                    self.conditional_advance("/", TokenType::LineComment, TokenType::ForwardSlash);
                if token_type == TokenType::LineComment {
                    // A line comment goes until the end of the line, so consume those graphemes
                    while self.peek() != "\n" && !self.at_end() {
                        self.advance();
                    }
                    // drop comments early,
                    // don't emit a token
                    Ok(None)
                } else {
                    // TokenType::ForwardSlash
                    Ok(Some(Token::new(token_type, lexeme, self.line)))
                }
            }
            // arbitrary-length lexemes
            "\"" => self.string_literal(),
            // Ignore whitespace
            " " | "\r" | "\t" => Ok(None),
            "\n" => {
                self.line += 1;
                Ok(None)
            }
            "" => Ok(None), // this happens at the end of the file
            other => {
                if Self::is_digit(other) {
                    self.number_literal()
                } else if Self::is_identifier_leading_char(other) {
                    self.identifier_or_keyword()
                } else {
                    Err(LexicalError {
                        line: self.line,
                        message: format!("Unexpected character: '{}'", other),
                    })
                }
            }
        };
        match scan_result {
            Ok(token) => {
                if let Some(token) = token {
                    self.tokens.push(token);
                }
            }
            Err(error) => self.errors.push(error),
        }
    }

    fn string_literal(&mut self) -> Result<Option<Token>, LexicalError> {
        while self.peek() != "\"" && !self.at_end() {
            if self.peek() == "\n" {
                self.line += 1;
            }
            self.advance();
        }
        if self.at_end() {
            return Err(LexicalError {
                line: self.line,
                message: "Unterminated string.".to_string(),
            });
        }
        // consume the closing '"'
        self.advance();
        let value = self.graphemes[(self.start + 1)..(self.current - 1)].join("");
        Ok(Some(Token::new_string(
            self.current_lexeme(),
            value,
            self.line,
        )))
    }

    fn is_digit(grapheme: &str) -> bool {
        let mut chars = grapheme.chars();
        if let Some(first) = chars.next() {
            first.is_ascii_digit() && chars.next().is_none()
        } else {
            false
        }
    }

    fn is_identifier_leading_char(grapheme: &str) -> bool {
        let mut chars = grapheme.chars();
        if let Some(first) = chars.next() {
            (first.is_alphabetic() || first == '_') && chars.next().is_none()
        } else {
            false
        }
    }

    fn is_identifier_char(grapheme: &str) -> bool {
        let mut chars = grapheme.chars();
        if let Some(first) = chars.next() {
            (first.is_alphanumeric() || first == '_') && chars.next().is_none()
        } else {
            false
        }
    }

    fn number_literal(&mut self) -> Result<Option<Token>, LexicalError> {
        while Self::is_digit(self.peek()) {
            self.advance();
        }
        if self.peek() == "." && Self::is_digit(self.peek_next()) {
            // Consume the decimal point
            self.advance();
            while Self::is_digit(self.peek()) {
                self.advance();
            }
        }
        let string = self.graphemes[self.start..self.current].join("");
        let result = BigDecimal::from_str(&string);
        match result {
            Ok(literal) => Ok(Some(Token::new_number(string, literal, self.line))),
            Err(parse_error) => Err(LexicalError {
                line: self.line,
                message: format!("Error parsing number literal: {}", parse_error),
            }),
        }
    }

    fn identifier_or_keyword(&mut self) -> Result<Option<Token>, LexicalError> {
        while Self::is_identifier_char(self.peek()) {
            self.advance();
        }
        let string = self.graphemes[self.start..self.current].join("");
        let token_type = if let Some(keyword_type) = KEYWORDS.get(&string) {
            *keyword_type
        } else {
            TokenType::Identifier
        };
        Ok(Some(Token::new(token_type, string, self.line))) // TODO should we have a dedicated identifier field?
    }

    /// Test if the next character matches what is expected and if so, advance the cursor
    fn conditional_advance(
        &mut self,
        expected_char: &str,
        type_on_match: TokenType,
        type_otherwise: TokenType,
    ) -> TokenType {
        if self.at_end() || self.graphemes[self.current] != expected_char {
            return type_otherwise;
        }
        self.current += 1;
        type_on_match
    }

    fn peek(&self) -> &str {
        if self.at_end() {
            return "\0"; // TODO can probably return ""
        }
        self.graphemes[self.current]
    }

    fn peek_next(&self) -> &str {
        let index = self.current + 1;
        if index >= self.graphemes.len() {
            return "\0"; // TODO can probably return ""
        }
        self.graphemes[index]
    }

    fn at_end(&self) -> bool {
        self.current >= self.graphemes.len()
    }

    fn advance(&mut self) -> &'a str {
        self.current += 1;
        if self.at_end() {
            return "";
        }
        self.graphemes[self.current - 1]
    }

    fn current_lexeme(&self) -> String {
        self.graphemes[self.start..self.current].iter().join("")
    }
}

#[cfg(test)]
mod tests {
    use super::Scanner;
    use crate::token::TokenType;
    use bigdecimal::BigDecimal;
    use std::str::FromStr;

    #[test]
    fn parse_comment() {
        // given
        let source = "// this is a comment";
        let mut scanner: Scanner = source.into();

        // when
        scanner.scan_tokens();

        // then
        assert!(
            scanner.errors.is_empty(),
            "Encountered errors: {:?}",
            scanner.errors
        );
        assert_eq!(scanner.tokens.len(), 1);
        assert_eq!(scanner.tokens.get(0).unwrap().token_type, TokenType::Eof);
    }

    #[test]
    fn group_stuff() {
        // given
        let source = "(( )){} // grouping stuff";
        let mut scanner: Scanner = source.into();

        // when
        scanner.scan_tokens();

        // then
        assert!(
            scanner.errors.is_empty(),
            "Encountered errors: {:?}",
            scanner.errors
        );
        assert_eq!(
            scanner.tokens.len(),
            7,
            "Wrong number of tokens: {:?}",
            scanner.tokens
        );
        assert_eq!(
            scanner.tokens.get(0).unwrap().token_type,
            TokenType::OpenParenthesis
        );
        assert_eq!(
            scanner.tokens.get(1).unwrap().token_type,
            TokenType::OpenParenthesis
        );
        assert_eq!(
            scanner.tokens.get(2).unwrap().token_type,
            TokenType::CloseParenthesis
        );
        assert_eq!(
            scanner.tokens.get(3).unwrap().token_type,
            TokenType::CloseParenthesis
        );
        assert_eq!(
            scanner.tokens.get(4).unwrap().token_type,
            TokenType::OpenBrace
        );
        assert_eq!(
            scanner.tokens.get(5).unwrap().token_type,
            TokenType::CloseBrace
        );
        assert_eq!(scanner.tokens.get(6).unwrap().token_type, TokenType::Eof);
    }

    #[test]
    fn operators() {
        // given
        let source = "!*+-/=<> <= == // operators";
        let mut scanner: Scanner = source.into();

        // when
        scanner.scan_tokens();

        // then
        assert!(
            scanner.errors.is_empty(),
            "Encountered errors: {:?}",
            scanner.errors
        );
        assert_eq!(scanner.tokens.len(), 11);
        assert_eq!(scanner.tokens.get(0).unwrap().token_type, TokenType::Not);
        assert_eq!(
            scanner.tokens.get(1).unwrap().token_type,
            TokenType::Asterisk
        );
        assert_eq!(scanner.tokens.get(2).unwrap().token_type, TokenType::Plus);
        assert_eq!(scanner.tokens.get(3).unwrap().token_type, TokenType::Minus);
        assert_eq!(
            scanner.tokens.get(4).unwrap().token_type,
            TokenType::ForwardSlash
        );
        assert_eq!(
            scanner.tokens.get(5).unwrap().token_type,
            TokenType::Assignment
        );
        assert_eq!(
            scanner.tokens.get(6).unwrap().token_type,
            TokenType::LessThan
        );
        assert_eq!(
            scanner.tokens.get(7).unwrap().token_type,
            TokenType::GreaterThan
        );
        assert_eq!(
            scanner.tokens.get(8).unwrap().token_type,
            TokenType::LessThanOrEqual
        );
        assert_eq!(scanner.tokens.get(9).unwrap().token_type, TokenType::Equal);
        assert_eq!(scanner.tokens.get(10).unwrap().token_type, TokenType::Eof);
    }

    #[test]
    fn string_literal() {
        // given
        let source = "\"this is a string\"";
        let mut scanner: Scanner = source.into();

        // when
        scanner.scan_tokens();

        // then
        assert!(
            scanner.errors.is_empty(),
            "Encountered errors: {:?}",
            scanner.errors
        );
        let token = scanner.tokens.get(0).unwrap();
        assert_eq!(token.token_type, TokenType::StringLiteral);
        assert_eq!(token.literal_string, Some(String::from("this is a string")));
        assert_eq!(scanner.tokens.get(1).unwrap().token_type, TokenType::Eof);
        assert_eq!(scanner.tokens.len(), 2);
    }

    #[test]
    fn unicode_string_literal() {
        // given
        let source = "var pie = \"🥧\"";
        let mut scanner: Scanner = source.into();

        // when
        scanner.scan_tokens();

        // then
        assert!(
            scanner.errors.is_empty(),
            "Encountered errors: {:?}",
            scanner.errors
        );
        assert_eq!(scanner.tokens.len(), 5);
        assert_eq!(
            scanner.tokens.get(0).unwrap().token_type,
            TokenType::Variable
        );
        let identifier = scanner.tokens.get(1).unwrap();
        assert_eq!(identifier.token_type, TokenType::Identifier);
        assert_eq!(&identifier.lexeme, "pie");
        assert_eq!(
            scanner.tokens.get(2).unwrap().token_type,
            TokenType::Assignment
        );
        let literal = scanner.tokens.get(3).unwrap();
        assert_eq!(literal.token_type, TokenType::StringLiteral);
        assert_eq!(literal.literal_string, Some("🥧".to_string()));
        println!("-- literal token: {:?}", literal);
    }

    #[test]
    fn multi_line_string_literal() {
        // given
        let source = "\"this is a\nstring\"";
        let mut scanner: Scanner = source.into();

        // when
        scanner.scan_tokens();

        // then
        assert!(
            scanner.errors.is_empty(),
            "Encountered errors: {:?}",
            scanner.errors
        );
        let token = scanner.tokens.get(0).unwrap();
        assert_eq!(token.token_type, TokenType::StringLiteral);
        assert_eq!(
            token.literal_string,
            Some(String::from("this is a\nstring"))
        );
        assert_eq!(scanner.tokens.get(1).unwrap().token_type, TokenType::Eof);
        assert_eq!(scanner.tokens.len(), 2);
    }

    #[test]
    fn number_literal() {
        // given
        let source = "var 𝜋 = 3.14159";
        let mut scanner: Scanner = source.into();

        // when
        scanner.scan_tokens();

        // then
        assert!(
            scanner.errors.is_empty(),
            "Encountered errors: {:?}",
            scanner.errors
        );
        assert_eq!(scanner.tokens.len(), 5);
        assert_eq!(
            scanner.tokens.get(0).unwrap().token_type,
            TokenType::Variable
        );
        let identifier = scanner.tokens.get(1).unwrap();
        assert_eq!(identifier.token_type, TokenType::Identifier);
        assert_eq!(&identifier.lexeme, "𝜋");
        assert_eq!(
            scanner.tokens.get(2).unwrap().token_type,
            TokenType::Assignment
        );
        let literal = scanner.tokens.get(3).unwrap();
        assert_eq!(literal.token_type, TokenType::NumberLiteral);
        assert_eq!(
            literal.literal_number,
            Some(BigDecimal::from_str("3.14159").unwrap())
        );
    }
}
