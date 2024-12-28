use crate::grammar::Expression::{Binary, Unary};
use crate::grammar::{BinaryOperator, Expression, Literal, UnaryOperator};
use crate::parser::ParseError::{
    InvalidBinaryOperator, InvalidLiteral, InvalidPrimaryToken, InvalidUnaryOperator,
    UnclosedGrouping,
};
use crate::token::{Token, TokenType};

#[derive(Debug)]
pub(crate) struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl From<Vec<Token>> for Parser {
    fn from(value: Vec<Token>) -> Self {
        Self {
            tokens: value,
            current: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum ParseError {
    InvalidBinaryOperator(Token),
    InvalidUnaryOperator(Token),
    InvalidPrimaryToken(Option<TokenType>),
    InvalidLiteral(Token),
    UnclosedGrouping,
}

impl TryFrom<Token> for BinaryOperator {
    type Error = ParseError;

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value.token_type {
            TokenType::Minus => Ok(BinaryOperator::Subtract),
            TokenType::Plus => Ok(BinaryOperator::Add),
            TokenType::ForwardSlash => Ok(BinaryOperator::Divide),
            TokenType::Asterisk => Ok(BinaryOperator::Multiply),
            TokenType::NotEqual => Ok(BinaryOperator::NotEqual),
            TokenType::Equal => Ok(BinaryOperator::Equal),
            TokenType::GreaterThan => Ok(BinaryOperator::GreaterThan),
            TokenType::GreaterThanOrEqual => Ok(BinaryOperator::GreaterThanOrEqual),
            TokenType::LessThan => Ok(BinaryOperator::LessThan),
            TokenType::LessThanOrEqual => Ok(BinaryOperator::LessThanOrEqual),
            _ => Err(InvalidBinaryOperator(value)),
        }
    }
}

impl TryFrom<Token> for UnaryOperator {
    type Error = ParseError;

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value.token_type {
            TokenType::Not => Ok(UnaryOperator::Not),
            TokenType::Minus => Ok(UnaryOperator::Negative),
            _ => Err(InvalidUnaryOperator(value)),
        }
    }
}

impl TryFrom<Token> for Literal {
    type Error = ParseError;

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value.token_type {
            TokenType::NumberLiteral => Ok(Literal::Number(
                value.literal_number.expect("Missing number literal"),
            )),
            TokenType::StringLiteral => Ok(Literal::String(
                value.literal_string.expect("Missing string literal"),
            )),
            TokenType::False => Ok(Literal::False),
            TokenType::True => Ok(Literal::True),
            TokenType::Nil => Ok(Literal::Nil),
            _ => Err(InvalidLiteral(value)),
        }
    }
}

impl Parser {
    fn expression(&mut self) -> Result<Expression, ParseError> {
        self.equality()
    }

    fn equality(&mut self) -> Result<Expression, ParseError> {
        let mut result = self.comparison()?;
        while self.token_match(&[TokenType::NotEqual, TokenType::Equal]) {
            let operator_token = self.previous().clone();
            let right_value = self.comparison()?;
            result = Binary {
                operator: operator_token.try_into()?,
                left_value: Box::new(result.clone()),
                right_value: Box::new(right_value),
            };
        }
        Ok(result)
    }

    fn comparison(&mut self) -> Result<Expression, ParseError> {
        let mut result = self.term()?;
        while self.token_match(&[
            TokenType::GreaterThan,
            TokenType::GreaterThanOrEqual,
            TokenType::LessThan,
            TokenType::LessThanOrEqual,
        ]) {
            let operator_token = self.previous().clone();
            let right_value = self.term()?;
            result = Binary {
                operator: operator_token.try_into()?,
                left_value: Box::new(result.clone()),
                right_value: Box::new(right_value),
            };
        }
        Ok(result)
    }

    fn term(&mut self) -> Result<Expression, ParseError> {
        let mut result = self.factor()?;
        while self.token_match(&[TokenType::Minus, TokenType::Plus]) {
            let operator_token = self.previous().clone();
            let right_value = self.factor()?;
            result = Binary {
                operator: operator_token.try_into()?,
                left_value: Box::new(result.clone()),
                right_value: Box::new(right_value),
            };
        }
        Ok(result)
    }

    fn factor(&mut self) -> Result<Expression, ParseError> {
        let mut result = self.unary()?;
        while self.token_match(&[TokenType::ForwardSlash, TokenType::Asterisk]) {
            let operator_token = self.previous().clone();
            let right_value = self.unary()?;
            result = Binary {
                operator: operator_token.try_into()?,
                left_value: Box::new(result.clone()),
                right_value: Box::new(right_value),
            };
        }
        Ok(result)
    }

    fn unary(&mut self) -> Result<Expression, ParseError> {
        if self.token_match(&[TokenType::Not, TokenType::Minus]) {
            let operator_token = self.previous().clone();
            let operand = self.unary()?;
            Ok(Unary(operator_token.try_into()?, Box::new(operand)))
        } else {
            self.primary()
        }
    }

    fn primary(&mut self) -> Result<Expression, ParseError> {
        if self.token_match(&[
            TokenType::False,
            TokenType::True,
            TokenType::Nil,
            TokenType::NumberLiteral,
            TokenType::StringLiteral,
        ]) {
            Ok(Expression::Literal(self.previous().clone().try_into()?))
        } else if self.token_match(&[TokenType::OpenParenthesis]) {
            let expression = self.expression()?;
            self.consume(&TokenType::CloseParenthesis, UnclosedGrouping)?;
            Ok(Expression::Grouping(Box::new(expression)))
        } else {
            Err(InvalidPrimaryToken(
                self.peek().map(|token| token.token_type),
            ))
        }
    }

    fn consume(
        &mut self,
        token_type: &TokenType,
        conditional_error: ParseError,
    ) -> Result<&Token, ParseError> {
        if self.check(token_type) {
            return Ok(self.advance());
        }
        Err(conditional_error)
    }

    fn token_match(&mut self, types: &[TokenType]) -> bool {
        for token_type in types {
            if self.check(token_type) {
                self.advance();
                return true;
            }
        }
        false
    }

    fn check(&self, token_type: &TokenType) -> bool {
        if let Some(current) = self.peek() {
            current.token_type == *token_type
        } else {
            false
        }
    }

    fn advance(&mut self) -> &Token {
        if !self.at_end() {
            self.current += 1;
        }
        self.previous()
    }

    fn at_end(&self) -> bool {
        if let Some(current) = self.peek() {
            current.token_type == TokenType::Eof
        } else {
            false
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.current)
    }

    fn previous(&self) -> &Token {
        &self.tokens[self.current - 1]
    }
}

#[cfg(test)]
mod tests {
    use crate::grammar::Expression::Literal;
    use crate::grammar::Literal::Number;
    use crate::grammar::{BinaryOperator, Expression};
    use crate::parser::Parser;
    use crate::token::{Token, TokenType};
    use bigdecimal::{BigDecimal, One};
    use std::ops::Deref;

    #[test]
    fn minus_is_left_associative() {
        // given
        let tokens = [
            Token::new_int(5),
            Token::new(TokenType::Minus, "-".to_string(), 0),
            Token::new_int(3),
            Token::new(TokenType::Minus, "-".to_string(), 0),
            Token::new_int(1),
        ]
        .to_vec();
        let mut parser: Parser = tokens.into();

        // when
        let result = parser.expression().expect("Unable to parse expression");

        // then
        if let Expression::Binary {
            operator,
            left_value,
            right_value,
        } = result
        {
            assert_eq!(operator, BinaryOperator::Subtract);
            assert_eq!(right_value, Box::new(Literal(Number(BigDecimal::one()))));
            if let Expression::Binary {
                operator,
                left_value,
                right_value,
            } = left_value.deref()
            {
                assert_eq!(*operator, BinaryOperator::Subtract);
                assert_eq!(*left_value, Box::new(Literal(Number(BigDecimal::from(5)))));
                assert_eq!(*right_value, Box::new(Literal(Number(BigDecimal::from(3)))));
            } else {
                panic!("Expected binary expression, got: {:?}", left_value)
            }
        } else {
            panic!("Expected binary expression, got: {:?}", result);
        }
    }

    #[test]
    fn parse_grouping() {
        // given
        let tokens = [
            Token::new(TokenType::OpenParenthesis, "(".to_string(), 0),
            Token::new_int(6),
            Token::new(TokenType::ForwardSlash, "/".to_string(), 0),
            Token::new_int(3),
            Token::new(TokenType::CloseParenthesis, "(".to_string(), 0),
            Token::new(TokenType::Minus, "-".to_string(), 0),
            Token::new_int(1),
        ]
        .to_vec();
        let mut parser: Parser = tokens.into();

        // when
        let result = parser.expression().expect("Unable to parse expression");

        // then
        if let Expression::Binary {
            operator,
            left_value,
            right_value,
        } = result
        {
            assert_eq!(operator, BinaryOperator::Subtract);
            assert_eq!(right_value, Box::new(Literal(Number(BigDecimal::one()))));
            if let Expression::Grouping(left_value) = *left_value {
                if let Expression::Binary {
                    operator,
                    left_value,
                    right_value,
                } = left_value.deref()
                {
                    assert_eq!(*operator, BinaryOperator::Divide);
                    assert_eq!(*left_value, Box::new(Literal(Number(BigDecimal::from(6)))));
                    assert_eq!(*right_value, Box::new(Literal(Number(BigDecimal::from(3)))));
                } else {
                    panic!("Expected binary expression, got: {:?}", left_value);
                }
            } else {
                panic!("Expected grouping, got: {:?}", left_value);
            }
        } else {
            panic!("Expected binary expression, got: {:?}", result);
        }
    }

    impl Token {
        fn new_int(int: u8) -> Self {
            Self::new_number(format!("{}", int), BigDecimal::from(int), 0)
        }
    }
}
