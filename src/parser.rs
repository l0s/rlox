use crate::grammar::{BinaryOperator, Expression, Literal, Statement, UnaryOperator};
use crate::parser::ParseError::{
    InvalidAssignmentTarget, InvalidBinaryOperator, InvalidLiteral, InvalidPrimaryToken,
    InvalidUnaryOperator, UnclosedGrouping, UnterminatedStatement, VariableNameExpected,
};
use crate::token::TokenType::Semicolon;
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
    /// Statement is missing a semicolon
    UnterminatedStatement,
    VariableNameExpected,
    InvalidAssignmentTarget(Token),
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

impl TryInto<Vec<Statement>> for Parser {
    type Error = ParseError;

    fn try_into(mut self) -> Result<Vec<Statement>, Self::Error> {
        let mut result = vec![];
        while !self.at_end() {
            if let Some(declaration) = self.declaration()? {
                result.push(declaration);
            }
        }
        Ok(result)
    }
}

impl Parser {
    fn declaration(&mut self) -> Result<Option<Statement>, ParseError> {
        if self.token_match(&[TokenType::Variable]) {
            return self.variable_declaration().map(Some);
        }
        match self.statement() {
            Ok(statement) => Ok(Some(statement)),
            Err(e) => {
                eprintln!("Error parsing statement: {:?}", e);
                self.synchronize();
                Err(e)
            }
        }
    }

    fn variable_declaration(&mut self) -> Result<Statement, ParseError> {
        let name_token = self.consume(&TokenType::Identifier, VariableNameExpected)?;
        let identifier = name_token.lexeme.clone();
        let expression = if self.token_match(&[TokenType::Assignment]) {
            Some(self.expression()?)
        } else {
            None
        };
        self.consume(&Semicolon, UnterminatedStatement)?; // TODO distinguish from unterminated print statement
        Ok(Statement::Variable {
            identifier,
            expression,
        })
    }

    fn statement(&mut self) -> Result<Statement, ParseError> {
        if self.token_match(&[TokenType::Print]) {
            self.print_statement()
        } else {
            self.expression_statement()
        }
    }

    fn print_statement(&mut self) -> Result<Statement, ParseError> {
        let value = self.expression()?;
        self.consume(&Semicolon, UnterminatedStatement)?; // TODO distinguish from unterminated expression
        Ok(Statement::Print(value))
    }

    fn expression_statement(&mut self) -> Result<Statement, ParseError> {
        let expression = self.expression()?;
        self.consume(&Semicolon, UnterminatedStatement)?; // TODO distinguish from unterminated print statement
        Ok(Statement::Expression(expression))
    }

    fn expression(&mut self) -> Result<Expression, ParseError> {
        self.assignment()
    }

    fn assignment(&mut self) -> Result<Expression, ParseError> {
        let expression = self.equality()?;
        if self.token_match(&[TokenType::Assignment]) {
            let value = self.assignment()?;
            return if let Expression::Variable(name) = expression.clone() {
                Ok(Expression::Assignment(name, Box::new(value)))
            } else {
                Err(InvalidAssignmentTarget(self.previous().clone()))
            };
        }
        Ok(expression)
    }

    fn equality(&mut self) -> Result<Expression, ParseError> {
        let mut result = self.comparison()?;
        while self.token_match(&[TokenType::NotEqual, TokenType::Equal]) {
            let operator_token = self.previous().clone();
            let right_value = self.comparison()?;
            result = Expression::Binary {
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
            result = Expression::Binary {
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
            result = Expression::Binary {
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
            result = Expression::Binary {
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
            Ok(Expression::Unary(
                operator_token.try_into()?,
                Box::new(operand),
            ))
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
        } else if self.token_match(&[TokenType::Identifier]) {
            Ok(Expression::Variable(self.previous().lexeme.clone()))
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
            true
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.current)
    }

    fn previous(&self) -> &Token {
        &self.tokens[self.current - 1]
    }

    /// In case of a parsing error, advance to a statement boundary to resume parsing
    fn synchronize(&mut self) {
        self.advance();
        while !self.at_end() {
            if self.previous().token_type == Semicolon {
                return;
            }

            if let Some(token) = self.peek() {
                match token.token_type {
                    TokenType::Class
                    | TokenType::Function
                    | TokenType::Variable
                    | TokenType::For
                    | TokenType::If
                    | TokenType::While
                    | TokenType::Print
                    | TokenType::Return => return,
                    _ => {}
                }
            }

            self.advance();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ParseError, Parser};
    use crate::grammar::{BinaryOperator, Expression, Literal, Statement};
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
            assert_eq!(
                right_value,
                Box::new(Expression::Literal(BigDecimal::one().into()))
            );
            if let Expression::Binary {
                operator,
                left_value,
                right_value,
            } = left_value.deref()
            {
                assert_eq!(*operator, BinaryOperator::Subtract);
                assert_eq!(
                    *left_value,
                    Box::new(Expression::Literal(BigDecimal::from(5).into()))
                );
                assert_eq!(
                    *right_value,
                    Box::new(Expression::Literal(BigDecimal::from(3).into()))
                );
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
            assert_eq!(
                right_value,
                Box::new(Expression::Literal(BigDecimal::one().into()))
            );
            if let Expression::Grouping(left_value) = *left_value {
                if let Expression::Binary {
                    operator,
                    left_value,
                    right_value,
                } = left_value.deref()
                {
                    assert_eq!(*operator, BinaryOperator::Divide);
                    assert_eq!(
                        *left_value,
                        Box::new(Expression::Literal(BigDecimal::from(6).into()))
                    );
                    assert_eq!(
                        *right_value,
                        Box::new(Expression::Literal(BigDecimal::from(3).into()))
                    );
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

    #[test]
    fn handle_unclosed_grouping() {
        // given
        let tokens = [
            Token::new(TokenType::OpenParenthesis, "(".to_string(), 0),
            Token::new_int(6),
            Token::new(TokenType::ForwardSlash, "/".to_string(), 0),
            Token::new_int(3),
        ]
        .to_vec();
        let mut parser: Parser = tokens.into();

        // when
        let result = parser.expression().expect_err("Expected parse error");

        // then
        match result {
            ParseError::UnclosedGrouping => {}
            _ => panic!("Expected unclosed grouping error but got: {:?}", result),
        }
    }

    #[test]
    fn parse_assignment() {
        // given
        let tokens = [
            Token::new(TokenType::Identifier, "a".to_string(), 0),
            Token::new(TokenType::Assignment, "=".to_string(), 0),
            Token::new_int(3),
            Token::new(TokenType::Semicolon, ";".to_string(), 0),
        ]
        .to_vec();
        let mut parser: Parser = tokens.into();

        // when
        let result: Vec<Statement> = parser.try_into().expect("Unable to parse assignment");

        // then
        assert_eq!(result.len(), 1);

        assert!(matches!(result.get(0).unwrap(),
            Statement::Expression(Expression::Assignment(name, value))
            if name == "a"
            && matches!(value.as_ref(),
                Expression::Literal(Literal::Number(value))
                if *value == BigDecimal::from(3))));
    }

    #[test]
    fn cannot_assign_to_grouping() {
        // given
        let tokens = [
            Token::new(TokenType::OpenParenthesis, "(".to_string(), 0),
            Token::new(TokenType::Identifier, "a".to_string(), 0),
            Token::new(TokenType::CloseParenthesis, ")".to_string(), 0),
            Token::new(TokenType::Assignment, "=".to_string(), 0),
            Token::new_int(3),
            Token::new(TokenType::Semicolon, ";".to_string(), 0),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: ParseError = <Parser as TryInto<Vec<Statement>>>::try_into(parser)
            .expect_err("Expected parse error");

        // then
        assert!(
            matches!(result, ParseError::InvalidAssignmentTarget(target) if target.token_type == TokenType::NumberLiteral)
        );
    }

    #[test]
    fn cannot_assign_to_expression() {
        // given
        let tokens = [
            Token::new(TokenType::Identifier, "a".to_string(), 0),
            Token::new(TokenType::Plus, "+".to_string(), 0),
            Token::new(TokenType::Identifier, "b".to_string(), 0),
            Token::new(TokenType::Assignment, "=".to_string(), 0),
            Token::new(TokenType::Identifier, "c".to_string(), 0),
            Token::new(TokenType::Semicolon, ";".to_string(), 0),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: ParseError = <Parser as TryInto<Vec<Statement>>>::try_into(parser)
            .expect_err("Expected parse error");

        // then
        assert!(
            matches!(result, ParseError::InvalidAssignmentTarget(target) if target.token_type == TokenType::Identifier)
        );
    }

    impl Token {
        fn new_int(int: u8) -> Self {
            Self::new_number(format!("{}", int), BigDecimal::from(int), 0)
        }
    }
}
