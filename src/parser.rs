use crate::grammar::Expression::AnonymousFunction;
use crate::grammar::{BinaryOperator, Expression, Literal, UnaryOperator};
use crate::parser::FunctionKind::Function;
use crate::parser::ParseError::{
    InvalidAssignmentTarget, InvalidBinaryOperator, InvalidLiteral, InvalidPrimaryToken,
    InvalidUnaryOperator, MissingCondition, MissingForParameters, MissingFunctionBody,
    MissingFunctionName, MissingFunctionParameters, MissingParameterName,
    MissingSemicolonAfterInitializer, MissingSemicolonAfterLoopCondition, TooManyFunctionArguments,
    UnclosedCondition, UnclosedForParameters, UnclosedFunctionParameters, UnclosedGrouping,
    UnterminatedBlock, UnterminatedStatement, VariableNameExpected,
};
use crate::statement::{Statement, VariableDeclarationStatement};
use crate::token::{Token, TokenType};
use either::{Left, Right};
use std::fmt::{Display, Formatter};

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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ParseError {
    InvalidBinaryOperator,
    InvalidUnaryOperator,
    InvalidPrimaryToken(Option<Token>),
    InvalidLiteral,
    UnclosedGrouping,
    /// Statement is missing a semicolon
    UnterminatedStatement(Option<Expression>),
    /// Block is missing the closing brace
    UnterminatedBlock,
    VariableNameExpected,
    InvalidAssignmentTarget,
    /// Missing open parenthesis to define conditional
    MissingCondition,
    /// Missing close parenthesis after conditional
    UnclosedCondition,
    /// For loop is missing the parenthetical section
    MissingForParameters,
    /// For loop's parenthetical section is not closed
    UnclosedForParameters,
    MissingSemicolonAfterLoopCondition,
    MissingSemicolonAfterInitializer,
    /// Missing ')' after arguments
    UnclosedFunctionCall,
    /// Functions cannot have more than 255 arguments
    TooManyFunctionArguments,
    MissingFunctionName(FunctionKind),
    MissingFunctionParameters(FunctionKind),
    UnclosedFunctionParameters(FunctionKind),
    MissingParameterName,
    MissingFunctionBody(FunctionKind),
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            // TODO `Display` depends on `Debug` for `Token` and `Expression`
            InvalidPrimaryToken(token) => write!(f, "Invalid primary token: {:?}", token),
            // TODO add error location details
            InvalidBinaryOperator => write!(f, "Invalid binary operator"),
            InvalidUnaryOperator => write!(f, "Invalid unary operator"),
            InvalidLiteral => write!(f, "Invalid literal"),
            UnclosedGrouping => write!(f, "Unclosed grouping"),
            UnterminatedStatement(expression) => {
                write!(f, "Unterminated statement: {:?}", expression)
            }
            UnterminatedBlock => write!(f, "Unterminated block"),
            VariableNameExpected => write!(f, "Variable name expected"),
            InvalidAssignmentTarget => write!(f, "Invalid assignment target"),
            MissingCondition => write!(f, "Missing condition"),
            UnclosedCondition => write!(f, "Unclosed condition"),
            MissingForParameters => write!(f, "Missing `for` parameters"),
            UnclosedForParameters => write!(f, "Unclosed `for` parameters"),
            MissingSemicolonAfterLoopCondition => {
                write!(f, "Missing semicolon after loop condition")
            }
            MissingSemicolonAfterInitializer => {
                write!(f, "Missing semicolon after loop initializer")
            }
            Self::UnclosedFunctionCall => write!(f, "Missing ')' after function arguments"),
            TooManyFunctionArguments => write!(f, "Too many function arguments"),
            MissingFunctionName(kind) => write!(f, "Missing name for {}", kind),
            MissingFunctionParameters(kind) => write!(f, "Missing parameters for {}", kind),
            UnclosedFunctionParameters(kind) => write!(f, "Missing ')' after {} parameters", kind),
            MissingParameterName => write!(f, "Missing parameter name"),
            MissingFunctionBody(kind) => write!(f, "Missing body for {}", kind),
        }
    }
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
            _ => Err(InvalidBinaryOperator),
        }
    }
}

impl TryFrom<Token> for UnaryOperator {
    type Error = ParseError;

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value.token_type {
            TokenType::Not => Ok(UnaryOperator::Not),
            TokenType::Minus => Ok(UnaryOperator::Negative),
            _ => Err(InvalidUnaryOperator),
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
            _ => Err(InvalidLiteral),
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

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum FunctionKind {
    Function,
    // Method,
}

impl Display for FunctionKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Function => write!(f, "function"),
            // Self::Method => write!(f, "method"),
        }
    }
}

impl Parser {
    fn declaration(&mut self) -> Result<Option<Statement>, ParseError> {
        if self.token_match(&[TokenType::Function]) {
            return self.function(Function).map(Some);
        }
        if self.token_match(&[TokenType::Variable]) {
            return self.variable_declaration().map(Some);
        }
        match self.statement() {
            Ok(statement) => Ok(Some(statement)),
            Err(e) => {
                self.synchronize();
                Err(e)
            }
        }
    }

    fn function(&mut self, kind: FunctionKind) -> Result<Statement, ParseError> {
        let name = self
            .consume(&TokenType::Identifier, MissingFunctionName(kind))?
            .lexeme
            .clone();
        let (parameter_names, statements) = self.function_definition(Function)?;
        Ok(Statement::Function {
            name,
            parameter_names,
            statements,
        })
    }

    /// Parse a variable declaration and optional initialization including the trailing semicolon.
    ///
    /// Returns:
    /// - `Ok(Statement)` - if the entire declaration and optional can be parsed
    /// - `Err(ParseError)` - if the variable name is not defined or the initialization expression
    ///   cannot be parsed
    fn variable_declaration(&mut self) -> Result<Statement, ParseError> {
        let name_token = self.consume(&TokenType::Identifier, VariableNameExpected)?;
        let identifier = name_token.lexeme.clone();
        let expression = if self.token_match(&[TokenType::Assignment]) {
            Some(self.expression()?)
        } else {
            None
        };
        self.consume(
            &TokenType::Semicolon,
            UnterminatedStatement(expression.clone()),
        )?; // TODO distinguish from unterminated print statement
        Ok(Statement::VariableDeclaration(
            VariableDeclarationStatement {
                identifier,
                expression,
            },
        ))
    }

    fn statement(&mut self) -> Result<Statement, ParseError> {
        if self.token_match(&[TokenType::For]) {
            self.for_statement()
        } else if self.token_match(&[TokenType::If]) {
            self.if_statement()
        } else if self.token_match(&[TokenType::Print]) {
            self.print_statement()
        } else if self.token_match(&[TokenType::Return]) {
            self.return_statement()
        } else if self.token_match(&[TokenType::While]) {
            self.while_statement()
        } else if self.token_match(&[TokenType::OpenBrace]) {
            self.block()
        } else if self.token_match(&[TokenType::Break, TokenType::Continue]) {
            let result = match self.previous().clone().token_type {
                TokenType::Break => Statement::Break,
                TokenType::Continue => Statement::Continue,
                _ => unreachable!("Mismatch with previous token"),
            };
            self.consume(&TokenType::Semicolon, UnterminatedStatement(None))?;
            Ok(result)
        } else {
            self.expression_statement()
        }
    }

    fn return_statement(&mut self) -> Result<Statement, ParseError> {
        let value = if self.check(&TokenType::Semicolon) {
            None
        } else {
            Some(self.expression()?)
        };

        // TODO optimization: only clone if necessary
        self.consume(&TokenType::Semicolon, UnterminatedStatement(value.clone()))?;

        Ok(Statement::Return(value))
    }

    fn for_statement(&mut self) -> Result<Statement, ParseError> {
        self.consume(&TokenType::OpenParenthesis, MissingForParameters)?;
        let initializer = if self.token_match(&[TokenType::Semicolon]) {
            None
        } else if self.token_match(&[TokenType::Variable]) {
            let declaration = self.variable_declaration()?;
            if let Statement::VariableDeclaration(declaration) = declaration {
                Some(Left(declaration))
            } else {
                panic!(
                    "Invalid variable declaration in `for` loop: {:?}",
                    declaration
                );
            }
        } else {
            let result = Some(Right(self.expression()?));
            self.consume(&TokenType::Semicolon, MissingSemicolonAfterInitializer)?;
            result
        };

        let condition = if !self.check(&TokenType::Semicolon) {
            Some(self.expression()?)
        } else {
            None
        };
        self.consume(&TokenType::Semicolon, MissingSemicolonAfterLoopCondition)?;

        let increment = if !self.check(&TokenType::CloseParenthesis) {
            Some(self.expression()?)
        } else {
            None
        };
        self.consume(&TokenType::CloseParenthesis, UnclosedForParameters)?;

        let statement = Box::new(self.statement()?);

        Ok(Statement::For {
            initializer,
            condition,
            increment,
            statement,
        })
    }

    fn while_statement(&mut self) -> Result<Statement, ParseError> {
        self.consume(&TokenType::OpenParenthesis, MissingCondition)?;
        let condition = self.expression()?;
        self.consume(&TokenType::CloseParenthesis, UnclosedCondition)?;
        let body = self.statement()?;
        Ok(Statement::While(condition, Box::new(body)))
    }

    fn if_statement(&mut self) -> Result<Statement, ParseError> {
        self.consume(&TokenType::OpenParenthesis, MissingCondition)?;
        let condition = self.expression()?;
        self.consume(&TokenType::CloseParenthesis, UnclosedCondition)?;
        let then_branch = Box::new(self.statement()?);
        let else_branch = if self.token_match(&[TokenType::Else]) {
            Some(Box::new(self.statement()?))
        } else {
            None
        };

        Ok(Statement::If {
            condition,
            then_branch,
            else_branch,
        })
    }

    fn block(&mut self) -> Result<Statement, ParseError> {
        let mut statements = vec![];

        while !self.check(&TokenType::CloseBrace) && !self.at_end() {
            if let Some(declaration) = self.declaration()? {
                statements.push(declaration);
            }
        }

        self.consume(&TokenType::CloseBrace, UnterminatedBlock)?;

        Ok(Statement::Block(statements))
    }

    fn print_statement(&mut self) -> Result<Statement, ParseError> {
        let value = self.expression()?;
        self.consume(
            &TokenType::Semicolon,
            UnterminatedStatement(Some(value.clone())),
        )?; // TODO distinguish from unterminated expression
        Ok(Statement::Print(value))
    }

    fn expression_statement(&mut self) -> Result<Statement, ParseError> {
        let expression = self.expression()?;
        self.consume(
            &TokenType::Semicolon,
            UnterminatedStatement(Some(expression.clone())),
        )?; // TODO distinguish from unterminated print statement
        Ok(Statement::Expression(expression))
    }

    fn expression(&mut self) -> Result<Expression, ParseError> {
        if self.token_match(&[TokenType::Function]) {
            self.anonymous_function()
        } else {
            self.assignment()
        }
    }

    fn function_definition(
        &mut self,
        kind: FunctionKind,
    ) -> Result<(Vec<String>, Vec<Statement>), ParseError> {
        self.consume(&TokenType::OpenParenthesis, MissingFunctionParameters(kind))?;
        let mut parameters = vec![];
        if !self.check(&TokenType::CloseParenthesis) {
            loop {
                if parameters.len() >= 255 {
                    return Err(TooManyFunctionArguments);
                }
                let parameter_token = self.consume(&TokenType::Identifier, MissingParameterName)?;
                parameters.push(parameter_token.clone());
                if !self.token_match(&[TokenType::Comma]) {
                    break;
                }
            }
        }
        let parameters = parameters
            .into_iter()
            .map(|parameter| parameter.lexeme)
            .collect();
        self.consume(
            &TokenType::CloseParenthesis,
            UnclosedFunctionParameters(kind),
        )?;
        self.consume(&TokenType::OpenBrace, MissingFunctionBody(kind))?;
        let statements = vec![self.block()?];
        Ok((parameters, statements))
    }

    fn anonymous_function(&mut self) -> Result<Expression, ParseError> {
        let (parameter_names, statements) = self.function_definition(Function)?;

        Ok(AnonymousFunction {
            parameter_names,
            statements,
        })
    }

    fn assignment(&mut self) -> Result<Expression, ParseError> {
        let expression = self.or()?;
        if self.token_match(&[TokenType::Assignment]) {
            let value = self.assignment()?;
            return if let Expression::VariableReference(name) = expression.clone() {
                Ok(Expression::Assignment(name, Box::new(value)))
            } else {
                Err(InvalidAssignmentTarget)
            };
        }
        Ok(expression)
    }

    /// Parse the expression at the current cursor as a disjunction or an expression with the next
    /// higher level of precedence. This will advance the cursor on success.
    fn or(&mut self) -> Result<Expression, ParseError> {
        let mut result = self.and()?;
        while self.token_match(&[TokenType::Or]) {
            result = Expression::Logical {
                operator: BinaryOperator::Or,
                left_value: Box::new(result),
                right_value: Box::new(self.and()?),
            };
        }
        Ok(result)
    }

    fn and(&mut self) -> Result<Expression, ParseError> {
        let mut result = self.equality()?;
        while self.token_match(&[TokenType::And]) {
            result = Expression::Logical {
                operator: BinaryOperator::And,
                left_value: Box::new(result),
                right_value: Box::new(self.equality()?),
            };
        }
        Ok(result)
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
            self.call()
        }
    }

    fn call(&mut self) -> Result<Expression, ParseError> {
        let mut expression = self.primary()?;

        loop {
            if self.token_match(&[TokenType::OpenParenthesis]) {
                expression = self.finish_call(expression)?;
            } else {
                break;
            }
        }

        Ok(expression)
    }

    fn finish_call(&mut self, callee: Expression) -> Result<Expression, ParseError> {
        let mut arguments = vec![];

        if !self.check(&TokenType::CloseParenthesis) {
            loop {
                if arguments.len() >= 255 {
                    // FIXME this should not be a parse error
                    // TODO create warning mechanism
                    return Err(TooManyFunctionArguments);
                }
                arguments.push(self.expression()?);
                if !self.token_match(&[TokenType::Comma]) {
                    break;
                }
            }
        }

        self.consume(
            &TokenType::CloseParenthesis,
            ParseError::UnclosedFunctionCall,
        )?;

        Ok(Expression::Call {
            callee: Box::new(callee),
            arguments,
        })
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
            Ok(Expression::VariableReference(
                self.previous().lexeme.clone(),
            ))
        } else {
            Err(InvalidPrimaryToken(self.peek().cloned()))
        }
    }

    /// Expect the current token to match the expected type and if so, advance the cursor.
    ///
    /// Parameters:
    /// - `token_type` - the expected type which will advance the cursor
    /// - `conditional_error` - the parse error to return if the current token is not the expected
    ///   type.
    ///
    /// Returns:
    /// - `Ok(&Token)` - if the token at the cursor matches the expected type and the cursor has
    ///   since been advanced
    /// - `Err(ParseError)` - if the token at the cursor did not match the expected type and the
    ///   cursor has not been modified
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

    /// Check if the current token matches one of the expected types and if so, advance the cursor
    ///
    /// Parameters:
    /// - `types` - any of the token types to consider a match
    ///
    /// Returns:
    /// - `true` - if the token at the cursor matched one of `types` and the cursor was advanced
    /// - `false` - if none of the `types` matched the token at the cursor and the cursor was *not*
    ///   advanced.
    fn token_match(&mut self, types: &[TokenType]) -> bool {
        for token_type in types {
            if self.check(token_type) {
                self.advance();
                return true;
            }
        }
        false
    }

    /// Check if the token at the cursor matches the expected type. This does not modify the cursor.
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
            if self.previous().token_type == TokenType::Semicolon {
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
    use crate::grammar::{BinaryOperator, Expression, Literal};
    use crate::parser::ParseError::{MissingCondition, UnclosedCondition};
    use crate::statement::{Statement, VariableDeclarationStatement};
    use crate::token::{Token, TokenType};
    use bigdecimal::{BigDecimal, One, Zero};
    use either::{Left, Right};
    use std::ops::Deref;

    #[test]
    fn minus_is_left_associative() {
        // given
        let tokens = [
            Token::new_int(5),
            TokenType::Minus.into(),
            Token::new_int(3),
            TokenType::Minus.into(),
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
            TokenType::OpenParenthesis.into(),
            Token::new_int(6),
            TokenType::ForwardSlash.into(),
            Token::new_int(3),
            TokenType::CloseParenthesis.into(),
            TokenType::Minus.into(),
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
            TokenType::OpenParenthesis.into(),
            Token::new_int(6),
            TokenType::ForwardSlash.into(),
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
            Token::new(TokenType::Identifier, "a".to_string(), 0, 0),
            TokenType::Assignment.into(),
            Token::new_int(3),
            TokenType::Semicolon.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

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
            TokenType::OpenParenthesis.into(),
            Token::new(TokenType::Identifier, "a".to_string(), 0, 1),
            TokenType::CloseParenthesis.into(),
            TokenType::Assignment.into(),
            Token::new_int(3),
            TokenType::Semicolon.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: ParseError = <Parser as TryInto<Vec<Statement>>>::try_into(parser)
            .expect_err("Expected parse error");

        // then
        assert_eq!(result, ParseError::InvalidAssignmentTarget);
    }

    #[test]
    fn cannot_assign_to_expression() {
        // given
        let tokens = [
            Token::new(TokenType::Identifier, "a".to_string(), 0, 0),
            TokenType::Plus.into(),
            Token::new(TokenType::Identifier, "b".to_string(), 0, 2),
            TokenType::Assignment.into(),
            Token::new(TokenType::Identifier, "c".to_string(), 0, 4),
            TokenType::Semicolon.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: ParseError = <Parser as TryInto<Vec<Statement>>>::try_into(parser)
            .expect_err("Expected parse error");

        // then
        assert_eq!(result, ParseError::InvalidAssignmentTarget);
    }

    #[test]
    fn else_bound_to_nearest_if() {
        // given
        let tokens = [
            TokenType::If.into(),
            TokenType::OpenParenthesis.into(),
            TokenType::True.into(),
            TokenType::CloseParenthesis.into(),
            TokenType::If.into(),
            TokenType::OpenParenthesis.into(),
            TokenType::True.into(),
            TokenType::CloseParenthesis.into(),
            TokenType::Print.into(),
            Token::new(TokenType::Identifier, "whenTrue".to_string(), 0, 33),
            TokenType::Semicolon.into(),
            TokenType::Else.into(),
            TokenType::Print.into(),
            Token::new(TokenType::Identifier, "whenFalse".to_string(), 0, 46),
            TokenType::Semicolon.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: Vec<Statement> = parser.try_into().expect("Unable to parse assignment");

        // then
        assert_eq!(result.len(), 1);
        let statement = &result[0];
        assert!(matches!(
            statement,
            Statement::If {
                condition,
                then_branch,
                else_branch,
            } if matches!(condition, Expression::Literal(Literal::True))
            && matches!(
                then_branch.as_ref(),
                Statement::If {
                    condition,
                    then_branch,
                    else_branch
                } if matches!(condition, Expression::Literal(Literal::True))
                && matches!(
                    then_branch.as_ref(),
                    Statement::Print(when_true) if matches!(
                        when_true,
                        Expression::VariableReference(when_true) if when_true == "whenTrue"
                    )
                )
                && matches!(
                    else_branch,
                    Some(else_branch) if matches!(
                        else_branch.as_ref(),
                        Statement::Print(when_false) if matches!(
                            when_false,
                            Expression::VariableReference(when_false) if when_false == "whenFalse"
                        )
                    )
                )
            )
            && else_branch.is_none()
        ))
    }

    #[test]
    fn parse_disjunction() {
        // given
        let tokens = [
            TokenType::Print.into(),
            Token::from("hi".to_string()),
            TokenType::Or.into(),
            Token::from(2u8),
            TokenType::Semicolon.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: Vec<Statement> = parser.try_into().expect("Unable to parse assignment");

        // then
        assert_eq!(result.len(), 1);
        assert!(matches!(
            &result[0],
            Statement::Print(expression)
            if matches!(
                expression,
                Expression::Logical {
                    operator,
                    left_value,
                    right_value,
                }
                if operator == &BinaryOperator::Or
                && matches!(
                    left_value.as_ref(),
                    Expression::Literal(left_value)
                    if matches!(
                        left_value,
                        Literal::String(left_value)
                        if left_value == "hi"
                    )
                )
                && matches!(
                    right_value.as_ref(),
                    Expression::Literal(right_value)
                    if matches!(
                        right_value,
                        Literal::Number(right_value)
                        if right_value == &BigDecimal::from(2u8)
                    )
                )
            )
        ))
    }

    #[test]
    fn parse_conjunction() {
        // given
        let tokens = [
            TokenType::Print.into(),
            TokenType::Nil.into(),
            TokenType::And.into(),
            Token::from("hi".to_string()),
            TokenType::Semicolon.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: Vec<Statement> = parser.try_into().expect("Unable to parse assignment");

        // then
        assert_eq!(result.len(), 1);
        assert!(matches!(
            &result[0],
            Statement::Print(expression)
            if matches!(
                expression,
                Expression::Logical {
                    operator,
                    left_value,
                    right_value,
                }
                if operator == &BinaryOperator::And
                && matches!(
                    left_value.as_ref(),
                    Expression::Literal(left_value)
                    if matches!(left_value, Literal::Nil)
                )
                && matches!(
                    right_value.as_ref(),
                    Expression::Literal(right_value)
                    if matches!(
                        right_value,
                        Literal::String(right_value)
                        if right_value == "hi"
                    )
                )
            )
        ))
    }

    #[test]
    fn parse_while_loop() {
        // given
        let tokens = [
            TokenType::While.into(),
            TokenType::OpenParenthesis.into(),
            Token::new(TokenType::Identifier, "c".to_string(), 0, 8),
            TokenType::LessThan.into(),
            8u8.into(),
            TokenType::CloseParenthesis.into(),
            TokenType::OpenBrace.into(),
            Token::new(TokenType::Identifier, "c".to_string(), 0, 15),
            TokenType::Assignment.into(),
            Token::new(TokenType::Identifier, "c".to_string(), 0, 18),
            TokenType::Plus.into(),
            1u8.into(),
            TokenType::Semicolon.into(),
            TokenType::CloseBrace.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: Vec<Statement> = parser.try_into().expect("Unable to parse while loop");

        // then
        assert_eq!(result.len(), 1);
        assert!(matches!(
            &result[0],
            Statement::While(
                condition,
                block,
            )
            if matches!(
                condition,
                Expression::Binary {
                    operator,
                    left_value,
                    right_value,
                }
                if operator == &BinaryOperator::LessThan
                    && matches!(
                        left_value.as_ref(),
                        Expression::VariableReference(name)
                        if name == "c"
                    )
                    && matches!(
                        right_value.as_ref(),
                        Expression::Literal(Literal::Number(value))
                        if value == &BigDecimal::from(8u8)
                    )
            ) && matches!(
                block.as_ref(),
                Statement::Block(statements)
                if statements.len() == 1
                    && matches!(
                        &statements[0],
                        Statement::Expression(Expression::Assignment(name, expression))
                        if name == "c"
                            && matches!(
                                expression.as_ref(),
                                Expression::Binary {
                                    operator,
                                    left_value,
                                    right_value,
                                }
                                if operator == &BinaryOperator::Add
                                    && matches!(left_value.as_ref(), Expression::VariableReference(name) if name == "c")
                                    && matches!(right_value.as_ref(), Expression::Literal(Literal::Number(value)) if value == &BigDecimal::one())
                            )
                    )
            )
        ));
    }

    #[test]
    fn while_loop_missing_open_parenthesis() {
        // given
        let tokens = [
            TokenType::While.into(),
            Token::new(TokenType::Identifier, "c".to_string(), 0, 7),
            TokenType::LessThan.into(),
            8u8.into(),
            TokenType::CloseParenthesis.into(),
            TokenType::OpenBrace.into(),
            Token::new(TokenType::Identifier, "c".to_string(), 0, 13),
            TokenType::Assignment.into(),
            Token::new(TokenType::Identifier, "c".to_string(), 0, 16),
            TokenType::Plus.into(),
            1u8.into(),
            TokenType::Semicolon.into(),
            TokenType::CloseBrace.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: ParseError = <Parser as TryInto<Vec<Statement>>>::try_into(parser)
            .expect_err("Expected parse error");

        // then
        assert_eq!(result, MissingCondition);
    }

    #[test]
    fn while_loop_missing_close_parenthesis() {
        // given
        let tokens = [
            TokenType::While.into(),
            TokenType::OpenParenthesis.into(),
            Token::new(TokenType::Identifier, "c".to_string(), 0, 8),
            TokenType::LessThan.into(),
            8u8.into(),
            TokenType::OpenBrace.into(),
            Token::new(TokenType::Identifier, "c".to_string(), 0, 14),
            TokenType::Assignment.into(),
            Token::new(TokenType::Identifier, "c".to_string(), 0, 17),
            TokenType::Plus.into(),
            1u8.into(),
            TokenType::Semicolon.into(),
            TokenType::CloseBrace.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: ParseError = <Parser as TryInto<Vec<Statement>>>::try_into(parser)
            .expect_err("Expected parse error");

        // then
        assert_eq!(result, UnclosedCondition);
    }

    #[test]
    fn empty_for_loop() {
        // given
        let tokens = [
            // `for (;;) {}`
            TokenType::For.into(),
            TokenType::OpenParenthesis.into(),
            TokenType::Semicolon.into(),
            TokenType::Semicolon.into(),
            TokenType::CloseParenthesis.into(),
            TokenType::OpenBrace.into(),
            TokenType::CloseBrace.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: Vec<Statement> = parser.try_into().expect("Unable to parse for loop");

        // then
        assert_eq!(result.len(), 1);
        assert!(matches!(
            &result[0],
            Statement::For {
                initializer,
                condition,
                increment,
                statement
            }
            if initializer.is_none() && condition.is_none() && increment.is_none()
            && matches!(
                statement.as_ref(),
                Statement::Block(statements)
                if statements.is_empty()
            )
        ));
    }

    #[test]
    fn for_loop_with_declaration() {
        // given
        let tokens: Vec<Token> = [
            // `for (var i = 0; ;) {}`
            TokenType::For.into(),
            TokenType::OpenParenthesis.into(),
            TokenType::Variable.into(),
            Token::new(TokenType::Identifier, "i".to_string(), 0, 9),
            TokenType::Assignment.into(),
            0u8.into(),
            TokenType::Semicolon.into(),
            TokenType::Semicolon.into(),
            TokenType::CloseParenthesis.into(),
            TokenType::OpenBrace.into(),
            TokenType::CloseBrace.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: Vec<Statement> = parser.try_into().expect("Unable to parse for loop");

        // then
        assert_eq!(result.len(), 1);
        assert!(matches!(
            &result[0],
            Statement::For {
                initializer,
                condition,
                increment,
                statement
            }
            if condition.is_none() && increment.is_none()
            && matches!(
                initializer,
                Some(Left(VariableDeclarationStatement {
                    identifier,
                    expression,
                }))
                if identifier == "i"
                && matches!(
                    expression,
                    Some(Expression::Literal(Literal::Number(initial_value)))
                    if initial_value == &BigDecimal::zero()
                )
            )
            && matches!(
                statement.as_ref(),
                Statement::Block(statements)
                if statements.is_empty()
            )
        ));
    }

    #[test]
    fn for_loop_with_initialization() {
        // given
        let tokens: Vec<Token> = [
            // `for (i = 1; ;) {}`
            TokenType::For.into(),
            TokenType::OpenParenthesis.into(),
            Token::new(TokenType::Identifier, "i".to_string(), 0, 5),
            TokenType::Assignment.into(),
            1u8.into(),
            Token::new(TokenType::Semicolon, ";".into(), 0, 10),
            Token::new(TokenType::Semicolon, ";".into(), 0, 12),
            TokenType::CloseParenthesis.into(),
            TokenType::OpenBrace.into(),
            TokenType::CloseBrace.into(),
        ]
        .to_vec();
        let parser: Parser = tokens.into();

        // when
        let result: Vec<Statement> = parser.try_into().expect("Unable to parse for loop");

        // then
        assert_eq!(result.len(), 1);
        assert!(matches!(
            &result[0],
            Statement::For {
                initializer,
                condition,
                increment,
                statement
            }
            if condition.is_none() && increment.is_none()
            && matches!(
                initializer,
                Some(Right(Expression::Assignment (
                    identifier,
                    expression,
                )))
                if identifier == "i"
                && matches!(
                    expression.as_ref(),
                    Expression::Literal(Literal::Number(initial_value))
                    if initial_value == &BigDecimal::one()
                )
            )
            && matches!(
                statement.as_ref(),
                Statement::Block(statements)
                if statements.is_empty()
            )
        ));
    }

    impl From<TokenType> for Token {
        fn from(value: TokenType) -> Self {
            match value {
                TokenType::OpenParenthesis => Self::new(value, "(".to_string(), 0, 0),
                TokenType::CloseParenthesis => Self::new(value, ")".to_string(), 0, 0),
                TokenType::OpenBrace => Self::new(value, "{".to_string(), 0, 0),
                TokenType::CloseBrace => Self::new(value, ")".to_string(), 0, 0),
                TokenType::Comma => Self::new(value, ",".to_string(), 0, 0),
                TokenType::Period => Self::new(value, ".".to_string(), 0, 0),
                TokenType::Minus => Self::new(value, "-".to_string(), 0, 0),
                TokenType::Plus => Self::new(value, "+".to_string(), 0, 0),
                TokenType::Semicolon => Self::new(value, ";".to_string(), 0, 0),
                TokenType::ForwardSlash => Self::new(value, "/".to_string(), 0, 0),
                TokenType::Asterisk => Self::new(value, "*".to_string(), 0, 0),
                TokenType::Not => Self::new(value, "!".to_string(), 0, 0),
                TokenType::NotEqual => Self::new(value, "!=".to_string(), 0, 0),
                TokenType::Assignment => Self::new(value, "=".to_string(), 0, 0),
                TokenType::Equal => Self::new(value, "==".to_string(), 0, 0),
                TokenType::GreaterThan => Self::new(value, ">".to_string(), 0, 0),
                TokenType::GreaterThanOrEqual => Self::new(value, ">=".to_string(), 0, 0),
                TokenType::LessThan => Self::new(value, "<".to_string(), 0, 0),
                TokenType::LessThanOrEqual => Self::new(value, "<=".to_string(), 0, 0),
                TokenType::And => Self::new(value, "and".to_string(), 0, 0),
                // TokenType::Class => Self::new(value, "class".to_string(), 0, 0),
                TokenType::Else => Self::new(value, "else".to_string(), 0, 0),
                TokenType::False => Self::new(value, "false".to_string(), 0, 0),
                // TokenType::Function => Self::new(value, "fun".to_string(), 0, 0),
                TokenType::For => Self::new(value, "for".to_string(), 0, 0),
                TokenType::If => Self::new(value, "if".to_string(), 0, 0),
                TokenType::Nil => Self::new(value, "nil".to_string(), 0, 0),
                TokenType::Or => Self::new(value, "or".to_string(), 0, 0),
                TokenType::Print => Self::new(value, "print".to_string(), 0, 0),
                // TokenType::Return => Self::new(value, "return".to_string(), 0, 0),
                // TokenType::Super => Self::new(value, "super".to_string(), 0, 0),
                TokenType::This => Self::new(value, "this".to_string(), 0, 0),
                TokenType::True => Self::new(value, "true".to_string(), 0, 0),
                TokenType::Variable => Self::new(value, "var".to_string(), 0, 0),
                TokenType::While => Self::new(value, "while".to_string(), 0, 0),
                TokenType::Break => Self::new(value, "break".to_string(), 0, 0),
                TokenType::Continue => Self::new(value, "continue".to_string(), 0, 0),
                _ => panic!(
                    "token type {:?} cannot be coerced into a token without more information",
                    value
                ),
            }
        }
    }

    impl Token {
        fn new_int(int: u8) -> Self {
            Self::new_number(format!("{}", int), BigDecimal::from(int), 0, 0)
        }
    }

    impl From<String> for Token {
        fn from(value: String) -> Self {
            Self::new_string(format!("\"{}\"", &value), value, 0, 0)
        }
    }

    impl From<u8> for Token {
        fn from(value: u8) -> Self {
            Self::new_int(value)
        }
    }
}
