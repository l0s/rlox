use std::fmt::{Display, Formatter};
use bigdecimal::BigDecimal;

pub(crate) enum Expression {
    LiteralExpression(Literal),
    UnaryExpression(UnaryOperator, Box<Expression>),
    BinaryExpression {
        operator: BinaryOperator,
        left_value: Box<Expression>,
        right_value: Box<Expression>,
    },
    Grouping(Box<Expression>),
}

pub(crate) enum BinaryOperator {
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    Plus,
    Minus,
    Multiply,
    Divide,
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Equal => f.write_str("Equal"),
            Self::NotEqual => f.write_str("NotEqual"),
            Self::LessThan => f.write_str("LessThan"),
            Self::GreaterThan => f.write_str("GreaterThan"),
            Self::LessThanOrEqual => f.write_str("LessThanOrEqual"),
            Self::GreaterThanOrEqual => f.write_str("GreaterThanOrEqual"),
            Self::Plus => f.write_str("Plus"),
            Self::Minus => f.write_str("Minus"),
            Self::Multiply => f.write_str("Multiply"),
            Self::Divide => f.write_str("Divide"),
        }
    }
}

pub(crate) enum UnaryOperator {
    Negative,
    Not,
}

pub(crate) enum Literal {
    NumberLiteral(BigDecimal),
    StringLiteral(String),
    True,
    False,
    Nil,
}

pub(crate) enum DataType {
    NumberType,
    StringType,
    BooleanType,
}

pub fn to_prefix_string(expression: &Expression) -> String {
    match expression {
        Expression::LiteralExpression(literal) => {
            match literal {
                Literal::NumberLiteral(number) => number.to_string(),
                Literal::StringLiteral(string) => string.clone(),
                Literal::True => "true".to_string(),
                Literal::False => "false".to_string(),
                Literal::Nil => "nil".to_string(),
            }
        },
        Expression::UnaryExpression(operator, expression) => {
            match operator {
                UnaryOperator::Negative => format!("(- {})", to_prefix_string(expression)),
                UnaryOperator::Not => format!("(! {})", to_prefix_string(expression)),
            }
        },
        Expression::BinaryExpression { operator, left_value, right_value } => {
            let symbol = match operator {
                BinaryOperator::Equal => "==",
                BinaryOperator::NotEqual => "!=",
                BinaryOperator::LessThan => "<",
                BinaryOperator::GreaterThan => ">",
                BinaryOperator::LessThanOrEqual => "<=",
                BinaryOperator::GreaterThanOrEqual => ">=",
                BinaryOperator::Plus => "+",
                BinaryOperator::Minus => "-",
                BinaryOperator::Multiply => "*",
                BinaryOperator::Divide => "/",
            };
            format!("({} {} {})", symbol, to_prefix_string(left_value), to_prefix_string(right_value))
        },
        Expression::Grouping(expression) => format!("(group {})", to_prefix_string(expression)),
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use bigdecimal::BigDecimal;
    use super::BinaryOperator::Multiply;
    use super::Expression::{BinaryExpression, Grouping, LiteralExpression, UnaryExpression};
    use super::Literal::NumberLiteral;
    use super::to_prefix_string;
    use super::UnaryOperator::Negative;

    #[test]
    pub fn test() {
        // given
        let ast = BinaryExpression {
            operator: Multiply,
            left_value: Box::new(UnaryExpression(Negative, Box::new(LiteralExpression(NumberLiteral(BigDecimal::from_str("123").unwrap()))))),
            right_value: Box::new(Grouping(Box::new(LiteralExpression(NumberLiteral(BigDecimal::from_str("45.67").unwrap())))))
        };

        // when
        let result = to_prefix_string(&ast);

        // then
        assert_eq!(result, "(* (- 123) (group 45.67))".to_string());
    }
}