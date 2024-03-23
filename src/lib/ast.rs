use std::fmt::Display;

pub struct Program {
    pub statements: Vec<Statement>,
}

pub enum Statement {
    Let { ident: String, expr: Expression },
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Let { ident, expr } => write!(f, "Let {ident} = {expr}"),
        }
    }
}

#[derive(Debug)]
pub enum Expression {
    Literal(String),
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Literal(s) => write!(f, "Literal {s}"),
        }
    }
}
