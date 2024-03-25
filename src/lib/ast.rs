use std::fmt::Display;

pub struct Program {
    pub statements: Vec<Statement>,
}

pub enum Statement {
    Expression { expr: Expression },
    Let { ident: String, expr: Expression },
    Return { expr: Expression },
}

#[derive(Debug)]
pub enum Expression {
    Ident(String),
    Literal(Literal),
    Prefix(Prefix, Box<Expression>),
}

#[derive(Debug)]
pub enum Literal {
    Int(isize),
    String(String),
}

#[derive(PartialEq, PartialOrd, Eq)]
pub enum Precedence {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
}

#[derive(Debug)]
pub enum Prefix {
    Negative,
    Not,
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Expression { expr } => write!(f, "ExpressionStatement {expr}"),
            Self::Let { ident, expr } => write!(f, "Let {ident} = {expr}"),
            Self::Return { expr } => write!(f, "Return {expr}"),
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(i) => write!(f, "Int {i}"),
            Self::String(s) => write!(f, "String \"{s}\""),
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ident(s) => write!(f, "Ident {s}"),
            Self::Literal(l) => write!(f, "Literal {l}"),
            Self::Prefix(p, b) => write!(f, "Prefix {p} on expr {b}"),
        }
    }
}

impl Display for Prefix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Negative => write!(f, "Negative"),
            Self::Not => write!(f, "Not"),
        }
    }
}
