use std::fmt::{Display, Write};

/// The program, consting of the [`Statement`] our parser creates
pub struct Program {
    pub statements: Vec<Statement>,
}

/// The differnt types of statements in the language
#[derive(Debug, PartialEq, Eq)]
pub enum Statement {
    Expression(Expression),
    Let { ident: String, expr: Expression },
    Return(Expression),
}

/// The different types of Expressions in the language
#[derive(Debug, PartialEq, Eq)]
pub enum Expression {
    Ident(String),
    Infix(Infix, Box<Expression>, Box<Expression>),
    Literal(Literal),
    Prefix(Prefix, Box<Expression>),
    If {
        cond: Box<Expression>,
        then: BlockStatement,
        alt: BlockStatement,
    },
    Call {
        args: Vec<Expression>,
        ident: Box<Expression>,
    },
    Function {
        body: BlockStatement,
        params: Vec<String>,
    },
}

/// The literal values the language represents
#[derive(Debug, PartialEq, Eq)]
pub enum Literal {
    Boolean(bool),
    Int(usize),
    String(String),
}

/// Precedence to bse used by our Operator-Precedence parser
///
/// Implements [`PartialOrd`] so do not sort the variants
#[derive(PartialEq, Eq, PartialOrd)]
pub enum Precedence {
    Lowest,
    Equals,
    LessMore,
    Sum,
    Product,
    Prefix,
    Call,
}

/// The prefixes to be used in the prefix variant of [`Expression`]
#[derive(Debug, PartialEq, Eq)]
pub enum Prefix {
    Negative,
    Not,
}

/// The infixes to be used in the infix variant of [`Expression`]
#[derive(Debug, PartialEq, Eq)]
pub enum Infix {
    Eq,
    Less,
    Minus,
    More,
    NotEq,
    Plus,
    Slash,
    Star,
}

/// A helper wrapper for repesenting block statements
#[derive(Debug, PartialEq, Eq)]
pub struct BlockStatement {
    pub stmts: Vec<Statement>,
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Expression(e) => write!(f, "Expression {e}"),
            Self::Let { ident, expr } => write!(f, "Let {ident} = {expr}"),
            Self::Return(e) => write!(f, "Return {e}"),
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Boolean(b) => write!(f, "{b}"),
            Self::Int(i) => write!(f, "{i}"),
            Self::String(s) => write!(f, "\"{s}\""),
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Function { body, params } => write!(f, "fn({}) {body}", params.join(", ")),
            Self::Ident(s) => write!(f, "{s}"),
            Self::Infix(i, l, r) => write!(f, "({l} {i} {r})"),
            Self::Literal(l) => write!(f, "{l}"),
            Self::Prefix(p, b) => write!(f, "({p} {b})"),
            Self::Call { args, ident } => write!(
                f,
                "{ident}({})",
                args.iter().fold(String::new(), |mut o, v| {
                    let _ = write!(o, "{v}, ");
                    o
                })
            ),
            Self::If { cond, alt, then } => write!(f, "If {cond} then {then} else {alt}"),
        }
    }
}

impl Display for Prefix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Negative => write!(f, "-"),
            Self::Not => write!(f, "!"),
        }
    }
}

impl Display for Infix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Eq => write!(f, "=="),
            Self::Less => write!(f, "<"),
            Self::Minus => write!(f, "-"),
            Self::More => write!(f, ">"),
            Self::NotEq => write!(f, "!="),
            Self::Plus => write!(f, "+"),
            Self::Slash => write!(f, "/"),
            Self::Star => write!(f, "*"),
        }
    }
}

impl Display for BlockStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{{}}}",
            self.stmts.iter().fold(String::new(), |mut o, v| {
                let _ = write!(o, "{v}; ");
                o
            })
        )
    }
}
