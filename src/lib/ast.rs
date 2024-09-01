use std::{
    fmt::{Display, Write},
    hash::Hash,
    rc::Rc,
};

/// The program, consting of the [`Statement`] our parser creates
pub struct Program {
    pub statements: Vec<Statement>,
}

/// The differnt types of statements in the language
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Statement {
    Expression(Expression),
    Let { ident: Rc<str>, expr: Expression },
    Return(Expression),
}

/// The different types of Expressions in the language
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expression {
    Ident(Rc<str>),
    /// Left is to index, right is which index
    Index(Box<Expression>, Box<Expression>),
    /// Infix of left and right
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
        params: Vec<Rc<str>>,
    },
    Macro {
        body: BlockStatement,
        params: Vec<Rc<str>>,
    },
}

impl Hash for Expression {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Call { ident, .. } => ident.hash(state),
            Self::Function { params, .. } | Self::Macro { params, .. } => params.hash(state),
            Self::Ident(r) => r.hash(state),
            Self::If { cond, .. } => cond.hash(state),
            Self::Index(b1, b2) | Self::Infix(_, b1, b2) => (b1, b2).hash(state),
            Self::Literal(_) => 0.hash(state),
            Self::Prefix(_, b) => b.hash(state),
        }
    }
}

/// The literal values the language represents
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Literal {
    List(Vec<Expression>),
    Boolean(bool),
    Int(isize),
    /// Vec<(k,v)> to then create map from in [`crate::evaluator::Evaluator`]
    Map(Vec<(Expression, Expression)>),
    String(Rc<str>),
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
    Index,
}

/// The prefixes to be used in the prefix variant of [`Expression`]
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Prefix {
    Negative,
    Not,
}

/// The infixes to be used in the infix variant of [`Expression`]
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Infix {
    Eq,
    Less,
    Minus,
    More,
    NotEq,
    Percent,
    Plus,
    Slash,
    Star,
}

/// A helper wrapper for repesenting block statements
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BlockStatement {
    pub statements: Vec<Statement>,
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
            Self::List(a) => write!(f, "[{}]", print_arr(a, ", ")),
            Self::Boolean(b) => write!(f, "{b}"),
            Self::Int(i) => write!(f, "{i}"),
            Self::Map(m) => write!(f, "{{{}}}", print_arr_pair(m, ", ")),
            Self::String(s) => write!(f, "\"{s}\""),
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Call { args, ident } => write!(f, "{ident}({})", print_arr(args, ", ")),
            Self::Function { body, params } => write!(f, "fn({}) {body}", params.join(", ")),
            Self::Macro { body, params } => write!(f, "macro({}) {body}", params.join(", ")),
            Self::Ident(s) => write!(f, "{s}"),
            Self::If { cond, alt, then } => write!(f, "If {cond} then {then} else {alt}"),
            Self::Index(a, i) => write!(f, "{a}[{i}]"),
            Self::Infix(i, l, r) => write!(f, "({l} {i} {r})"),
            Self::Literal(l) => write!(f, "{l}"),
            Self::Prefix(p, b) => write!(f, "({p} {b})"),
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
            Self::Percent => write!(f, "%"),
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
            self.statements.iter().fold(String::new(), |mut o, v| {
                let _ = write!(o, "{v}; ");
                o
            })
        )
    }
}

/// Helper func to print an array of expression
fn print_arr(v: &[Expression], s: &str) -> String {
    v.iter()
        .map(ToString::to_string)
        .collect::<Vec<String>>()
        .join(s)
}

/// Helper func to print an array of expression pairs
fn print_arr_pair(a: &[(Expression, Expression)], s: &str) -> String {
    a.iter()
        .map(|(k, v)| format!("{k}: {v}"))
        .collect::<Vec<String>>()
        .join(s)
}
