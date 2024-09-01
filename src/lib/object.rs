use std::{cell::RefCell, collections::HashMap, fmt::Display, hash::Hash, rc::Rc};

use crate::{
    ast::{BlockStatement, Expression},
    builtins::BuiltinError,
    environment::Environment,
};

/// The objects that our [`crate::ast::Statement`] and [`crate::ast::Program`] evaluate to
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Object {
    Boolean(bool),
    /// Function and Option of wether there is a correct nr of args
    Builtin(
        fn(&[Object]) -> Result<Object, BuiltinError>,
        Option<u8>,
        Rc<str>,
    ),
    /// Vec of param identifiers, a block to execute and an environment for nesting
    Function(Vec<Rc<str>>, BlockStatement, Rc<RefCell<Environment>>),
    Int(isize),
    List(Vec<Object>),
    Map(HashMap<Object, Object>),
    Quote(Expression),
    Return(Box<Object>),
    String(Rc<str>),
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Boolean(b) => write!(f, "{b}"),
            Self::Builtin(_, _, s) => write!(f, "[builtin-fn] {s}"),
            Self::Function(p, b, _) => write!(f, "fn({}) {b}", p.join(", ")),
            Self::Int(i) => write!(f, "{i}"),
            Self::List(a) => write!(f, "[{}]", print_arr(a, ", ")),
            Self::Map(hm) => write!(f, "{{{}}}", print_map(hm, ", ")),
            Self::Quote(s) => write!(f, "Quote{s}"),
            Self::Return(o) => write!(f, "{o}"),
            Self::String(s) => write!(f, "\"{s}\""),
        }
    }
}

impl Hash for Object {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Boolean(b) => b.hash(state),
            Self::Builtin(_, o, _) => o.hash(state),
            Self::Function(f, _, _) => f.hash(state),
            Self::Int(i) => i.hash(state),
            Self::List(a) => a.hash(state),
            Self::Map(_) => 0.hash(state),
            Self::Quote(s) => s.hash(state),
            Self::Return(b) => b.hash(state),
            Self::String(s) => s.hash(state),
        }
    }
}

/// Helper fn for printing array of [`Object`]
fn print_arr(v: &[Object], s: &str) -> String {
    v.iter()
        .map(ToString::to_string)
        .collect::<Vec<String>>()
        .join(s)
}

/// Helper fn for printing map of <[`Object`], [`Object`]>
fn print_map(v: &HashMap<Object, Object>, s: &str) -> String {
    v.iter()
        .map(|(k, v)| format!("{k}: {v}"))
        .collect::<Vec<String>>()
        .join(s)
}
