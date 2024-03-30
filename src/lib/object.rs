use std::{cell::RefCell, collections::HashMap, fmt::Display, hash::Hash, rc::Rc};

use crate::{ast::BlockStatement, environment::Environment};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Object {
    Array(Vec<Object>),
    Boolean(bool),
    Builtin(fn(&[Object]) -> Object, Option<u8>),
    Function(Vec<String>, BlockStatement, Rc<RefCell<Environment>>),
    Int(isize),
    Map(HashMap<Object, Object>),
    Null,
    Return(Box<Object>),
    String(String),
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Array(a) => write!(f, "[{}]", print_arr(a, ", ")),
            Self::Boolean(b) => write!(f, "{b}"),
            Self::Builtin(_, _) => write!(f, "[builtin-fn]"),
            Self::Function(p, b, _) => write!(f, "fn({}) {b}", p.join(", ")),
            Self::Int(i) => write!(f, "{i}"),
            Self::Null => write!(f, ""),
            Self::Return(o) => write!(f, "{o}"),
            Self::String(s) => write!(f, "\"{s}\""),
            Self::Map(hm) => write!(f, "{{{}}}", print_map(hm, ",")),
        }
    }
}

fn print_arr(v: &[Object], s: &str) -> String {
    v.iter()
        .map(ToString::to_string)
        .collect::<Vec<String>>()
        .join(s)
}

fn print_map(v: &HashMap<Object, Object>, s: &str) -> String {
    v.iter()
        .map(|(k, v)| format!("{k}: {v}"))
        .collect::<Vec<String>>()
        .join(s)
}

impl Hash for Object {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Array(a) => a.hash(state),
            Self::Boolean(b) => b.hash(state),
            Self::Builtin(_, o) => o.hash(state),
            Self::Function(f, _, _) => f.hash(state),
            Self::Int(i) => i.hash(state),
            Self::Map(_) => 0.hash(state),
            Self::Null => '\0'.hash(state),
            Self::Return(b) => b.hash(state),
            Self::String(s) => s.hash(state),
        }
    }
}
