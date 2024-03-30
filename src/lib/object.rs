use std::{cell::RefCell, fmt::Display, rc::Rc};

use crate::{ast::BlockStatement, environment::Environment};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Object {
    Array(Vec<Object>),
    Boolean(bool),
    Builtin(fn(&[Object]) -> Object, Option<u8>),
    Function(Vec<String>, BlockStatement, Rc<RefCell<Environment>>),
    Int(isize),
    Null,
    Return(Box<Object>),
    String(String),
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Array(v) => write!(f, "[{}]", print_arr(v, ", ")),
            Self::Boolean(b) => write!(f, "{b}"),
            Self::Builtin(_, _) => write!(f, "[builtin-fn]"),
            Self::Function(p, b, _) => write!(f, "fn({}) {b}", p.join(", ")),
            Self::Int(i) => write!(f, "{i}"),
            Self::Null => write!(f, "null"),
            Self::Return(o) => write!(f, "{o}"),
            Self::String(s) => write!(f, "\"{s}\""),
        }
    }
}

fn print_arr(v: &[Object], s: &str) -> String {
    v.iter()
        .map(ToString::to_string)
        .collect::<Vec<String>>()
        .join(s)
}
