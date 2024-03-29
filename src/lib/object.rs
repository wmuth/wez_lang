use std::{cell::RefCell, fmt::Display, rc::Rc};

use crate::{ast::BlockStatement, environment::Environment};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Object {
    Boolean(bool),
    Function(Vec<String>, BlockStatement, Rc<RefCell<Environment>>),
    Int(isize),
    Null,
    Return(Box<Object>),
    String(String),
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Boolean(b) => write!(f, "{b}"),
            Self::Int(i) => write!(f, "{i}"),
            Self::Null => write!(f, "null"),
            Self::Return(o) => write!(f, "{o}"),
            Self::String(s) => write!(f, "\"{s}\""),
            Self::Function(p, b, _) => write!(f, "fn({}) {b}", p.join(", ")),
        }
    }
}
