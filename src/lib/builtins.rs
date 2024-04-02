use std::{collections::HashMap, fmt::Display, num::TryFromIntError, rc::Rc};

use crate::object::Object;

/// Gets a map of all the builtin functions where key is the name of the function and object is the
/// [`Object::Builtin`] variant for this builtin function
pub fn get_builtin_fns() -> HashMap<Rc<str>, Rc<Object>> {
    let print = Rc::from(Object::Builtin(print, None));
    let push = Rc::from(Object::Builtin(push, Some(2)));

    let mut map = HashMap::new();
    map.insert(Rc::from("first"), Rc::from(Object::Builtin(first, Some(1))));
    map.insert(
        Rc::from("insert"),
        Rc::from(Object::Builtin(insert, Some(3))),
    );
    map.insert(Rc::from("invest"), Rc::clone(&push));
    map.insert(Rc::from("last"), Rc::from(Object::Builtin(last, Some(1))));
    map.insert(Rc::from("len"), Rc::from(Object::Builtin(len, Some(1))));
    map.insert(Rc::from("print"), Rc::clone(&print));
    map.insert(Rc::from("push"), Rc::clone(&push));
    map.insert(Rc::from("rest"), Rc::from(Object::Builtin(rest, Some(1))));
    map.insert(Rc::from("roar"), Rc::clone(&print));
    map
}

pub enum BuiltinError {
    /// .len() returns usize but [`Object::Int`] is isize. Should never be an issue in practice
    LenToInt,
    /// If args checking was bypassed or if passing nothing to a builtin with None on args
    NotEnoughArgs,
    /// Wrong type with a string that lists the types the function does accept
    WrongType(String),
}

impl Display for BuiltinError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LenToInt => write!(f, "Could not convert len() to int."),
            Self::NotEnoughArgs => write!(f, "Not enough args."),
            Self::WrongType(e) => write!(f, "Wrong type passed to builtin. Expected {e}."),
        }
    }
}

impl From<TryFromIntError> for BuiltinError {
    fn from(_value: TryFromIntError) -> Self {
        Self::LenToInt
    }
}

/// Gets the length of the list, map or string
fn len(v: &[Object]) -> Result<Object, BuiltinError> {
    match v.first() {
        Some(Object::List(a)) => Ok(Object::Int(a.len().try_into()?)),
        Some(Object::Map(hm)) => Ok(Object::Int(hm.len().try_into()?)),
        Some(Object::String(s)) => Ok(Object::Int(s.len().try_into()?)),
        _ => Err(BuiltinError::WrongType(String::from("List, Map or String"))),
    }
}

/// Gets the first object in the list of objects or a string
fn first(v: &[Object]) -> Result<Object, BuiltinError> {
    match v.first() {
        Some(Object::List(a)) => Ok(a.first().unwrap_or(&Object::Null).clone()),
        Some(Object::String(s)) => s.chars().next().map_or_else(
            || Ok(Object::Null),
            |c| Ok(Object::String(Rc::from(c.to_string()))),
        ),
        _ => Err(BuiltinError::WrongType(String::from("List or String"))),
    }
}

/// Gets the last object in the list of objects or a string
fn last(v: &[Object]) -> Result<Object, BuiltinError> {
    match v.first() {
        Some(Object::List(a)) => Ok(a.last().unwrap_or(&Object::Null).clone()),
        Some(Object::String(s)) => s.chars().last().map_or_else(
            || Ok(Object::Null),
            |c| Ok(Object::String(Rc::from(c.to_string()))),
        ),
        _ => Err(BuiltinError::WrongType(String::from("List or String"))),
    }
}

/// Gets the list of objects or a string except the first
fn rest(v: &[Object]) -> Result<Object, BuiltinError> {
    match v.first() {
        Some(Object::List(a)) => Ok(Object::List(a.iter().skip(1).cloned().collect())),
        Some(Object::String(s)) => Ok(Object::String(Rc::from(&s[1..]))),
        _ => Err(BuiltinError::WrongType(String::from("List or String"))),
    }
}

/// Pushes an object into the end of a list of objects or a string
fn push(v: &[Object]) -> Result<Object, BuiltinError> {
    if let Some(o) = v.get(1) {
        if *o != Object::Null {
            return match v.first() {
                Some(Object::List(a)) => Ok(Object::List({
                    let mut x = a.clone();
                    x.push(o.clone());
                    x
                })),
                Some(Object::String(s)) => {
                    if let Object::String(ss) = o {
                        Ok(Object::String(Rc::from(s.to_string() + ss)))
                    } else {
                        Ok(Object::String(Rc::clone(s)))
                    }
                }
                _ => Err(BuiltinError::WrongType(String::from("List or String"))),
            };
        }
    }
    Err(BuiltinError::NotEnoughArgs)
}

/// Inserts an object into a map of objects
fn insert(v: &[Object]) -> Result<Object, BuiltinError> {
    if let Some(o) = v.get(1) {
        if *o != Object::Null {
            return match v.first() {
                Some(Object::Map(hm)) => v.get(2).map_or_else(
                    || Err(BuiltinError::NotEnoughArgs),
                    |ob| {
                        Ok(Object::Map({
                            let mut x = hm.clone();
                            x.insert(o.clone(), ob.clone());
                            x
                        }))
                    },
                ),
                _ => Err(BuiltinError::WrongType(String::from("Map"))),
            };
        }
    }
    Err(BuiltinError::NotEnoughArgs)
}

/// Prints a list of any objects
fn print(v: &[Object]) -> Result<Object, BuiltinError> {
    if v.is_empty() {
        return Err(BuiltinError::NotEnoughArgs);
    }

    for o in v {
        println!("{o}");
    }
    Ok(Object::Null)
}
