use std::collections::HashMap;

use crate::object::Object;

pub fn get_builtin_fns() -> HashMap<String, Object> {
    let mut map = HashMap::new();
    map.insert(String::from("len"), Object::Builtin(len, Some(1)));
    map.insert(String::from("first"), Object::Builtin(first, Some(1)));
    map.insert(String::from("last"), Object::Builtin(last, Some(1)));
    map.insert(String::from("rest"), Object::Builtin(rest, Some(1)));
    map.insert(String::from("push"), Object::Builtin(push, Some(2)));
    map.insert(String::from("print"), Object::Builtin(print, None));
    map
}

fn len(v: &[Object]) -> Object {
    // TODO: Fix usize to isize - impl usize in lang?
    match v.first() {
        Some(Object::Array(a)) => a.len().try_into().map_or(Object::Null, Object::Int),
        Some(Object::String(s)) => s.len().try_into().map_or(Object::Null, Object::Int),
        _ => Object::Null,
    }
}

fn first(v: &[Object]) -> Object {
    match v.first() {
        Some(Object::Array(a)) => a.first().unwrap_or(&Object::Null).clone(),
        Some(Object::String(s)) => s
            .chars()
            .next()
            .map_or_else(|| Object::Null, |c| Object::String(String::from(c))),
        _ => Object::Null,
    }
}

fn last(v: &[Object]) -> Object {
    match v.first() {
        Some(Object::Array(a)) => a.last().unwrap_or(&Object::Null).clone(),
        Some(Object::String(s)) => s
            .chars()
            .last()
            .map_or_else(|| Object::Null, |c| Object::String(String::from(c))),
        _ => Object::Null,
    }
}

fn rest(v: &[Object]) -> Object {
    match v.first() {
        Some(Object::Array(a)) => Object::Array(a.iter().skip(1).cloned().collect()),
        Some(Object::String(s)) => Object::String(s.chars().skip(1).collect()),
        _ => Object::Null,
    }
}

fn push(v: &[Object]) -> Object {
    if let Some(o) = v.get(1) {
        if *o != Object::Null {
            return match v.first() {
                Some(Object::Array(a)) => Object::Array({
                    let mut x = a.clone();
                    x.push(o.clone());
                    x
                }),
                Some(Object::String(s)) => {
                    if let Object::String(ss) = o {
                        Object::String(s.clone() + ss)
                    } else {
                        Object::String(s.clone())
                    }
                }
                _ => Object::Null,
            };
        }
    }
    Object::Null
}

fn print(v: &[Object]) -> Object {
    for o in v {
        println!("{o}");
    }
    Object::Null
}
