use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::object::Object;

#[derive(Debug, PartialEq, Eq)]
pub struct Environment {
    map: HashMap<String, Object>,
    parent: Option<Rc<RefCell<Environment>>>,
}

impl Environment {
    #[must_use]
    pub fn new(parent: Option<Rc<RefCell<Self>>>) -> Self {
        Self {
            map: HashMap::new(),
            parent,
        }
    }

    pub fn add_map(&mut self, m: HashMap<String, Object>) {
        self.map.extend(m);
    }

    pub fn set(&mut self, s: String, o: Object) {
        *self.map.entry(s).or_insert(o) = o.clone();
    }

    pub fn get(&mut self, name: String) -> Option<Object> {
        match self.map.get(&name) {
            Some(o) => Some(o.clone()),
            None => self
                .parent
                .as_ref()
                .map_or_else(|| None, |parent| parent.borrow_mut().get(name)),
        }
    }
}
