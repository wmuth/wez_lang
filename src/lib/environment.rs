use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::object::Object;

/// The environment the current scope executes in. Has all object identifier bindings
#[derive(Debug, PartialEq, Eq)]
pub struct Environment {
    map: HashMap<Rc<str>, Rc<Object>>,
    parent: Option<Rc<RefCell<Environment>>>,
}

impl Environment {
    /// Creates an environment
    ///
    /// # Params
    /// - `parent` None if there is no parent environment, otherwise Some with an `Rc`<`RefCell`<>>
    #[must_use]
    pub fn new(parent: Option<Rc<RefCell<Self>>>) -> Self {
        Self {
            map: HashMap::new(),
            parent,
        }
    }

    /// Adds another map to the environments map, used for builtins
    pub fn add_map(&mut self, m: HashMap<Rc<str>, Rc<Object>>) {
        self.map.extend(m);
    }

    /// Sets a key to a value
    ///
    /// # Params
    /// - `s` the key to set, the identifier of the object
    /// - `o` the value to set, the object itself
    pub fn set(&mut self, s: Rc<str>, o: Rc<Object>) {
        self.map.insert(s, o);
    }

    /// Gets a value by a key
    ///
    /// # Params
    /// - `name` the key to get
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Rc<Object>> {
        self.map.get(name).map_or_else(
            || {
                self.parent
                    .as_ref()
                    .map_or_else(|| None, |parent| parent.borrow_mut().get(name))
            },
            |o| Some(Rc::clone(o)),
        )
    }
}
