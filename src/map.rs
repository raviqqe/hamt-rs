use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

use hamt::Hamt;
use node::Node;

#[derive(Clone, Debug)]
pub struct Map<K, V> {
    size: usize,
    hamt: Hamt<Entry<K, V>>,
}

impl<K: Clone + Hash + Ord, V: Clone> Map<K, V> {
    pub fn new() -> Self {
        Map {
            size: 0,
            hamt: Hamt::new(0),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Entry<K, V>(K, V);

impl<K: Hash, V> Hash for Entry<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<K: Ord, V> Ord for Entry<K, V> {
    fn cmp(&self, e: &Self) -> Ordering {
        self.0.cmp(&e.0)
    }
}

impl<K: PartialOrd, V> PartialOrd for Entry<K, V> {
    fn partial_cmp(&self, e: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&e.0)
    }
}

impl<K: PartialEq, V> Eq for Entry<K, V> {}

impl<K: PartialEq, V> PartialEq for Entry<K, V> {
    fn eq(&self, e: &Self) -> bool {
        self.0 == e.0
    }
}
