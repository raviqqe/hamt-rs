use crate::utilities::hash_key;
use std::hash::Hash;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KeyValue<K, V> {
    key: K,
    value: V,
    hash: u64,
}

impl<K: Hash, V> KeyValue<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Self {
            hash: hash_key(&key),
            key,
            value,
        }
    }
}

impl<K, V> KeyValue<K, V> {
    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn value(&self) -> &V {
        &self.value
    }

    pub fn hash(&self) -> u64 {
        self.hash
    }
}
