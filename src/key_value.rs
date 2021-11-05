use std::hash::Hash;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KeyValue<K, V> {
    key: K,
    hash: u64,
    value: V,
}

impl<K: Hash, V> KeyValue<K, V> {
    pub fn new(key: K, hash: u64, value: V) -> Self {
        Self { key, hash, value }
    }
}

impl<K, V> KeyValue<K, V> {
    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn hash(&self) -> u64 {
        self.hash
    }

    pub fn value(&self) -> &V {
        &self.value
    }
}
