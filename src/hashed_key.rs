use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

#[derive(Clone, Copy, Debug)]
pub struct HashedKey<K> {
    key: K,
    hash: u64,
}

impl<K: Hash> HashedKey<K> {
    pub fn new(key: K) -> Self {
        Self {
            key,
            hash: Self::hash_key(key),
        }
    }

    pub fn key(self) -> K {
        self.key
    }

    pub fn hash(&self) -> u64 {
        self.hash
    }

    fn hash_key(key: &impl Hash) -> u64 {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }
}
