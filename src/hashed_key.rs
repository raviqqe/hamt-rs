use crate::utilities::hash_key;
use std::hash::Hash;

pub trait HashedKey<K> {
    fn key(&self) -> &K;
    fn hash(&self) -> u64;
}

impl<K: Hash> HashedKey<K> for K {
    fn key(&self) -> &K {
        self
    }

    fn hash(&self) -> u64 {
        hash_key(&self)
    }
}

impl<K: Hash> HashedKey<K> for &K {
    fn key(&self) -> &K {
        self
    }

    fn hash(&self) -> u64 {
        hash_key(self)
    }
}
