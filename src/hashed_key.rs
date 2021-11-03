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

impl<K: Hash> HashedKey<K> for (K, u64) {
    fn key(&self) -> &K {
        &self.0
    }

    fn hash(&self) -> u64 {
        self.1
    }
}

impl<K: Hash> HashedKey<K> for (&K, u64) {
    fn key(&self) -> &K {
        self.0
    }

    fn hash(&self) -> u64 {
        self.1
    }
}

pub trait IntoKey<K> {
    fn into_key(self) -> K;
}

impl<K> IntoKey<K> for K {
    fn into_key(self) -> K {
        self
    }
}

impl<K> IntoKey<K> for (K, u64) {
    fn into_key(self) -> K {
        self.0
    }
}
