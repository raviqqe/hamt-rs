use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

pub fn hash_key(key: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    hasher.finish()
}
