use std::hash::Hash;

pub trait Node: Sized {
    type Key: Hash + PartialEq;
    type Value;

    // TODO Use Result<T, T>::into_ok_or_err() when it gets stable.
    fn insert(&self, key: Self::Key, value: Self::Value) -> (Self, bool);
    fn remove(&self, key: &Self::Key) -> Option<Self>;
    fn get(&self, key: &Self::Key) -> Option<&Self::Value>;
    fn first_rest(&self) -> Option<(&Self::Key, &Self::Value, Self)>;
    fn is_singleton(&self) -> bool; // for normalization
    fn entry_count(&self) -> usize; // for debugging
}
