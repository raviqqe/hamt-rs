use std::hash::Hash;

pub trait Node: Sized {
    type Key: Hash + PartialEq;
    type Value;

    fn insert(&self, key: Self::Key, value: Self::Value) -> (Self, bool);
    fn delete(&self, key: &Self::Key) -> Option<Self>;
    fn find(&self, key: &Self::Key) -> Option<&Self::Value>;
    fn first_rest(&self) -> Option<(&Self::Key, &Self::Value, Self)>;
    fn is_singleton(&self) -> bool; // for normalization
    #[cfg(test)]
    fn entry_count(&self) -> usize; // for debugging
}
