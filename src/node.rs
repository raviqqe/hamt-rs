use std::hash::Hash;

pub trait Node
where
    Self: Sized,
{
    type Key: Hash + Ord;

    fn insert(&self, Self::Key) -> (Self, bool);
    fn delete(&self, &Self::Key) -> Option<Self>;
    fn find(&self, &Self::Key) -> Option<&Self::Key>;
    fn first_rest(&self) -> Option<(&Self::Key, Self)>;
    fn is_singleton(&self) -> bool; // for normalization
    fn size(&self) -> usize; // for debugging
}
