use std::hash::Hash;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum State {
    Empty,
    Singleton,
    More,
}

pub trait Node
where
    Self: Sized,
{
    type Key: Hash + Ord;

    fn insert(&self, Self::Key) -> Self;
    fn delete(&self, Self::Key) -> Option<Self>;
    fn find(&self, Self::Key) -> Option<Self::Key>;
    fn first_rest(&self) -> Option<(Self::Key, Self)>;
    fn state(&self) -> State;
    fn size(&self) -> usize; // for debugging
}
