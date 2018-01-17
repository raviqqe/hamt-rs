use std::hash::Hash;
use std::sync::Arc;

use node::{Node, State};
use node::State::{Empty, More, Singleton};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Bucket<K: Ord>(Arc<Vec<K>>);

impl<K: Ord> Bucket<K> {
    fn new(k: K) -> Self {
        Bucket(Arc::new(vec![k]))
    }
}

impl<K: Clone + Hash + Ord> Node for Bucket<K> {
    type Key = K;

    fn insert(&self, k: K) -> Self {
        let mut v = (*self.0).clone();

        v.insert(
            match self.0.binary_search(&k) {
                Ok(i) => i,
                Err(i) => i,
            },
            k,
        );

        Bucket(Arc::new(v))
    }

    fn delete(&self, k: K) -> Option<Self> {
        match self.0.binary_search(&k) {
            Ok(i) => {
                let mut v = (*self.0).clone();
                v.remove(i);
                Some(Bucket(Arc::new(v)))
            }
            _ => None,
        }
    }

    fn find(&self, k: K) -> Option<K> {
        self.0.binary_search(&k).ok().map(|i| self.0[i].clone())
    }

    fn first_rest(&self) -> Option<(K, Self)> {
        if self.0.is_empty() {
            return None;
        }

        let f = self.0[0].clone();
        let mut v = (*self.0).clone();
        v.remove(0);
        Some((f, Bucket(Arc::new(v))))
    }

    fn state(&self) -> State {
        match self.0.len() {
            0 => Empty,
            1 => Singleton,
            _ => More,
        }
    }

    fn size(&self) -> usize {
        self.0.len()
    }
}

#[cfg(test)]
mod test {
    use node::State::{Empty, More, Singleton};

    use super::*;

    #[test]
    fn bucket_new() {
        Bucket::new(42);
    }

    #[test]
    fn bucket_insert() {
        let b = Bucket::new(42);

        assert_eq!(b.size(), 1);

        let bb = b.insert(0);

        assert_eq!(b.size(), 1);
        assert_eq!(bb.size(), 2);
    }

    #[test]
    fn bucket_delete() {
        let b = Bucket::new(42);

        assert_eq!(b.delete(42).unwrap().size(), 0);
        assert_eq!(b.insert(0).delete(42).unwrap(), Bucket::new(0));
    }

    #[test]
    fn bucket_find() {
        let b = Bucket::new(42);

        assert_eq!(b.find(42), Some(42));
        assert_eq!(b.find(0), None);
    }

    #[test]
    fn bucket_first_rest() {
        let b = Bucket::new(42).insert(0);

        assert_eq!(b.first_rest(), Some((0, Bucket::new(42))));
        assert_eq!(
            b.delete(0).unwrap().first_rest(),
            Some((42, b.delete(0).unwrap().delete(42).unwrap()))
        );
    }

    #[test]
    fn bucket_state() {
        let b = Bucket::new(42);

        assert_eq!(b.delete(42).unwrap().state(), Empty);
        assert_eq!(b.state(), Singleton);
        assert_eq!(b.insert(0).state(), More);
    }
}
