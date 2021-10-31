use std::{hash::Hash, sync::Arc};

use node::Node;

// TODO: Fix Eq and PartialEq impl.
// TODO: Unwrap Arc.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Bucket<K, V>(Arc<Vec<(K, V)>>);

impl<K, V> Bucket<K, V> {
    pub fn new(k: K, v: V) -> Self {
        Bucket(Arc::new(vec![(k, v)]))
    }
}

impl<K, V> Bucket<K, V> {
    pub fn to_vec(&self) -> &Vec<(K, V)> {
        &self.0
    }
}

impl<K: PartialEq, V> Bucket<K, V> {
    fn find_index(&self, k: &K) -> Option<usize> {
        for (i, &(ref kk, _)) in self.0.iter().enumerate() {
            if *k == *kk {
                return Some(i);
            }
        }

        None
    }
}

impl<K: Clone + Hash + PartialEq, V: Clone> Node for Bucket<K, V> {
    type Key = K;
    type Value = V;

    fn insert(&self, k: K, v: V) -> (Self, bool) {
        let mut kvs = (*self.0).clone();

        match self.find_index(&k) {
            Some(i) => {
                kvs[i] = (k, v);
                (Bucket(Arc::new(kvs)), false)
            }
            None => {
                kvs.push((k, v));
                (Bucket(Arc::new(kvs)), true)
            }
        }
    }

    fn delete(&self, k: &K) -> Option<Self> {
        self.find_index(k).map(|i| {
            let mut v = (*self.0).clone();
            v.remove(i);
            Bucket(Arc::new(v))
        })
    }

    fn find(&self, k: &K) -> Option<&V> {
        self.find_index(k).map(|i| &self.0[i].1)
    }

    fn first_rest(&self) -> Option<(&K, &V, Self)> {
        if self.0.is_empty() {
            return None;
        }

        let mut kvs = (*self.0).clone();
        kvs.remove(0);
        Some((&self.0[0].0, &self.0[0].1, Bucket(Arc::new(kvs))))
    }

    fn is_singleton(&self) -> bool {
        self.size() == 1
    }

    fn size(&self) -> usize {
        self.0.len()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        Bucket::new(42, 0);
    }

    #[test]
    fn insert() {
        let b = Bucket::new(42, 0);

        assert_eq!(b.size(), 1);

        let (bb, new) = b.insert(0, 0);

        assert!(new);
        assert_eq!(b.size(), 1);
        assert_eq!(bb.size(), 2);
    }

    #[test]
    fn delete() {
        let b = Bucket::new(42, 0);

        assert_eq!(b.delete(&42).unwrap().size(), 0);
        assert_eq!(b.insert(0, 0).0.delete(&42).unwrap(), Bucket::new(0, 0));
    }

    #[test]
    fn find() {
        let b = Bucket::new(42, 0);

        assert_eq!(b.find(&42), Some(&0));
        assert_eq!(b.find(&0), None);
    }

    #[test]
    fn first_rest() {
        let b = Bucket::new(42, 0).insert(0, 0).0;

        assert_eq!(b.first_rest(), Some((&42, &0, Bucket::new(0, 0))));
        assert_eq!(
            b.delete(&0).unwrap().first_rest(),
            Some((&42, &0, b.delete(&0).unwrap().delete(&42).unwrap()))
        );
    }

    #[test]
    fn is_singleton() {
        let b = Bucket::new(42, 0);

        assert!(!b.delete(&42).unwrap().is_singleton());
        assert!(b.is_singleton());
        assert!(!b.insert(0, 0).0.is_singleton());
    }
}
