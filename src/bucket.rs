use crate::node::Node;
use std::{hash::Hash, sync::Arc};

// TODO: Fix Eq and PartialEq impl.
// TODO: Unwrap Arc.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Bucket<K, V>(Arc<Vec<(K, V)>>);

impl<K, V> Bucket<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Bucket(Arc::new(vec![(key, value)]))
    }
}

impl<K, V> Bucket<K, V> {
    pub fn to_vec(&self) -> &Vec<(K, V)> {
        &self.0
    }
}

impl<K: PartialEq, V> Bucket<K, V> {
    fn find_index(&self, key: &K) -> Option<usize> {
        for (i, (other_key, _)) in self.0.iter().enumerate() {
            if key == other_key {
                return Some(i);
            }
        }

        None
    }
}

impl<K: Clone + Hash + PartialEq, V: Clone> Node for Bucket<K, V> {
    type Key = K;
    type Value = V;

    fn insert(&self, key: K, value: V) -> (Self, bool) {
        let mut key_values = (*self.0).clone();

        match self.find_index(&key) {
            Some(index) => {
                key_values[index] = (key, value);
                (Bucket(Arc::new(key_values)), false)
            }
            None => {
                key_values.push((key, value));
                (Bucket(Arc::new(key_values)), true)
            }
        }
    }

    fn delete(&self, key: &K) -> Option<Self> {
        self.find_index(key).map(|index| {
            let mut value = (*self.0).clone();
            value.remove(index);
            Bucket(Arc::new(value))
        })
    }

    fn find(&self, key: &K) -> Option<&V> {
        self.find_index(key).map(|index| &self.0[index].1)
    }

    fn first_rest(&self) -> Option<(&K, &V, Self)> {
        if self.0.is_empty() {
            return None;
        }

        let mut key_values = (*self.0).clone();
        key_values.remove(0);
        Some((&self.0[0].0, &self.0[0].1, Bucket(Arc::new(key_values))))
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
        let bucket = Bucket::new(42, 0);

        assert_eq!(bucket.size(), 1);

        let (other_bucket, ok) = bucket.insert(0, 0);

        assert!(ok);
        assert_eq!(bucket.size(), 1);
        assert_eq!(other_bucket.size(), 2);
    }

    #[test]
    fn delete() {
        let bucket = Bucket::new(42, 0);

        assert_eq!(bucket.delete(&42).unwrap().size(), 0);
        assert_eq!(
            bucket.insert(0, 0).0.delete(&42).unwrap(),
            Bucket::new(0, 0)
        );
    }

    #[test]
    fn find() {
        let bucket = Bucket::new(42, 0);

        assert_eq!(bucket.find(&42), Some(&0));
        assert_eq!(bucket.find(&0), None);
    }

    #[test]
    fn first_rest() {
        let bucket = Bucket::new(42, 0).insert(0, 0).0;

        assert_eq!(bucket.first_rest(), Some((&42, &0, Bucket::new(0, 0))));
        assert_eq!(
            bucket.delete(&0).unwrap().first_rest(),
            Some((&42, &0, bucket.delete(&0).unwrap().delete(&42).unwrap()))
        );
    }

    #[test]
    fn is_singleton() {
        let bucket = Bucket::new(42, 0);

        assert!(!bucket.delete(&42).unwrap().is_singleton());
        assert!(bucket.is_singleton());
        assert!(!bucket.insert(0, 0).0.is_singleton());
    }
}
