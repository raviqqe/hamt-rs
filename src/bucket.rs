use std::{borrow::Borrow, sync::Arc};

#[derive(Clone, Debug)]
pub struct Bucket<K, V> {
    entries: Arc<[(K, V)]>,
}

impl<K, V> Bucket<K, V> {
    pub fn new(entries: Vec<(K, V)>) -> Self {
        Self {
            entries: entries.into(),
        }
    }
}

impl<K, V> Bucket<K, V> {
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_singleton(&self) -> bool {
        self.len() == 1
    }

    pub fn as_slice(&self) -> &[(K, V)] {
        &self.entries
    }

    #[cfg(test)]
    pub fn entry_count(&self) -> usize {
        self.entries.len()
    }
}

impl<K: PartialEq, V> Bucket<K, V> {
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: PartialEq,
    {
        self.find_index(key).map(|index| &self.entries[index].1)
    }

    fn find_index<Q: ?Sized>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: PartialEq,
    {
        for (index, (other_key, _)) in self.entries.iter().enumerate() {
            if key == &other_key {
                return Some(index);
            }
        }

        None
    }
}

impl<K: Clone + PartialEq, V: Clone> Bucket<K, V> {
    pub fn insert(&self, key: K, value: V) -> (Self, bool) {
        let mut entries = self.entries.to_vec();

        match self.find_index(&key) {
            Some(index) => {
                entries[index] = (key, value);

                (
                    Self {
                        entries: entries.into(),
                    },
                    false,
                )
            }
            None => {
                entries.push((key, value));

                (
                    Self {
                        entries: entries.into(),
                    },
                    true,
                )
            }
        }
    }

    pub fn remove(&self, key: &K) -> Option<Self> {
        self.find_index(key).map(|index| {
            let mut entries = self.entries.to_vec();

            entries.remove(index);

            Self {
                entries: entries.into(),
            }
        })
    }

    pub fn first_rest(&self) -> Option<(&K, &V, Self)> {
        if self.entries.is_empty() {
            return None;
        }

        let mut entries = self.entries.to_vec();

        entries.remove(0);

        Some((
            &self.entries[0].0,
            &self.entries[0].1,
            Self {
                entries: entries.into(),
            },
        ))
    }
}

impl<K: PartialEq, V: PartialEq> PartialEq for Bucket<K, V> {
    fn eq(&self, other: &Self) -> bool {
        for entry in self.entries.as_ref() {
            if !other.entries.contains(entry) {
                return false;
            }
        }

        true
    }
}

impl<K: PartialEq, V: PartialEq> Eq for Bucket<K, V> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        Bucket::new(vec![(42, 0)]);
    }

    #[test]
    fn insert() {
        let bucket = Bucket::new(vec![(42, 0)]);

        assert_eq!(bucket.entry_count(), 1);

        let (other_bucket, ok) = bucket.insert(0, 0);

        assert!(ok);
        assert_eq!(bucket.entry_count(), 1);
        assert_eq!(other_bucket.entry_count(), 2);
    }

    #[test]
    fn remove() {
        let bucket = Bucket::new(vec![(42, 0)]);

        assert_eq!(bucket.remove(&42).unwrap().entry_count(), 0);
        assert_eq!(
            bucket.insert(0, 0).0.remove(&42).unwrap(),
            Bucket::new(vec![(0, 0)])
        );
    }

    #[test]
    fn get() {
        let bucket = Bucket::new(vec![(42, 0)]);

        assert_eq!(bucket.get(&42), Some(&0));
        assert_eq!(bucket.get(&0), None);
    }

    #[test]
    fn first_rest() {
        let bucket = Bucket::new(vec![(42, 0)]).insert(0, 0).0;

        assert_eq!(
            bucket.first_rest(),
            Some((&42, &0, Bucket::new(vec![(0, 0)])))
        );
        assert_eq!(
            bucket.remove(&0).unwrap().first_rest(),
            Some((&42, &0, bucket.remove(&0).unwrap().remove(&42).unwrap()))
        );
    }

    #[test]
    fn is_singleton() {
        let bucket = Bucket::new(vec![(42, 0)]);

        assert!(!bucket.remove(&42).unwrap().is_singleton());
        assert!(bucket.is_singleton());
        assert!(!bucket.insert(0, 0).0.is_singleton());
    }

    #[test]
    fn equal() {
        assert_eq!(
            Bucket::new(vec![(1, 0), (2, 0)]),
            Bucket::new(vec![(2, 0), (1, 0)])
        );
    }
}
