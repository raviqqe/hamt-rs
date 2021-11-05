use crate::{bucket::Bucket, key_value::KeyValue, utilities::hash_key};
use std::{hash::Hash, sync::Arc};

const MAX_LEVEL: u8 = 64 / 5;
const ENTRY_COUNT: usize = 32;

#[derive(Clone, Debug, Eq, PartialEq)]
enum Entry<K, V> {
    Empty,
    KeyValue(KeyValue<K, V>),
    Hamt(Arc<Hamt<K, V>>),
    Bucket(Bucket<K, V>),
}

impl<K, V> Default for Entry<K, V> {
    fn default() -> Self {
        Self::Empty
    }
}

impl<K: Hash, V> From<KeyValue<K, V>> for Entry<K, V> {
    fn from(key_value: KeyValue<K, V>) -> Self {
        Self::KeyValue(key_value)
    }
}

impl<K: Clone + Hash + PartialEq, V: Clone> From<Hamt<K, V>> for Entry<K, V> {
    fn from(hamt: Hamt<K, V>) -> Self {
        if hamt.is_singleton() {
            for entry in hamt.entries {
                if matches!(&entry, Self::KeyValue(_)) {
                    return entry;
                }
            }

            unreachable!()
        } else {
            Self::Hamt(hamt.into())
        }
    }
}

impl<K: Clone + Hash + PartialEq, V: Clone> From<Bucket<K, V>> for Entry<K, V> {
    fn from(bucket: Bucket<K, V>) -> Self {
        if bucket.is_singleton() {
            let (key, value) = bucket.as_slice().iter().next().unwrap();

            // TODO Cache hash.
            Self::KeyValue(KeyValue::new(key.clone(), hash_key(key), value.clone()))
        } else {
            Self::Bucket(bucket)
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Hamt<K, V> {
    // TODO: Use bitmaps and raw union types for performance.
    level: u8,
    entries: [Entry<K, V>; ENTRY_COUNT],
}

impl<K, V> Hamt<K, V> {
    pub fn new(level: u8) -> Self {
        Self {
            level,
            entries: Default::default(),
        }
    }

    fn entry_index(&self, hash: u64) -> usize {
        ((hash >> (self.level * 5)) & 0b11111) as usize
    }
}

impl<K: Hash + PartialEq, V> Hamt<K, V> {
    pub fn get(&self, key: &K) -> Option<&V> {
        self.get_with_hash(key, hash_key(key))
    }

    fn get_with_hash(&self, key: &K, hash: u64) -> Option<&V> {
        match &self.entries[self.entry_index(hash)] {
            Entry::Empty => None,
            Entry::KeyValue(key_value) => {
                if key == key_value.key() {
                    Some(key_value.value())
                } else {
                    None
                }
            }
            Entry::Hamt(hamt) => hamt.get_with_hash(key, hash),
            Entry::Bucket(bucket) => bucket.get(key),
        }
    }
}

impl<K: Clone, V: Clone> Hamt<K, V> {
    fn set_entry(&self, index: usize, entry: impl Into<Entry<K, V>>) -> Self {
        let mut entries = self.entries.clone();

        entries[index] = entry.into();

        Self {
            level: self.level,
            entries,
        }
    }
}

impl<K: Clone + Hash + PartialEq, V: Clone> Hamt<K, V> {
    pub fn remove(&self, key: &K) -> Option<Self> {
        self.remove_with_hash(key, hash_key(key))
    }

    fn remove_with_hash(&self, key: &K, hash: u64) -> Option<Self> {
        let index = self.entry_index(hash);

        Some(self.set_entry(
            index,
            match &self.entries[index] {
                Entry::Empty => None,
                Entry::KeyValue(key_value) => {
                    if key == key_value.key() {
                        Some(Entry::Empty)
                    } else {
                        None
                    }
                }
                Entry::Hamt(hamt) => hamt.remove_with_hash(key, hash).map(Entry::from),
                Entry::Bucket(bucket) => bucket.remove(key).map(Entry::from),
            }?,
        ))
    }

    pub fn insert(&self, key: K, value: V) -> (Self, bool) {
        let hash = hash_key(&key);

        self.insert_with_hash(key, hash, value)
    }

    fn insert_with_hash(&self, key: K, hash: u64, value: V) -> (Self, bool) {
        let index = self.entry_index(hash);

        match &self.entries[index] {
            Entry::Empty => (self.set_entry(index, KeyValue::new(key, hash, value)), true),
            Entry::KeyValue(key_value) => {
                if &key == key_value.key() {
                    (
                        self.set_entry(index, KeyValue::new(key, hash, value)),
                        false,
                    )
                } else {
                    (
                        self.set_entry(
                            index,
                            if self.level < MAX_LEVEL {
                                let mut hamt = Self::new(self.level + 1);

                                hamt.insert_mut_with_hash(
                                    key_value.key().clone(),
                                    key_value.hash(),
                                    key_value.value().clone(),
                                );
                                hamt.insert_mut_with_hash(key, hash, value);

                                Entry::from(hamt)
                            } else {
                                Bucket::new(vec![
                                    (key, value),
                                    (key_value.key().clone(), key_value.value().clone()),
                                ])
                                .into()
                            },
                        ),
                        true,
                    )
                }
            }
            Entry::Hamt(hamt) => {
                let (hamt, ok) = hamt.insert_with_hash(key, hash, value);
                (self.set_entry(index, hamt), ok)
            }
            Entry::Bucket(bucket) => {
                let (bucket, ok) = bucket.insert(key, value);
                (self.set_entry(index, bucket), ok)
            }
        }
    }

    pub fn first_rest(&self) -> Option<(&K, &V, Self)> {
        for (index, entry) in self.entries.iter().enumerate() {
            match entry {
                Entry::Empty => {}
                Entry::KeyValue(key_value) => {
                    return Some((
                        key_value.key(),
                        key_value.value(),
                        self.remove(key_value.key()).unwrap(),
                    ))
                }
                Entry::Hamt(hamt) => {
                    let (key, value, rest) = hamt.first_rest().unwrap();

                    return Some((key, value, self.set_entry(index, rest)));
                }
                Entry::Bucket(bucket) => {
                    let (key, value, rest) = bucket.first_rest().unwrap();

                    return Some((key, value, self.set_entry(index, rest)));
                }
            }
        }

        None
    }

    pub fn insert_mut(&mut self, key: K, value: V) -> bool {
        let hash = hash_key(&key);

        self.insert_mut_with_hash(key, hash, value)
    }

    fn insert_mut_with_hash(&mut self, key: K, hash: u64, value: V) -> bool {
        let index = self.entry_index(hash);

        match &mut self.entries[index] {
            Entry::Empty => {
                self.entries[index] = KeyValue::new(key, hash, value).into();
                true
            }
            Entry::KeyValue(key_value) => {
                let (entry, ok) = if &key == key_value.key() {
                    (KeyValue::new(key, hash, value).into(), false)
                } else if self.level < MAX_LEVEL {
                    let mut hamt = Self::new(self.level + 1);

                    hamt.insert_mut_with_hash(key, hash, value);
                    // TODO Cache hash.
                    hamt.insert_mut_with_hash(
                        key_value.key().clone(),
                        key_value.hash(),
                        key_value.value().clone(),
                    );

                    (hamt.into(), true)
                } else {
                    (
                        Bucket::new(vec![
                            (key, value),
                            (key_value.key().clone(), key_value.value().clone()),
                        ])
                        .into(),
                        true,
                    )
                };

                self.entries[index] = entry;

                ok
            }
            Entry::Hamt(hamt) => Arc::get_mut(hamt)
                .unwrap()
                .insert_mut_with_hash(key, hash, value),
            Entry::Bucket(bucket) => {
                let (bucket, ok) = bucket.insert(key, value);

                self.entries[index] = bucket.into();

                ok
            }
        }
    }

    fn is_singleton(&self) -> bool {
        self.entries
            .iter()
            .map(|entry| match entry {
                Entry::Empty => 0,
                Entry::KeyValue(_) => 1,
                _ => 2,
            })
            .sum::<usize>()
            == 1
    }

    #[cfg(test)]
    fn contains_bucket(&self) -> bool {
        self.entries
            .iter()
            .any(|entry| matches!(entry, Entry::Bucket(_)))
    }

    #[cfg(test)]
    fn is_normal(&self) -> bool {
        self.entries.iter().all(|entry| match entry {
            Entry::Bucket(bucket) => !bucket.is_singleton(),
            Entry::Hamt(hamt) => hamt.is_normal() && !hamt.is_singleton(),
            _ => true,
        })
    }

    #[cfg(test)]
    fn entry_count(&self) -> usize {
        self.entries
            .iter()
            .map(|entry| match entry {
                Entry::Empty => 0,
                Entry::KeyValue(_) => 1,
                Entry::Hamt(hamt) => hamt.entry_count(),
                Entry::Bucket(bucket) => bucket.entry_count(),
            })
            .sum()
    }
}

#[derive(Debug)]
enum NodeRef<'a, K: 'a, V: 'a> {
    Hamt(&'a Hamt<K, V>),
    Bucket(&'a Bucket<K, V>),
}

#[derive(Debug)]
pub struct HamtIterator<'a, K: 'a, V: 'a>(Vec<(NodeRef<'a, K, V>, usize)>);

impl<'a, K, V> IntoIterator for &'a Hamt<K, V> {
    type IntoIter = HamtIterator<'a, K, V>;
    type Item = (&'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        HamtIterator(vec![(NodeRef::Hamt(self), 0)])
    }
}

impl<'a, K, V> Iterator for HamtIterator<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop().and_then(|(node, index)| match node {
            NodeRef::Hamt(hamt) => {
                if index == ENTRY_COUNT {
                    return self.next();
                }

                self.0.push((node, index + 1));

                match &hamt.entries[index] {
                    Entry::Empty => self.next(),
                    Entry::Hamt(hamt) => {
                        self.0.push((NodeRef::Hamt(hamt), 0));
                        self.next()
                    }
                    Entry::KeyValue(key_value) => Some((key_value.key(), key_value.value())),
                    Entry::Bucket(bucket) => {
                        self.0.push((NodeRef::Bucket(bucket), 0));
                        self.next()
                    }
                }
            }
            NodeRef::Bucket(bucket) => {
                if index == bucket.len() {
                    return self.next();
                }

                self.0.push((node, index + 1));

                let (key, value) = &bucket.as_slice()[index];
                Some((key, value))
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{random, seq::SliceRandom, thread_rng};
    use std::collections::{HashMap, HashSet};

    const NUM_ITERATIONS: usize = 1 << 12;

    #[test]
    fn new() {
        Hamt::<usize, usize>::new(0);
    }

    #[test]
    fn insert() {
        let hamt = Hamt::new(0);

        assert_eq!(hamt.entry_count(), 0);

        let (other, ok) = hamt.insert(0, 0);

        assert!(ok);
        assert_eq!(other.entry_count(), 1);

        let (other, ok) = other.insert(0, 0);

        assert!(!ok);
        assert_eq!(other.entry_count(), 1);

        let (hamt, ok) = other.insert(1, 0);

        assert!(ok);
        assert_eq!(hamt.entry_count(), 2);
    }

    #[test]
    fn insert_many_in_order() {
        let mut hamt = Hamt::new(0);

        for index in 0..NUM_ITERATIONS {
            let (other, ok) = hamt.insert(index, index);
            hamt = other;
            assert!(ok);
            assert_eq!(hamt.entry_count(), index + 1);
        }
    }

    #[test]
    fn insert_many_at_random() {
        let mut hamt: Hamt<usize, usize> = Hamt::new(0);

        for index in 0..NUM_ITERATIONS {
            let key = random();
            hamt = hamt.insert(key, key).0;
            assert_eq!(hamt.entry_count(), index + 1);
        }
    }

    #[test]
    fn remove() {
        let hamt = Hamt::new(0);

        assert_eq!(hamt.insert(0, 0).0.remove(&0), Some(hamt.clone()));
        assert_eq!(hamt.insert(0, 0).0.remove(&1), None);
        assert_eq!(
            hamt.insert(0, 0).0.insert(1, 0).0.remove(&0),
            Some(hamt.insert(1, 0).0)
        );
        assert_eq!(
            hamt.insert(0, 0).0.insert(1, 0).0.remove(&1),
            Some(hamt.insert(0, 0).0)
        );
        assert_eq!(hamt.insert(0, 0).0.insert(1, 0).0.remove(&2), None);
    }

    #[test]
    fn insert_remove_many() {
        let mut hamt: Hamt<i16, i16> = Hamt::new(0);

        for _ in 0..NUM_ITERATIONS {
            let key = random();
            let size = hamt.entry_count();
            let found = hamt.get(&key).is_some();

            if random() {
                hamt = hamt.insert(key, key).0;

                assert_eq!(hamt.entry_count(), if found { size } else { size + 1 });
                assert_eq!(hamt.get(&key), Some(&key));
            } else {
                hamt = hamt.remove(&key).unwrap_or(hamt);

                assert_eq!(hamt.entry_count(), if found { size - 1 } else { size });
                assert_eq!(hamt.get(&key), None);
            }

            assert!(hamt.is_normal());
        }
    }

    #[test]
    fn get() {
        let hamt = Hamt::new(0);

        assert_eq!(hamt.insert(0, 0).0.get(&0), Some(&0));
        assert_eq!(hamt.insert(0, 0).0.get(&1), None);
        assert_eq!(hamt.insert(1, 0).0.get(&0), None);
        assert_eq!(hamt.insert(1, 0).0.get(&1), Some(&0));
        assert_eq!(hamt.insert(0, 0).0.insert(1, 0).0.get(&0), Some(&0));
        assert_eq!(hamt.insert(0, 0).0.insert(1, 0).0.get(&1), Some(&0));
        assert_eq!(hamt.insert(0, 0).0.insert(1, 0).0.get(&2), None);
    }

    #[test]
    fn first_rest() {
        let mut hamt: Hamt<i16, i16> = Hamt::new(0);

        for _ in 0..NUM_ITERATIONS {
            let key = random();
            hamt = hamt.insert(key, key).0;

            assert!(hamt.is_normal());
        }

        for _ in 0..hamt.entry_count() {
            let (key, _, rest) = hamt.first_rest().unwrap();

            assert_eq!(rest.entry_count(), hamt.entry_count() - 1);
            assert_eq!(rest.get(key), None);

            hamt = rest;

            assert!(hamt.is_normal());
        }

        assert_eq!(hamt, Hamt::new(0));
    }

    #[test]
    fn is_singleton() {
        let hamt = Hamt::new(0);

        assert!(!hamt.is_singleton());
        assert!(hamt.insert(0, 0).0.is_singleton());
        assert!(!hamt.insert(0, 0).0.insert(1, 0).0.is_singleton());
    }

    #[test]
    fn equality() {
        for _ in 0..8 {
            let mut hamts: [Hamt<i16, i16>; 2] = [Hamt::new(0), Hamt::new(0)];
            let mut inserted_keys: Vec<i16> = (0..NUM_ITERATIONS).map(|_| random()).collect();
            let mut deleted_keys: Vec<i16> = (0..NUM_ITERATIONS).map(|_| random()).collect();

            for hamt in hamts.iter_mut() {
                inserted_keys.shuffle(&mut thread_rng());
                deleted_keys.shuffle(&mut thread_rng());

                for key in &inserted_keys {
                    *hamt = hamt.insert(*key, *key).0;
                }

                for key in &deleted_keys {
                    *hamt = hamt.remove(key).unwrap_or_else(|| hamt.clone());
                }
            }

            assert_eq!(hamts[0], hamts[1]);
        }
    }

    #[test]
    fn collision() {
        let mut hamt = Hamt::new(MAX_LEVEL);
        let mut set = HashSet::new();

        for key in 0.. {
            assert!(!hamt.contains_bucket());

            hamt = hamt.insert(key, key).0;

            let index = hash_key(&key) >> 60;

            if set.contains(&index) {
                break;
            }

            set.insert(index);
        }

        assert!(hamt.contains_bucket());
    }

    #[test]
    fn iterate() {
        let sizes: Vec<usize> = (0..42)
            .chain((0..100).map(|_| random::<usize>() % 1024))
            .collect();

        for &level in &[0, MAX_LEVEL] {
            for size in &sizes {
                let mut hamt: Hamt<i16, i16> = Hamt::new(level);
                let mut map: HashMap<i16, i16> = HashMap::new();

                for _ in 0..*size {
                    let key = random();
                    let value = random();

                    let (other_hamt, _) = hamt.insert(key, value);
                    hamt = other_hamt;

                    map.insert(key, value);
                }

                let mut size = 0;

                for (key, value) in hamt.into_iter() {
                    size += 1;

                    assert_eq!(map[key], *value);
                }

                assert_eq!(size, hamt.entry_count());
            }
        }
    }
}
