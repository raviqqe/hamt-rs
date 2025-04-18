use crate::{key_value::KeyValue, utilities::hash_key};
use std::{borrow::Borrow, hash::Hash, sync::Arc};

const MAX_LEVEL: usize = 64 / 5 - 1; // inclusive
const ENTRY_COUNT: usize = 32;

#[derive(Clone, Debug, Eq, PartialEq)]
enum Entry<K, V> {
    Empty,
    KeyValue(KeyValue<K, V>),
    Hamt(Arc<Hamt<K, V>>),
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

impl<K: Clone + Hash + Eq, V: Clone> From<Hamt<K, V>> for Entry<K, V> {
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Hamt<K, V> {
    // TODO: Use bitmaps and raw union types for performance.
    entries: [Entry<K, V>; ENTRY_COUNT],
}

impl<K, V> Default for Hamt<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Hamt<K, V> {
    pub fn new() -> Self {
        Self {
            entries: Default::default(),
        }
    }

    fn entry_index(&self, hash: u64, level: usize) -> usize {
        ((hash >> (level * 5)) & 0b11111) as usize
    }

    fn increment_level(
        key: &impl Hash,
        hash: u64,
        level: usize,
        layer: usize,
    ) -> (u64, usize, usize) {
        if level < MAX_LEVEL {
            (hash, level + 1, layer)
        } else {
            let layer = layer + 1;

            (hash_key(key, layer), 0, layer)
        }
    }
}

impl<K: Hash + Eq, V> Hamt<K, V> {
    #[must_use]
    pub fn get<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        self.get_with_hash(key, hash_key(key, 0), 0, 0)
    }

    #[cfg(test)]
    pub fn get_at_level<Q: Hash + Eq + ?Sized>(
        &self,
        key: &Q,
        level: usize,
        layer: usize,
    ) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        self.get_with_hash(key, hash_key(key, layer), level, layer)
    }

    fn get_with_hash<Q: Hash + Eq + ?Sized>(
        &self,
        key: &Q,
        hash: u64,
        level: usize,
        layer: usize,
    ) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        match &self.entries[self.entry_index(hash, level)] {
            Entry::Empty => None,
            Entry::KeyValue(key_value) => {
                if key == key_value.key().borrow() {
                    Some(key_value.value())
                } else {
                    None
                }
            }
            Entry::Hamt(hamt) => {
                let (hash, level, layer) = Self::increment_level(&key, hash, level, layer);

                hamt.get_with_hash(key, hash, level, layer)
            }
        }
    }
}

impl<K: Clone, V: Clone> Hamt<K, V> {
    fn set_entry(&self, index: usize, entry: impl Into<Entry<K, V>>) -> Self {
        let mut entries = self.entries.clone();

        entries[index] = entry.into();

        Self { entries }
    }
}

impl<K: Clone + Hash + Eq, V: Clone> Hamt<K, V> {
    #[must_use]
    pub fn remove<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<Self>
    where
        K: Borrow<Q>,
    {
        self.remove_with_hash(key, hash_key(key, 0), 0, 0)
    }

    #[cfg(test)]
    pub fn remove_at_level<Q: Hash + Eq + ?Sized>(
        &self,
        key: &Q,
        level: usize,
        layer: usize,
    ) -> Option<Self>
    where
        K: Borrow<Q>,
    {
        self.remove_with_hash(key, hash_key(key, layer), level, layer)
    }

    fn remove_with_hash<Q: Hash + Eq + ?Sized>(
        &self,
        key: &Q,
        hash: u64,
        level: usize,
        layer: usize,
    ) -> Option<Self>
    where
        K: Borrow<Q>,
    {
        let index = self.entry_index(hash, level);

        Some(self.set_entry(
            index,
            match &self.entries[index] {
                Entry::Empty => None,
                Entry::KeyValue(key_value) => {
                    if key == key_value.key().borrow() {
                        Some(Entry::Empty)
                    } else {
                        None
                    }
                }
                Entry::Hamt(hamt) => {
                    let (hash, level, layer) = Self::increment_level(&key, hash, level, layer);

                    hamt.remove_with_hash(key, hash, level, layer)
                        .map(Entry::from)
                }
            }?,
        ))
    }

    #[must_use]
    pub fn insert(&self, key: K, value: V) -> (Self, bool) {
        let hash = hash_key(&key, 0);

        self.insert_with_hash(key, hash, value, 0, 0)
    }

    #[cfg(test)]
    pub fn insert_at_level(&self, key: K, value: V, level: usize, layer: usize) -> (Self, bool) {
        let hash = hash_key(&key, layer);

        self.insert_with_hash(key, hash, value, level, layer)
    }

    fn insert_with_hash(
        &self,
        key: K,
        hash: u64,
        value: V,
        level: usize,
        layer: usize,
    ) -> (Self, bool) {
        let index = self.entry_index(hash, level);

        match &self.entries[index] {
            Entry::Empty => (self.set_entry(index, KeyValue::new(key, value)), true),
            Entry::KeyValue(key_value) => {
                if &key == key_value.key() {
                    (self.set_entry(index, KeyValue::new(key, value)), false)
                } else {
                    let (hash, level, layer) = Self::increment_level(&key, hash, level, layer);

                    let mut hamt = Self::new();

                    hamt.insert_mut_with_hash(
                        key_value.key().clone(),
                        hash_key(key_value.key(), layer),
                        key_value.value().clone(),
                        level,
                        layer,
                    );
                    hamt.insert_mut_with_hash(key, hash, value, level, layer);

                    (self.set_entry(index, hamt), true)
                }
            }
            Entry::Hamt(hamt) => {
                let (hash, level, layer) = Self::increment_level(&key, hash, level, layer);

                let (hamt, ok) = hamt.insert_with_hash(key, hash, value, level, layer);

                (self.set_entry(index, hamt), ok)
            }
        }
    }

    pub fn first_rest(&self) -> Option<(&K, &V, Self)> {
        self.first_entry().map(|key_value| {
            (
                key_value.key(),
                key_value.value(),
                self.remove(key_value.key()).unwrap(),
            )
        })
    }

    fn first_entry(&self) -> Option<&KeyValue<K, V>> {
        for entry in self.entries.iter() {
            match entry {
                Entry::Empty => {}
                Entry::KeyValue(key_value) => {
                    return Some(key_value);
                }
                Entry::Hamt(hamt) => return hamt.first_entry(),
            }
        }

        None
    }

    pub fn insert_mut(&mut self, key: K, value: V) -> bool {
        let hash = hash_key(&key, 0);

        self.insert_mut_with_hash(key, hash, value, 0, 0)
    }

    fn insert_mut_with_hash(
        &mut self,
        key: K,
        hash: u64,
        value: V,
        level: usize,
        layer: usize,
    ) -> bool {
        let index = self.entry_index(hash, level);

        match &mut self.entries[index] {
            Entry::Empty => {
                self.entries[index] = KeyValue::new(key, value).into();
                true
            }
            Entry::KeyValue(key_value) => {
                let (entry, ok) = if &key == key_value.key() {
                    (KeyValue::new(key, value).into(), false)
                } else {
                    let (hash, level, layer) = Self::increment_level(&key, hash, level, layer);
                    let mut hamt = Self::new();

                    // TODO Cache hash.
                    hamt.insert_mut_with_hash(
                        key_value.key().clone(),
                        hash_key(key_value.key(), layer),
                        key_value.value().clone(),
                        level,
                        layer,
                    );
                    hamt.insert_mut_with_hash(key, hash, value, level, layer);

                    (hamt.into(), true)
                };

                self.entries[index] = entry;

                ok
            }
            Entry::Hamt(hamt) => {
                let (hash, level, layer) = Self::increment_level(&key, hash, level, layer);

                Arc::get_mut(hamt)
                    .unwrap()
                    .insert_mut_with_hash(key, hash, value, level, layer)
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
    fn is_normal(&self) -> bool {
        self.entries.iter().all(|entry| match entry {
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
            })
            .sum()
    }
}

#[derive(Debug)]
pub struct HamtIterator<'a, K: 'a, V: 'a>(Vec<(&'a Hamt<K, V>, usize)>);

impl<'a, K, V> IntoIterator for &'a Hamt<K, V> {
    type IntoIter = HamtIterator<'a, K, V>;
    type Item = (&'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        HamtIterator(vec![(self, 0)])
    }
}

impl<'a, K, V> Iterator for HamtIterator<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop().and_then(|(hamt, index)| {
            if index == ENTRY_COUNT {
                return self.next();
            }

            self.0.push((hamt, index + 1));

            match &hamt.entries[index] {
                Entry::Empty => self.next(),
                Entry::Hamt(hamt) => {
                    self.0.push((hamt, 0));
                    self.next()
                }
                Entry::KeyValue(key_value) => Some((key_value.key(), key_value.value())),
            }
        })
    }
}

#[derive(Debug)]
pub struct ClonedHamtIterator<K: Clone, V: Clone>(Vec<(Arc<Hamt<K, V>>, usize)>);

impl<K: Clone, V: Clone> IntoIterator for Hamt<K, V> {
    type IntoIter = ClonedHamtIterator<K, V>;
    type Item = (K, V);

    fn into_iter(self) -> Self::IntoIter {
        ClonedHamtIterator(vec![(self.into(), 0)])
    }
}

impl<K: Clone, V: Clone> Iterator for ClonedHamtIterator<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop().and_then(|(hamt, index)| {
            if index == ENTRY_COUNT {
                return self.next();
            }

            self.0.push((hamt.clone(), index + 1));

            match &hamt.entries[index] {
                Entry::Empty => self.next(),
                Entry::Hamt(hamt) => {
                    self.0.push((hamt.clone(), 0));
                    self.next()
                }
                Entry::KeyValue(key_value) => {
                    Some((key_value.key().clone(), key_value.value().clone()))
                }
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{random, rng, seq::SliceRandom};
    use std::collections::HashMap;

    const ITERATION_COUNT: usize = 1 << 12;

    #[test]
    fn new() {
        Hamt::<usize, usize>::new();
    }

    #[test]
    fn insert() {
        let hamt = Hamt::new();

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
        let mut hamt = Hamt::new();

        for index in 0..ITERATION_COUNT {
            let (other, ok) = hamt.insert(index, index);
            hamt = other;
            assert!(ok);
            assert_eq!(hamt.entry_count(), index + 1);
        }
    }

    #[test]
    fn insert_many_at_random() {
        let mut hamt: Hamt<u64, u64> = Hamt::new();

        for index in 0..ITERATION_COUNT {
            let key = random();
            hamt = hamt.insert(key, key).0;
            assert_eq!(hamt.entry_count(), index + 1);
        }
    }

    #[test]
    fn remove() {
        let hamt = Hamt::new();

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
        let mut hamt: Hamt<i16, i16> = Hamt::new();

        for _ in 0..ITERATION_COUNT {
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
        let hamt = Hamt::new();

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
        let mut hamt: Hamt<i16, i16> = Hamt::new();

        for _ in 0..ITERATION_COUNT {
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

        assert_eq!(hamt, Hamt::new());
    }

    #[test]
    fn is_singleton() {
        let hamt = Hamt::new();

        assert!(!hamt.is_singleton());
        assert!(hamt.insert(0, 0).0.is_singleton());
        assert!(!hamt.insert(0, 0).0.insert(1, 0).0.is_singleton());
    }

    #[test]
    fn equality() {
        for _ in 0..8 {
            let mut hamts: [Hamt<i16, i16>; 2] = [Hamt::new(), Hamt::new()];
            let mut inserted_keys: Vec<i16> = (0..ITERATION_COUNT).map(|_| random()).collect();
            let mut deleted_keys: Vec<i16> = (0..ITERATION_COUNT).map(|_| random()).collect();

            for hamt in hamts.iter_mut() {
                inserted_keys.shuffle(&mut rng());
                deleted_keys.shuffle(&mut rng());

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
    fn iterate() {
        let sizes = (0..42)
            .chain((0..100).map(|_| random::<u64>() % 1024))
            .collect::<Vec<_>>();

        for layer in 0..=1 {
            for level in 0..=MAX_LEVEL {
                for size in &sizes {
                    let mut hamt: Hamt<i16, i16> = Hamt::new();
                    let mut map: HashMap<i16, i16> = HashMap::new();

                    for _ in 0..*size {
                        let key = random();
                        let value = random();

                        hamt = hamt.insert_at_level(key, value, level, layer).0;

                        map.insert(key, value);
                    }

                    let mut size = 0;

                    for (key, value) in &hamt {
                        size += 1;

                        assert_eq!(map[key], *value);
                    }

                    assert_eq!(size, hamt.entry_count());
                }
            }
        }
    }
}
