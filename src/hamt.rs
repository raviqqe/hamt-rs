use bucket::Bucket;
use node::Node;
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
    sync::Arc,
};

const MAX_LEVEL: u8 = 64 / 5;
const ENTRY_COUNT: usize = 32;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Entry<K, V> {
    Empty,
    KeyValue(K, V),
    Hamt(Arc<Hamt<K, V>>),
    Bucket(Bucket<K, V>),
}

impl<K, V> Default for Entry<K, V> {
    fn default() -> Self {
        Entry::Empty
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Hamt<K, V> {
    // TODO: Use bitmaps and raw union types for performance.
    level: u8,
    entries: [Entry<K, V>; ENTRY_COUNT],
}

impl<K: Clone + Hash + PartialEq, V: Clone> Hamt<K, V> {
    pub fn new(level: u8) -> Self {
        Hamt {
            level,
            entries: Default::default(),
        }
    }

    fn entry_index(&self, key: &K) -> usize {
        ((hash(key) >> (self.level * 5)) & 0b11111) as usize
    }

    fn set_entry(&self, index: usize, entry: Entry<K, V>) -> Self {
        let mut entries = self.entries.clone();

        entries[index] = entry;

        Hamt {
            level: self.level,
            entries,
        }
    }

    #[cfg(test)]
    fn contain_bucket(&self) -> bool {
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
}

impl<K: Clone + Hash + PartialEq, V: Clone> Node for Hamt<K, V> {
    type Key = K;
    type Value = V;

    fn insert(&self, k: K, v: V) -> (Self, bool) {
        let i = self.entry_index(&k);

        match &self.entries[i] {
            Entry::Empty => (self.set_entry(i, Entry::KeyValue(k, v)), true),
            Entry::KeyValue(kk, vv) => {
                if *kk == k {
                    return (self.set_entry(i, Entry::KeyValue(k, v)), false);
                }

                (
                    self.set_entry(
                        i,
                        if self.level < MAX_LEVEL {
                            Entry::Hamt(Arc::new(
                                Hamt::new(self.level + 1)
                                    .insert(kk.clone(), vv.clone())
                                    .0
                                    .insert(k, v)
                                    .0,
                            ))
                        } else {
                            Entry::Bucket(Bucket::new(kk.clone(), vv.clone()).insert(k, v).0)
                        },
                    ),
                    true,
                )
            }
            Entry::Hamt(h) => {
                let (h, new) = h.insert(k, v);
                (self.set_entry(i, Entry::Hamt(Arc::new(h))), new)
            }
            Entry::Bucket(b) => {
                let (b, new) = b.insert(k, v);
                (self.set_entry(i, Entry::Bucket(b)), new)
            }
        }
    }

    fn delete(&self, key: &K) -> Option<Self> {
        let index = self.entry_index(key);

        Some(self.set_entry(
            index,
            match &self.entries[index] {
                Entry::Empty => return None,
                Entry::KeyValue(other_key, _) => {
                    if key == other_key {
                        Entry::Empty
                    } else {
                        return None;
                    }
                }
                Entry::Hamt(h) => match h.delete(key) {
                    None => return None,
                    Some(h) => node_to_entry(&h, |h| Entry::Hamt(Arc::new(h))),
                },
                Entry::Bucket(b) => match b.delete(key) {
                    None => return None,
                    Some(b) => node_to_entry(&b, Entry::Bucket),
                },
            },
        ))
    }

    fn find(&self, key: &K) -> Option<&V> {
        match &self.entries[self.entry_index(key)] {
            Entry::Empty => None,
            Entry::KeyValue(other_key, value) => {
                if key == other_key {
                    Some(value)
                } else {
                    None
                }
            }
            Entry::Hamt(hamt) => hamt.find(key),
            Entry::Bucket(bucket) => bucket.find(key),
        }
    }

    fn first_rest(&self) -> Option<(&K, &V, Self)> {
        for (i, e) in self.entries.iter().enumerate() {
            match e {
                Entry::Empty => {}
                Entry::KeyValue(k, v) => return Some((k, v, self.delete(k).unwrap())),
                Entry::Hamt(h) => {
                    let (k, v, r) = h.first_rest().unwrap();
                    return Some((
                        k,
                        v,
                        self.set_entry(i, node_to_entry(&r, |h| Entry::Hamt(Arc::new(h)))),
                    ));
                }
                Entry::Bucket(b) => {
                    let (k, v, r) = b.first_rest().unwrap();
                    return Some((k, v, self.set_entry(i, node_to_entry(&r, Entry::Bucket))));
                }
            }
        }

        None
    }

    fn is_singleton(&self) -> bool {
        self.entries
            .iter()
            .map(|e| match *e {
                Entry::Empty => 0,
                Entry::KeyValue(_, _) => 1,
                _ => 2,
            })
            .sum::<usize>()
            == 1
    }

    fn size(&self) -> usize {
        self.entries
            .iter()
            .map(|e| match e {
                Entry::Empty => 0,
                Entry::KeyValue(_, _) => 1,
                Entry::Hamt(h) => h.size(),
                Entry::Bucket(b) => b.size(),
            })
            .sum()
    }
}

fn node_to_entry<N: Clone + Node>(
    node: &N,
    to_entry: fn(N) -> Entry<N::Key, N::Value>,
) -> Entry<N::Key, N::Value>
where
    N::Key: Clone,
    N::Value: Clone,
{
    if node.is_singleton() {
        let (key, value, _) = node.first_rest().unwrap();
        Entry::KeyValue(key.clone(), value.clone())
    } else {
        to_entry(node.clone())
    }
}

fn hash<K: Hash>(key: &K) -> u64 {
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    hasher.finish()
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
        self.0.pop().and_then(|t| match t {
            (NodeRef::Hamt(hamt), index) => {
                if index == ENTRY_COUNT {
                    return self.next();
                }

                self.0.push((t.0, index + 1));

                match &hamt.entries[index] {
                    Entry::Empty => self.next(),
                    Entry::Hamt(hamt) => {
                        self.0.push((NodeRef::Hamt(hamt), 0));
                        self.next()
                    }
                    Entry::KeyValue(key, value) => Some((key, value)),
                    Entry::Bucket(bucket) => {
                        self.0.push((NodeRef::Bucket(bucket), 0));
                        self.next()
                    }
                }
            }
            (NodeRef::Bucket(bucket), i) => {
                if i == bucket.to_vec().len() {
                    return self.next();
                }

                self.0.push((t.0, i + 1));

                let (k, v) = &bucket.to_vec()[i];
                Some((k, v))
            }
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::{random, seq::SliceRandom, thread_rng};
    use std::collections::{HashMap, HashSet};
    use test::Bencher;

    const NUM_ITERATIONS: usize = 1 << 12;

    #[test]
    fn new() {
        Hamt::<usize, usize>::new(0);
    }

    #[test]
    fn insert() {
        let hamt = Hamt::new(0);

        assert_eq!(hamt.size(), 0);

        let (other, ok) = hamt.insert(0, 0);

        assert!(ok);
        assert_eq!(other.size(), 1);

        let (other, ok) = other.insert(0, 0);

        assert!(!ok);
        assert_eq!(other.size(), 1);

        let (hamt, ok) = other.insert(1, 0);

        assert!(ok);
        assert_eq!(hamt.size(), 2);
    }

    #[test]
    fn insert_many_in_order() {
        let mut hamt = Hamt::new(0);

        for index in 0..NUM_ITERATIONS {
            let (other, ok) = hamt.insert(index, index);
            hamt = other;
            assert!(ok);
            assert_eq!(hamt.size(), index + 1);
        }
    }

    #[test]
    fn insert_many_at_random() {
        let mut hamt: Hamt<usize, usize> = Hamt::new(0);

        for index in 0..NUM_ITERATIONS {
            let key = random();
            hamt = hamt.insert(key, key).0;
            assert_eq!(hamt.size(), index + 1);
        }
    }

    #[test]
    fn delete() {
        let hamt = Hamt::new(0);

        assert_eq!(hamt.insert(0, 0).0.delete(&0), Some(hamt.clone()));
        assert_eq!(hamt.insert(0, 0).0.delete(&1), None);
        assert_eq!(
            hamt.insert(0, 0).0.insert(1, 0).0.delete(&0),
            Some(hamt.insert(1, 0).0)
        );
        assert_eq!(
            hamt.insert(0, 0).0.insert(1, 0).0.delete(&1),
            Some(hamt.insert(0, 0).0)
        );
        assert_eq!(hamt.insert(0, 0).0.insert(1, 0).0.delete(&2), None);
    }

    #[test]
    fn insert_delete_many() {
        let mut hamt: Hamt<i16, i16> = Hamt::new(0);

        for _ in 0..NUM_ITERATIONS {
            let key = random();
            let size = hamt.size();
            let found = hamt.find(&key).is_some();

            if random() {
                hamt = hamt.insert(key, key).0;

                assert_eq!(hamt.size(), if found { size } else { size + 1 });
                assert_eq!(hamt.find(&key), Some(&key));
            } else {
                hamt = hamt.delete(&key).unwrap_or(hamt);

                assert_eq!(hamt.size(), if found { size - 1 } else { size });
                assert_eq!(hamt.find(&key), None);
            }

            assert!(hamt.is_normal());
        }
    }

    #[test]
    fn find() {
        let hamt = Hamt::new(0);

        assert_eq!(hamt.insert(0, 0).0.find(&0), Some(&0));
        assert_eq!(hamt.insert(0, 0).0.find(&1), None);
        assert_eq!(hamt.insert(1, 0).0.find(&0), None);
        assert_eq!(hamt.insert(1, 0).0.find(&1), Some(&0));
        assert_eq!(hamt.insert(0, 0).0.insert(1, 0).0.find(&0), Some(&0));
        assert_eq!(hamt.insert(0, 0).0.insert(1, 0).0.find(&1), Some(&0));
        assert_eq!(hamt.insert(0, 0).0.insert(1, 0).0.find(&2), None);
    }

    #[test]
    fn first_rest() {
        let mut hamt: Hamt<i16, i16> = Hamt::new(0);

        for _ in 0..NUM_ITERATIONS {
            let key = random();
            hamt = hamt.insert(key, key).0;

            assert!(hamt.is_normal());
        }

        for _ in 0..hamt.size() {
            let (key, _, rest) = hamt.first_rest().unwrap();

            assert_eq!(rest.size(), hamt.size() - 1);
            assert_eq!(rest.find(key), None);

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
                    *hamt = hamt.delete(key).unwrap_or_else(|| hamt.clone());
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
            assert!(!hamt.contain_bucket());

            hamt = hamt.insert(key, key).0;

            let index = hash(&key) >> 60;

            if set.contains(&index) {
                break;
            }

            set.insert(index);
        }

        assert!(hamt.contain_bucket());
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

                assert_eq!(size, hamt.size());
            }
        }
    }

    fn keys() -> Vec<i16> {
        (0..1000).collect()
    }

    #[bench]
    fn bench_hamt_insert_1000(bencher: &mut Bencher) {
        let keys = keys();

        bencher.iter(|| {
            let mut hamt = Hamt::new(0);

            for key in &keys {
                hamt = hamt.insert(key, key).0;
            }
        });
    }

    #[bench]
    fn bench_hamt_find_1000(bencher: &mut Bencher) {
        let keys = keys();
        let mut hamt = Hamt::new(0);

        for key in &keys {
            hamt = hamt.insert(key, key).0;
        }

        bencher.iter(|| {
            for key in &keys {
                hamt.find(&key);
            }
        });
    }

    #[bench]
    fn bench_hash_map_insert_1000(bencher: &mut Bencher) {
        let keys = keys();

        bencher.iter(|| {
            let mut map = HashMap::new();

            for key in &keys {
                map.insert(key, key);
            }
        });
    }

    #[bench]
    fn bench_hash_map_find_1000(bencher: &mut Bencher) {
        let keys = keys();
        let mut map = HashMap::new();

        for key in &keys {
            map.insert(key, key);
        }

        bencher.iter(|| {
            for key in &keys {
                map.get(&key);
            }
        });
    }
}
