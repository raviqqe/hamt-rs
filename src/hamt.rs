use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use bucket::Bucket;
use node::Node;

const MAX_LEVEL: u8 = 64 / 5;

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
    // TODO: Use bitmap.
    level: u8,
    entries: [Entry<K, V>; 32],
}

impl<K: Clone + Hash + PartialEq, V: Clone> Hamt<K, V> {
    pub fn new(l: u8) -> Self {
        Hamt {
            level: l,
            entries: Default::default(),
        }
    }

    fn entry_index(&self, k: &K) -> usize {
        ((hash(k) >> (self.level * 5)) & 0b11111) as usize
    }

    fn set_entry(&self, i: usize, e: Entry<K, V>) -> Self {
        let mut es = self.entries.clone();
        es[i] = e;
        self.from_entries(es)
    }

    fn from_entries(&self, es: [Entry<K, V>; 32]) -> Self {
        Hamt {
            level: self.level,
            entries: es,
        }
    }

    #[cfg(test)]
    fn contain_bucket(&self) -> bool {
        self.entries.iter().any(|e| match *e {
            Entry::Bucket(_) => true,
            _ => false,
        })
    }

    #[cfg(test)]
    fn is_normal(&self) -> bool {
        self.entries.iter().all(|e| match *e {
            Entry::Bucket(ref b) => !b.is_singleton(),
            Entry::Hamt(ref h) => h.is_normal() && !h.is_singleton(),
            _ => true,
        })
    }
}

impl<K: Clone + Hash + PartialEq, V: Clone> Node for Hamt<K, V> {
    type Key = K;
    type Value = V;

    fn insert(&self, k: K, v: V) -> (Self, bool) {
        let i = self.entry_index(&k);

        match self.entries[i] {
            Entry::Empty => (self.set_entry(i, Entry::KeyValue(k, v)), true),
            Entry::KeyValue(ref kk, ref vv) => {
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
            Entry::Hamt(ref h) => {
                let (h, new) = h.insert(k, v);
                (self.set_entry(i, Entry::Hamt(Arc::new(h))), new)
            }
            Entry::Bucket(ref b) => {
                let (b, new) = b.insert(k, v);
                (self.set_entry(i, Entry::Bucket(b)), new)
            }
        }
    }

    fn delete(&self, k: &K) -> Option<Self> {
        let i = self.entry_index(k);

        Some(self.set_entry(
            i,
            match self.entries[i] {
                Entry::Empty => return None,
                Entry::KeyValue(ref kk, _) => if *kk == *k {
                    Entry::Empty
                } else {
                    return None;
                },
                Entry::Hamt(ref h) => match h.delete(k) {
                    None => return None,
                    Some(h) => node_to_entry(&h, |h| Entry::Hamt(Arc::new(h))),
                },
                Entry::Bucket(ref b) => match b.delete(k) {
                    None => return None,
                    Some(b) => node_to_entry(&b, Entry::Bucket),
                },
            },
        ))
    }

    fn find(&self, k: &K) -> Option<(&K, &V)> {
        match self.entries[self.entry_index(k)] {
            Entry::Empty => None,
            Entry::KeyValue(ref kk, ref vv) => if *kk == *k {
                Some((kk, vv))
            } else {
                None
            },
            Entry::Hamt(ref h) => h.find(k),
            Entry::Bucket(ref b) => b.find(k),
        }
    }

    fn first_rest(&self) -> Option<(&K, &V, Self)> {
        for (i, e) in self.entries.iter().enumerate() {
            match *e {
                Entry::Empty => {}
                Entry::KeyValue(ref k, ref v) => return Some((k, v, self.delete(k).unwrap())),
                Entry::Hamt(ref h) => {
                    let (k, v, r) = h.first_rest().unwrap();
                    return Some((
                        k,
                        v,
                        self.set_entry(i, node_to_entry(&r, |h| Entry::Hamt(Arc::new(h)))),
                    ));
                }
                Entry::Bucket(ref b) => {
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
            .sum::<usize>() == 1
    }

    fn size(&self) -> usize {
        self.entries
            .iter()
            .map(|e| match *e {
                Entry::Empty => 0,
                Entry::KeyValue(_, _) => 1,
                Entry::Hamt(ref h) => h.size(),
                Entry::Bucket(ref b) => b.size(),
            })
            .sum()
    }
}

fn node_to_entry<N: Clone + Node>(
    n: &N,
    f: fn(N) -> Entry<N::Key, N::Value>,
) -> Entry<N::Key, N::Value>
where
    N::Key: Clone,
    N::Value: Clone,
{
    if n.is_singleton() {
        let (k, v, _) = n.first_rest().unwrap();
        Entry::KeyValue(k.clone(), v.clone())
    } else {
        f(n.clone())
    }
}

fn hash<K: Hash>(k: &K) -> u64 {
    let mut h = DefaultHasher::new();
    k.hash(&mut h);
    h.finish()
}

#[cfg(test)]
mod test {
    use std::collections::{HashMap, HashSet};

    use rand::{random, thread_rng, Rng};
    use test::Bencher;

    use super::*;

    const NUM_ITERATIONS: usize = 1 << 12;

    #[test]
    fn new() {
        Hamt::new(0) as Hamt<usize, usize>;
    }

    #[test]
    fn insert() {
        let h = Hamt::new(0);

        assert_eq!(h.size(), 0);

        let (h, b) = h.insert(0, 0);

        assert!(b);
        assert_eq!(h.size(), 1);

        let (hh, b) = h.insert(0, 0);

        assert!(!b);
        assert_eq!(hh.size(), 1);

        let (h, b) = h.insert(1, 0);

        assert!(b);
        assert_eq!(h.size(), 2);
    }

    #[test]
    fn insert_many_in_order() {
        let mut h = Hamt::new(0);

        for i in 0..NUM_ITERATIONS {
            let (hh, b) = h.insert(i, i);
            h = hh;
            assert!(b);
            assert_eq!(h.size(), i + 1);
        }
    }

    #[test]
    fn insert_many_at_random() {
        let mut h: Hamt<usize, usize> = Hamt::new(0);

        for i in 0..NUM_ITERATIONS {
            let k = random();
            h = h.insert(k, k).0;
            assert_eq!(h.size(), i + 1);
        }
    }

    #[test]
    fn delete() {
        let h = Hamt::new(0);

        assert_eq!(h.insert(0, 0).0.delete(&0), Some(h.clone()));
        assert_eq!(h.insert(0, 0).0.delete(&1), None);
        assert_eq!(
            h.insert(0, 0).0.insert(1, 0).0.delete(&0),
            Some(h.insert(1, 0).0)
        );
        assert_eq!(
            h.insert(0, 0).0.insert(1, 0).0.delete(&1),
            Some(h.insert(0, 0).0)
        );
        assert_eq!(h.insert(0, 0).0.insert(1, 0).0.delete(&2), None);
    }

    #[test]
    fn insert_delete_many() {
        let mut h: Hamt<i16, i16> = Hamt::new(0);

        for _ in 0..NUM_ITERATIONS {
            let k = random();
            let s = h.size();
            let found = h.find(&k).is_some();

            if random() {
                h = h.insert(k, k).0;

                assert_eq!(h.size(), if found { s } else { s + 1 });
                assert_eq!(h.find(&k), Some((&k, &k)));
            } else {
                h = h.delete(&k).unwrap_or(h);

                assert_eq!(h.size(), if found { s - 1 } else { s });
                assert_eq!(h.find(&k), None);
            }

            assert!(h.is_normal());
        }
    }

    #[test]
    fn find() {
        let h = Hamt::new(0);

        assert_eq!(h.insert(0, 0).0.find(&0), Some((&0, &0)));
        assert_eq!(h.insert(0, 0).0.find(&1), None);
        assert_eq!(h.insert(1, 0).0.find(&0), None);
        assert_eq!(h.insert(1, 0).0.find(&1), Some((&1, &0)));
        assert_eq!(h.insert(0, 0).0.insert(1, 0).0.find(&0), Some((&0, &0)));
        assert_eq!(h.insert(0, 0).0.insert(1, 0).0.find(&1), Some((&1, &0)));
        assert_eq!(h.insert(0, 0).0.insert(1, 0).0.find(&2), None);
    }

    #[test]
    fn first_rest() {
        let mut h: Hamt<i16, i16> = Hamt::new(0);

        for _ in 0..NUM_ITERATIONS {
            let k = random();
            h = h.insert(k, k).0;

            assert!(h.is_normal());
        }

        for _ in 0..h.size() {
            let new: Hamt<i16, i16>;

            {
                let (k, _, r) = h.first_rest().unwrap();

                assert_eq!(r.size(), h.size() - 1);
                assert_eq!(r.find(k), None);

                new = r;
            }

            h = new;

            assert!(h.is_normal());
        }

        assert_eq!(h, Hamt::new(0));
    }

    #[test]
    fn is_singleton() {
        let h = Hamt::new(0);

        assert!(!h.is_singleton());
        assert!(h.insert(0, 0).0.is_singleton());
        assert!(!h.insert(0, 0).0.insert(1, 0).0.is_singleton());
    }

    #[test]
    fn equality() {
        for _ in 0..8 {
            let mut hs: [Hamt<i16, i16>; 2] = [Hamt::new(0), Hamt::new(0)];
            let mut is: Vec<i16> = (0..NUM_ITERATIONS).map(|_| random()).collect();
            let mut ds: Vec<i16> = (0..NUM_ITERATIONS).map(|_| random()).collect();

            for h in hs.iter_mut() {
                thread_rng().shuffle(&mut is);
                thread_rng().shuffle(&mut ds);

                for i in &is {
                    *h = h.insert(*i, *i).0;
                }

                for d in &ds {
                    *h = h.delete(&d).unwrap_or(h.clone());
                }
            }

            assert_eq!(hs[0], hs[1]);
        }
    }

    #[test]
    fn collision() {
        let mut h = Hamt::new(MAX_LEVEL);
        let mut s = HashSet::new();

        for k in 0.. {
            assert!(!h.contain_bucket());

            h = h.insert(k, k).0;

            let i = hash(&k) >> 60;

            if s.contains(&i) {
                break;
            }

            s.insert(i);
        }

        assert!(h.contain_bucket());
    }

    fn keys() -> Vec<i16> {
        (0..1000).collect()
    }

    #[bench]
    fn bench_insert_1000(b: &mut Bencher) {
        let ks = keys();

        b.iter(|| {
            let mut h = Hamt::new(0);

            for k in &ks {
                h = h.insert(k, k).0;
            }
        });
    }

    #[bench]
    fn bench_find_1000(b: &mut Bencher) {
        let ks = keys();
        let mut h = Hamt::new(0);

        for k in &ks {
            h = h.insert(k, k).0;
        }

        b.iter(|| {
            for k in &ks {
                h.find(&k);
            }
        });
    }

    #[bench]
    fn bench_hash_map_insert_1000(b: &mut Bencher) {
        let ks = keys();

        b.iter(|| {
            let mut h = HashMap::new();

            for k in &ks {
                h.insert(k, k);
            }
        });
    }

    #[bench]
    fn bench_hash_map_find_1000(b: &mut Bencher) {
        let ks = keys();
        let mut h = HashMap::new();

        for k in &ks {
            h.insert(k, k);
        }

        b.iter(|| {
            for k in &ks {
                h.get(&k);
            }
        });
    }
}
