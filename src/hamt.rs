use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use bucket::Bucket;
use node::Node;

const MAX_LEVEL: u8 = 64 / 5;

#[derive(Clone, Debug, Eq, PartialEq)]
enum Entry<K> {
    Empty,
    Key(K),
    Hamt(Hamt<K>),
    Bucket(Bucket<K>),
}

impl<K> Default for Entry<K> {
    fn default() -> Self {
        Entry::Empty
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Hamt<K>(Arc<Inner<K>>);

#[derive(Clone, Debug, Eq, PartialEq)]
struct Inner<K> {
    level: u8,
    entries: [Entry<K>; 32],
}

impl<K: Clone + Hash + Ord> Hamt<K> {
    fn new(l: u8) -> Self {
        Hamt(Arc::new(Inner {
            level: l,
            entries: Default::default(),
        }))
    }

    fn entry_index(&self, k: &K) -> usize {
        ((hash(k) >> (self.0.level * 5)) & 0b11111) as usize
    }

    fn set_entry(&self, i: usize, e: Entry<K>) -> Self {
        let mut es = self.0.entries.clone();
        es[i] = e;
        self.from_entries(es)
    }

    fn from_entries(&self, es: [Entry<K>; 32]) -> Self {
        Hamt(Arc::new(Inner {
            level: self.0.level,
            entries: es,
        }))
    }

    #[cfg(test)]
    fn contain_bucket(&self) -> bool {
        self.0.entries.iter().any(|e| match *e {
            Entry::Bucket(_) => true,
            _ => false,
        })
    }

    #[cfg(test)]
    fn is_normal(&self) -> bool {
        self.0.entries.iter().all(|e| match *e {
            Entry::Bucket(ref b) => !b.is_singleton(),
            Entry::Hamt(ref h) => h.is_normal() && !h.is_singleton(),
            _ => true,
        })
    }
}

impl<K: Clone + Hash + Ord> Node for Hamt<K> {
    type Key = K;

    fn insert(&self, k: K) -> Self {
        let i = self.entry_index(&k);

        self.set_entry(
            i,
            match self.0.entries[i] {
                Entry::Empty => Entry::Key(k),
                Entry::Key(ref kk) => {
                    if *kk == k {
                        Entry::Key(k)
                    } else if self.0.level < MAX_LEVEL {
                        Entry::Hamt(Hamt::new(self.0.level + 1).insert(kk.clone()).insert(k))
                    } else {
                        Entry::Bucket(Bucket::new(kk.clone()).insert(k))
                    }
                }
                Entry::Hamt(ref h) => Entry::Hamt(h.insert(k)),
                Entry::Bucket(ref b) => Entry::Bucket(b.insert(k)),
            },
        )
    }

    fn delete(&self, k: K) -> Option<Self> {
        let i = self.entry_index(&k);

        Some(self.set_entry(
            i,
            match self.0.entries[i] {
                Entry::Empty => return None,
                Entry::Key(ref kk) => if *kk == k {
                    Entry::Empty
                } else {
                    return None;
                },
                Entry::Hamt(ref h) => match h.delete(k) {
                    None => return None,
                    Some(h) => node_to_entry(&h, Entry::Hamt),
                },
                Entry::Bucket(ref b) => match b.delete(k) {
                    None => return None,
                    Some(b) => node_to_entry(&b, Entry::Bucket),
                },
            },
        ))
    }

    fn find(&self, k: K) -> Option<K> {
        match self.0.entries[self.entry_index(&k)] {
            Entry::Empty => None,
            Entry::Key(ref kk) => if *kk == k {
                Some(k.clone())
            } else {
                None
            },
            Entry::Hamt(ref h) => h.find(k),
            Entry::Bucket(ref b) => b.find(k),
        }
    }

    fn first_rest(&self) -> Option<(K, Self)> {
        for (i, e) in self.0.entries.iter().enumerate() {
            match *e {
                Entry::Empty => {}
                Entry::Key(ref k) => return Some((k.clone(), self.delete(k.clone()).unwrap())),
                Entry::Hamt(ref h) => {
                    let (f, r) = h.first_rest().unwrap();
                    return Some((f, self.set_entry(i, node_to_entry(&r, Entry::Hamt))));
                }
                Entry::Bucket(ref b) => {
                    let (f, r) = b.first_rest().unwrap();
                    return Some((f, self.set_entry(i, node_to_entry(&r, Entry::Bucket))));
                }
            }
        }

        None
    }

    fn is_singleton(&self) -> bool {
        self.0
            .entries
            .iter()
            .map(|e| match *e {
                Entry::Empty => 0,
                Entry::Key(_) => 1,
                _ => 2,
            })
            .sum::<usize>() == 1
    }

    fn size(&self) -> usize {
        self.0
            .entries
            .iter()
            .map(|e| match *e {
                Entry::Empty => 0,
                Entry::Key(_) => 1,
                Entry::Hamt(ref h) => h.size(),
                Entry::Bucket(ref b) => b.size(),
            })
            .sum()
    }
}

fn node_to_entry<N: Clone + Node>(n: &N, f: fn(N) -> Entry<N::Key>) -> Entry<N::Key> {
    if n.is_singleton() {
        let (f, _) = n.first_rest().unwrap();
        Entry::Key(f)
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
    use std::collections::HashSet;

    use rand::{random, thread_rng, Rng};

    use super::*;

    const NUM_ITERATIONS: usize = 2 ^ 16;

    #[test]
    fn new() {
        Hamt::new(0) as Hamt<usize>;
    }

    #[test]
    fn insert() {
        let h = Hamt::new(0);

        assert_eq!(h.size(), 0);
        assert_eq!(h.insert(0).size(), 1);
        assert_eq!(h.insert(0).insert(0).size(), 1);
        assert_eq!(h.insert(0).insert(1).size(), 2);
    }

    #[test]
    fn insert_many_in_order() {
        let mut h = Hamt::new(0);

        for i in 0..NUM_ITERATIONS {
            h = h.insert(i);
            assert_eq!(h.size(), i + 1);
        }
    }

    #[test]
    fn insert_many_at_random() {
        let mut h: Hamt<usize> = Hamt::new(0);

        for i in 0..NUM_ITERATIONS {
            h = h.insert(random());
            assert_eq!(h.size(), i + 1);
        }
    }

    #[test]
    fn delete() {
        let h = Hamt::new(0);

        assert_eq!(h.insert(0).delete(0), Some(h.clone()));
        assert_eq!(h.insert(0).delete(1), None);
        assert_eq!(h.insert(0).insert(1).delete(0), Some(h.insert(1)));
        assert_eq!(h.insert(0).insert(1).delete(1), Some(h.insert(0)));
        assert_eq!(h.insert(0).insert(1).delete(2), None);
    }

    #[test]
    fn insert_delete_many() {
        let mut h: Hamt<i16> = Hamt::new(0);

        for _ in 0..NUM_ITERATIONS {
            let k = random();
            let s = h.size();
            let found = h.find(k).is_some();

            if random() {
                h = h.insert(k);

                assert_eq!(h.size(), if found { s } else { s + 1 });
                assert_eq!(h.find(k), Some(k));
            } else {
                h = h.delete(k).or(Some(h)).unwrap();

                assert_eq!(h.size(), if found { s - 1 } else { s });
                assert_eq!(h.find(k), None);
            }

            assert!(h.is_normal());
        }
    }

    #[test]
    fn find() {
        let h = Hamt::new(0);

        assert_eq!(h.insert(0).find(0), Some(0));
        assert_eq!(h.insert(0).find(1), None);
        assert_eq!(h.insert(1).find(0), None);
        assert_eq!(h.insert(1).find(1), Some(1));
        assert_eq!(h.insert(0).insert(1).find(0), Some(0));
        assert_eq!(h.insert(0).insert(1).find(1), Some(1));
        assert_eq!(h.insert(0).insert(1).find(2), None);
    }

    #[test]
    fn first_rest() {
        let mut h: Hamt<i16> = Hamt::new(0);

        for _ in 0..NUM_ITERATIONS {
            h = h.insert(random());

            assert!(h.is_normal());
        }

        for _ in 0..NUM_ITERATIONS {
            let (f, r) = h.first_rest().unwrap();

            assert_eq!(r.size(), h.size() - 1);
            assert_eq!(r.find(f), None);

            h = r;

            assert!(h.is_normal());
        }

        assert_eq!(h, Hamt::new(0));
    }

    #[test]
    fn is_singleton() {
        let h = Hamt::new(0);

        assert!(!h.is_singleton());
        assert!(h.insert(0).is_singleton());
        assert!(!h.insert(0).insert(1).is_singleton());
    }

    #[test]
    fn equality() {
        for _ in 0..8 {
            let mut hs: [Hamt<i16>; 2] = [Hamt::new(0), Hamt::new(0)];
            let ks: [i16; NUM_ITERATIONS] = random();
            let bs: [bool; NUM_ITERATIONS] = random();

            for h in hs.iter_mut() {
                let mut v: Vec<usize> = (0..ks.len()).collect();
                thread_rng().shuffle(&mut v);

                for i in v {
                    let k = ks[i];

                    *h = if bs[i] {
                        h.insert(k.clone())
                    } else {
                        h.delete(k.clone()).or(Some(h.clone())).unwrap()
                    };
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

            h = h.insert(k);

            let i = hash(&k) >> 60;

            if s.contains(&i) {
                break;
            }

            s.insert(i);
        }

        assert!(h.contain_bucket());
    }
}
