use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::mem::uninitialized;

use hamt::Hamt;
use node::Node;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Map<K, V> {
    size: usize,
    hamt: Hamt<Entry<K, V>>,
}

impl<K: Clone + Hash + Ord, V: Clone> Map<K, V> {
    pub fn new() -> Self {
        Map {
            size: 0,
            hamt: Hamt::new(0),
        }
    }

    pub fn insert(&self, k: K, v: V) -> Self {
        let mut s = self.size;
        let e = Entry(k, v);

        if let None = self.hamt.find(&e) {
            s += 1;
        }

        Map {
            size: s,
            hamt: self.hamt.insert(e),
        }
    }

    pub fn delete(&self, k: K) -> Option<Self> {
        self.hamt.delete(&Self::key_only_entry(k)).map(|h| Map {
            size: self.size - 1,
            hamt: h,
        })
    }

    pub fn find(&self, k: K) -> Option<(&K, &V)> {
        self.hamt
            .find(&Self::key_only_entry(k))
            .map(|e| (&e.0, &e.1))
    }

    pub fn first_rest(&self) -> Option<(&K, &V, Self)> {
        self.hamt.first_rest().map(|(e, h)| {
            (
                &e.0,
                &e.1,
                Map {
                    size: self.size - 1,
                    hamt: h,
                },
            )
        })
    }

    pub fn size(&self) -> usize {
        self.size
    }

    fn key_only_entry(k: K) -> Entry<K, V> {
        Entry(k, unsafe { uninitialized() })
    }
}

#[derive(Clone, Debug)]
struct Entry<K, V>(K, V);

impl<K: Hash, V> Hash for Entry<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<K: Ord, V> Ord for Entry<K, V> {
    fn cmp(&self, e: &Self) -> Ordering {
        self.0.cmp(&e.0)
    }
}

impl<K: PartialOrd, V> PartialOrd for Entry<K, V> {
    fn partial_cmp(&self, e: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&e.0)
    }
}

impl<K: PartialEq, V> Eq for Entry<K, V> {}

impl<K: PartialEq, V> PartialEq for Entry<K, V> {
    fn eq(&self, e: &Self) -> bool {
        self.0 == e.0
    }
}

#[cfg(test)]
mod test {
    use rand::{random, thread_rng, Rng};
    use test::Bencher;

    use super::Map;

    const NUM_ITERATIONS: usize = 1 << 12;

    #[test]
    fn new() {
        Map::new() as Map<usize, usize>;
    }

    #[test]
    fn insert() {
        let h = Map::new();

        assert_eq!(h.size(), 0);
        assert_eq!(h.insert(0, 0).size(), 1);
        assert_eq!(h.insert(0, 0).insert(0, 0).size(), 1);
        assert_eq!(h.insert(0, 0).insert(1, 0).size(), 2);
    }

    #[test]
    fn insert_many_in_order() {
        let mut h = Map::new();

        for i in 0..NUM_ITERATIONS {
            h = h.insert(i, i);
            assert_eq!(h.size(), i + 1);
        }
    }

    #[test]
    fn insert_many_at_random() {
        let mut h: Map<usize, usize> = Map::new();

        for i in 0..NUM_ITERATIONS {
            let k = random();
            h = h.insert(k, k);
            assert_eq!(h.size(), i + 1);
        }
    }

    #[test]
    fn delete() {
        let h = Map::new();

        assert_eq!(h.insert(0, 0).delete(0), Some(h.clone()));
        assert_eq!(h.insert(0, 0).delete(1), None);
        assert_eq!(h.insert(0, 0).insert(1, 0).delete(0), Some(h.insert(1, 0)));
        assert_eq!(h.insert(0, 0).insert(1, 0).delete(1), Some(h.insert(0, 0)));
        assert_eq!(h.insert(0, 0).insert(1, 0).delete(2), None);
    }

    #[test]
    fn insert_delete_many() {
        let mut h: Map<i16, i16> = Map::new();

        for _ in 0..NUM_ITERATIONS {
            let k = random();
            let s = h.size();
            let found = h.find(k).is_some();

            if random() {
                h = h.insert(k, k);

                assert_eq!(h.size(), if found { s } else { s + 1 });
                assert_eq!(h.find(k), Some((&k, &k)));
            } else {
                h = h.delete(k).unwrap_or(h);

                assert_eq!(h.size(), if found { s - 1 } else { s });
                assert_eq!(h.find(k), None);
            }
        }
    }

    #[test]
    fn find() {
        let h = Map::new();

        assert_eq!(h.insert(0, 0).find(0), Some((&0, &0)));
        assert_eq!(h.insert(0, 0).find(1), None);
        assert_eq!(h.insert(1, 0).find(0), None);
        assert_eq!(h.insert(1, 0).find(1), Some((&1, &0)));
        assert_eq!(h.insert(0, 0).insert(1, 0).find(0), Some((&0, &0)));
        assert_eq!(h.insert(0, 0).insert(1, 0).find(1), Some((&1, &0)));
        assert_eq!(h.insert(0, 0).insert(1, 0).find(2), None);
    }

    #[test]
    fn first_rest() {
        let mut h: Map<i16, i16> = Map::new();

        for _ in 0..NUM_ITERATIONS {
            h = h.insert(random(), 0);
        }

        for _ in 0..h.size() {
            let new: Map<i16, i16>;

            {
                let (f, _, r) = h.first_rest().unwrap();

                assert_eq!(r.size(), h.size() - 1);
                assert_eq!(r.find(*f), None);

                new = r;
            }

            h = new;
        }

        assert_eq!(h, Map::new());
    }

    #[test]
    fn equality() {
        for _ in 0..8 {
            let mut hs: [Map<i16, i16>; 2] = [Map::new(), Map::new()];
            let mut is: Vec<i16> = (0..NUM_ITERATIONS).map(|_| random()).collect();
            let mut ds: Vec<i16> = (0..NUM_ITERATIONS).map(|_| random()).collect();

            for h in hs.iter_mut() {
                thread_rng().shuffle(&mut is);
                thread_rng().shuffle(&mut ds);

                for i in &is {
                    *h = h.insert(*i, *i);
                }

                for d in &ds {
                    *h = h.delete(*d).unwrap_or(h.clone());
                }
            }

            assert_eq!(hs[0], hs[1]);
        }
    }

    fn keys() -> Vec<i16> {
        (0..1000).collect()
    }

    #[bench]
    fn bench_insert_1000(b: &mut Bencher) {
        let ks = keys();

        b.iter(|| {
            let mut h = Map::new();

            for k in &ks {
                h = h.insert(k, k);
            }
        });
    }

    #[bench]
    fn bench_find_1000(b: &mut Bencher) {
        let ks = keys();
        let mut h = Map::new();

        for k in &ks {
            h = h.insert(k, k);
        }

        b.iter(|| {
            for k in &ks {
                h.find(&k);
            }
        });
    }
}
