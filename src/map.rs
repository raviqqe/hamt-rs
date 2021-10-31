use std::hash::Hash;

use hamt::{Hamt, HamtIterator};
use node::Node;

/// Map data structure of HAMT.
///
/// Note that every method does not modify the original map but creates a new
/// one if necessary.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Map<K, V> {
    size: usize,
    hamt: Hamt<K, V>,
}

impl<K: Clone + Hash + PartialEq, V: Clone> Map<K, V> {
    /// Creates a new map.
    pub fn new() -> Self {
        Map {
            size: 0,
            hamt: Hamt::new(0),
        }
    }

    /// Inserts a key-value pair into a map.
    pub fn insert(&self, k: K, v: V) -> Self {
        let (h, b) = self.hamt.insert(k, v);

        Map {
            size: self.size + (b as usize),
            hamt: h,
        }
    }

    /// Deletes a key and its corresponding value from a map.
    pub fn delete(&self, k: &K) -> Option<Self> {
        self.hamt.delete(k).map(|h| Map {
            size: self.size - 1,
            hamt: h,
        })
    }

    /// Finds a key and its corresponding value in a map.
    pub fn find(&self, k: &K) -> Option<&V> {
        self.hamt.find(k)
    }

    /// Removes the first element in a map and returns a new map containing the
    /// rest of elements.
    pub fn first_rest(&self) -> Option<(&K, &V, Self)> {
        self.hamt.first_rest().map(|(k, v, h)| {
            (
                k,
                v,
                Map {
                    size: self.size - 1,
                    hamt: h,
                },
            )
        })
    }

    /// Returns a size of a map.
    pub fn size(&self) -> usize {
        self.size
    }
}

impl<K: Clone + Hash + PartialEq, V: Clone> Default for Map<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct MapIterator<'a, K: 'a, V: 'a>(HamtIterator<'a, K, V>);

impl<'a, K, V> Iterator for MapIterator<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl<'a, K, V> IntoIterator for &'a Map<K, V> {
    type IntoIter = MapIterator<'a, K, V>;
    type Item = (&'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        MapIterator(self.hamt.into_iter())
    }
}

#[cfg(test)]
mod test {
    use super::Map;
    use rand::{random, seq::SliceRandom, thread_rng};
    use std::thread::spawn;
    use test::Bencher;

    const NUM_ITERATIONS: usize = 1 << 12;

    #[test]
    fn new() {
        Map::<u8, u8>::new();
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

        assert_eq!(h.insert(0, 0).delete(&0), Some(h.clone()));
        assert_eq!(h.insert(0, 0).delete(&1), None);
        assert_eq!(h.insert(0, 0).insert(1, 0).delete(&0), Some(h.insert(1, 0)));
        assert_eq!(h.insert(0, 0).insert(1, 0).delete(&1), Some(h.insert(0, 0)));
        assert_eq!(h.insert(0, 0).insert(1, 0).delete(&2), None);
    }

    #[test]
    fn insert_delete_many() {
        let mut h: Map<i16, i16> = Map::new();

        for _ in 0..NUM_ITERATIONS {
            let k = random();
            let s = h.size();
            let found = h.find(&k).is_some();

            if random() {
                h = h.insert(k, k);

                assert_eq!(h.size(), if found { s } else { s + 1 });
                assert_eq!(h.find(&k), Some(&k));
            } else {
                h = h.delete(&k).unwrap_or(h);

                assert_eq!(h.size(), if found { s - 1 } else { s });
                assert_eq!(h.find(&k), None);
            }
        }
    }

    #[test]
    fn find() {
        let h = Map::new();

        assert_eq!(h.insert(0, 0).find(&0), Some(&0));
        assert_eq!(h.insert(0, 0).find(&1), None);
        assert_eq!(h.insert(1, 0).find(&0), None);
        assert_eq!(h.insert(1, 0).find(&1), Some(&0));
        assert_eq!(h.insert(0, 0).insert(1, 0).find(&0), Some(&0));
        assert_eq!(h.insert(0, 0).insert(1, 0).find(&1), Some(&0));
        assert_eq!(h.insert(0, 0).insert(1, 0).find(&2), None);
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
                assert_eq!(r.find(f), None);

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
                is.shuffle(&mut thread_rng());
                ds.shuffle(&mut thread_rng());

                for i in &is {
                    *h = h.insert(*i, *i);
                }

                for d in &ds {
                    *h = h.delete(d).unwrap_or_else(|| h.clone());
                }
            }

            assert_eq!(hs[0], hs[1]);
        }
    }

    #[test]
    fn send_and_sync() {
        let m: Map<usize, usize> = Map::new();
        spawn(move || m);
        let m: Map<String, String> = Map::new();
        spawn(move || m);
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
