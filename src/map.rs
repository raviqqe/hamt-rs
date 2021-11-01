use crate::{
    hamt::{Hamt, HamtIterator},
    node::Node,
};
use std::{hash::Hash, ops::Index};

/// Map data structure of HAMT.
///
/// Note that every method does not modify the original map but creates a new
/// one if necessary.
#[derive(Clone, Debug, Eq, PartialEq)]
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

    /// Finds a key and its corresponding value in a map.
    pub fn get(&self, key: &K) -> Option<&V> {
        self.hamt.get(key)
    }

    /// Checks if a key is contained in a map.
    pub fn contains_key(&self, key: &K) -> bool {
        self.hamt.get(key).is_some()
    }

    /// Inserts a key-value pair into a map.
    pub fn insert(&self, key: K, value: V) -> Self {
        let (hamt, ok) = self.hamt.insert(key, value);

        Map {
            size: self.size + (ok as usize),
            hamt,
        }
    }

    /// Removes a key and returns its corresponding value from a map if any.
    pub fn remove(&self, key: &K) -> Option<Self> {
        self.hamt.remove(key).map(|hamt| Map {
            size: self.size - 1,
            hamt,
        })
    }

    /// Returns a size of a map.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns true if a map is empty.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Returns keys in a map
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.into_iter().map(|(key, _)| key)
    }

    /// Returns keys in a map
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.into_iter().map(|(_, value)| value)
    }

    /// Removes the first element in a map and returns a new map containing the
    /// rest of elements.
    pub fn first_rest(&self) -> Option<(&K, &V, Self)> {
        self.hamt.first_rest().map(|(key, value, hamt)| {
            (
                key,
                value,
                Map {
                    size: self.size - 1,
                    hamt,
                },
            )
        })
    }
}

impl<K: Clone + Hash + PartialEq, V: Clone> Default for Map<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

// TODO Remove Clone requirements.
impl<K: Hash + PartialEq + Clone, V: Clone> Index<&K> for Map<K, V> {
    type Output = V;

    fn index(&self, key: &K) -> &V {
        self.get(key).expect("invalid key")
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

    const NUM_ITERATIONS: usize = 1 << 12;

    #[test]
    fn new() {
        Map::<u8, u8>::new();
    }

    #[test]
    fn insert() {
        let map = Map::new();

        assert_eq!(map.len(), 0);
        assert_eq!(map.insert(0, 0).len(), 1);
        assert_eq!(map.insert(0, 0).insert(0, 0).len(), 1);
        assert_eq!(map.insert(0, 0).insert(1, 0).len(), 2);
    }

    #[test]
    fn insert_many_in_order() {
        let mut map = Map::new();

        for index in 0..NUM_ITERATIONS {
            map = map.insert(index, index);
            assert_eq!(map.len(), index + 1);
        }
    }

    #[test]
    fn insert_many_at_random() {
        let mut map: Map<usize, usize> = Map::new();

        for index in 0..NUM_ITERATIONS {
            let ey = random();
            map = map.insert(ey, ey);
            assert_eq!(map.len(), index + 1);
        }
    }

    #[test]
    fn remove() {
        let map = Map::new();

        assert_eq!(map.insert(0, 0).remove(&0), Some(map.clone()));
        assert_eq!(map.insert(0, 0).remove(&1), None);
        assert_eq!(
            map.insert(0, 0).insert(1, 0).remove(&0),
            Some(map.insert(1, 0))
        );
        assert_eq!(
            map.insert(0, 0).insert(1, 0).remove(&1),
            Some(map.insert(0, 0))
        );
        assert_eq!(map.insert(0, 0).insert(1, 0).remove(&2), None);
    }

    #[test]
    fn insert_remove_many() {
        let mut map: Map<i16, i16> = Map::new();

        for _ in 0..NUM_ITERATIONS {
            let key = random();
            let size = map.len();
            let found = map.get(&key).is_some();

            if random() {
                map = map.insert(key, key);

                assert_eq!(map.len(), if found { size } else { size + 1 });
                assert_eq!(map.get(&key), Some(&key));
            } else {
                map = map.remove(&key).unwrap_or(map);

                assert_eq!(map.len(), if found { size - 1 } else { size });
                assert_eq!(map.get(&key), None);
            }
        }
    }

    #[test]
    fn get() {
        let map = Map::new();

        assert_eq!(map.insert(0, 0).get(&0), Some(&0));
        assert_eq!(map.insert(0, 0).get(&1), None);
        assert_eq!(map.insert(1, 0).get(&0), None);
        assert_eq!(map.insert(1, 0).get(&1), Some(&0));
        assert_eq!(map.insert(0, 0).insert(1, 0).get(&0), Some(&0));
        assert_eq!(map.insert(0, 0).insert(1, 0).get(&1), Some(&0));
        assert_eq!(map.insert(0, 0).insert(1, 0).get(&2), None);
    }

    #[test]
    fn first_rest() {
        let mut map: Map<i16, i16> = Map::new();

        for _ in 0..NUM_ITERATIONS {
            map = map.insert(random(), 0);
        }

        for _ in 0..map.len() {
            let (key, _, rest) = map.first_rest().unwrap();

            assert_eq!(rest.len(), map.len() - 1);
            assert_eq!(rest.get(key), None);

            map = rest;
        }

        assert_eq!(map, Map::new());
    }

    #[test]
    fn equality() {
        for _ in 0..8 {
            let mut maps: [Map<i16, i16>; 2] = [Map::new(), Map::new()];
            let mut inserted_keys: Vec<i16> = (0..NUM_ITERATIONS).map(|_| random()).collect();
            let mut deleted_keys: Vec<i16> = (0..NUM_ITERATIONS).map(|_| random()).collect();

            for map in maps.iter_mut() {
                inserted_keys.shuffle(&mut thread_rng());
                deleted_keys.shuffle(&mut thread_rng());

                for key in &inserted_keys {
                    *map = map.insert(*key, *key);
                }

                for key in &deleted_keys {
                    *map = map.remove(key).unwrap_or_else(|| map.clone());
                }
            }

            assert_eq!(maps[0], maps[1]);
        }
    }

    #[test]
    fn send_and_sync() {
        let map: Map<usize, usize> = Map::new();
        spawn(move || map);

        let map: Map<String, String> = Map::new();
        spawn(move || map);
    }

    // fn generate_keys() -> Vec<usize> {
    //     (0..10000).collect()
    // }

    // #[bench]
    // fn bench_insert(bencher: &mut Bencher) {
    //     let keys = generate_keys();

    //     bencher.iter(|| {
    //         let mut map = Map::new();

    //         for key in &keys {
    //             map = map.insert(key, key);
    //         }
    //     });
    // }

    // #[bench]
    // fn bench_get(bencher: &mut Bencher) {
    //     let keys = generate_keys();
    //     let mut map = Map::new();

    //     for key in &keys {
    //         map = map.insert(key, key);
    //     }

    //     bencher.iter(|| {
    //         for key in &keys {
    //             map.get(&key);
    //         }
    //     });
    // }
}
