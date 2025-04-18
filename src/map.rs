use crate::hamt::{ClonedHamtIterator, Hamt, HamtIterator};
use std::{borrow::Borrow, hash::Hash, ops::Index, sync::Arc};

/// Map data structure of HAMT.
///
/// Note that every method does not modify the original map but creates a new
/// one if necessary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Map<K, V> {
    size: usize,
    hamt: Arc<Hamt<K, V>>,
}

impl<K: Hash + Eq, V> Map<K, V> {
    /// Creates a new map.
    pub fn new() -> Self {
        Self {
            size: 0,
            hamt: Hamt::new().into(),
        }
    }

    /// Finds a key and its corresponding value in a map.
    pub fn get<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        self.hamt.get(key)
    }

    /// Checks if a key is contained in a map.
    pub fn contains_key<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
    {
        self.get(key).is_some()
    }
}

impl<K: Clone + Hash + Eq, V: Clone> Map<K, V> {
    /// Inserts a key-value pair into a map.
    #[must_use]
    pub fn insert(&self, key: K, value: V) -> Self {
        let (hamt, ok) = self.hamt.insert(key, value);

        Self {
            size: self.size + (ok as usize),
            hamt: hamt.into(),
        }
    }

    /// Removes a key from a map if any.
    #[must_use]
    pub fn remove<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Self
    where
        K: Borrow<Q>,
    {
        if let Some(hamt) = self.hamt.remove(key) {
            Self {
                size: self.size - 1,
                hamt: hamt.into(),
            }
        } else {
            self.clone()
        }
    }

    /// Extends a map with an iterator of key-value pairs.
    #[must_use]
    pub fn extend(&self, iterator: impl IntoIterator<Item = (K, V)>) -> Self {
        let mut map = self.clone();

        for (key, value) in iterator {
            map = map.insert(key, value);
        }

        map
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
    #[must_use]
    pub fn first_rest(&self) -> Option<(&K, &V, Self)> {
        self.hamt.first_rest().map(|(key, value, hamt)| {
            (
                key,
                value,
                Self {
                    size: self.size - 1,
                    hamt: hamt.into(),
                },
            )
        })
    }
}

impl<K: Clone + Hash + Eq, V: Clone> Default for Map<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Q: Hash + Eq + ?Sized, K: Hash + Eq, V> Index<&Q> for Map<K, V>
where
    K: Borrow<Q>,
{
    type Output = V;

    fn index(&self, key: &Q) -> &Self::Output {
        self.get(key).expect("existent key")
    }
}

impl<K: Clone + Hash + Eq, V: Clone> FromIterator<(K, V)> for Map<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iterator: T) -> Self {
        let mut size = 0;
        let mut hamt = Hamt::new();

        for (key, value) in iterator {
            size += hamt.insert_mut(key, value) as usize;
        }

        Self {
            size,
            hamt: hamt.into(),
        }
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

pub struct ClonedMapIterator<K: Clone, V: Clone>(ClonedHamtIterator<K, V>);

impl<K: Clone, V: Clone> Iterator for ClonedMapIterator<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl<K: Clone, V: Clone> IntoIterator for Map<K, V> {
    type IntoIter = ClonedMapIterator<K, V>;
    type Item = (K, V);

    fn into_iter(self) -> Self::IntoIter {
        ClonedMapIterator(self.hamt.as_ref().clone().into_iter())
    }
}

#[cfg(test)]
mod test {
    use super::Map;
    use rand::{random, rng, seq::SliceRandom};
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
        let mut map: Map<u64, u64> = Map::new();

        for index in 0..NUM_ITERATIONS {
            let key = random();
            map = map.insert(key, key);
            assert_eq!(map.len(), index + 1);
        }
    }

    #[test]
    fn remove() {
        let map = Map::new();

        assert_eq!(map.insert(0, 0).remove(&0), map);
        assert_eq!(map.insert(0, 0).remove(&1), map.insert(0, 0));
        assert_eq!(map.insert(0, 0).insert(1, 0).remove(&0), map.insert(1, 0));
        assert_eq!(map.insert(0, 0).insert(1, 0).remove(&1), map.insert(0, 0));
        assert_eq!(
            map.insert(0, 0).insert(1, 0).remove(&2),
            map.insert(0, 0).insert(1, 0)
        );
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
                map = map.remove(&key);

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
                inserted_keys.shuffle(&mut rng());
                deleted_keys.shuffle(&mut rng());

                for key in &inserted_keys {
                    *map = map.insert(*key, *key);
                }

                for key in &deleted_keys {
                    *map = map.remove(key);
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

    #[test]
    fn extend() {
        assert_eq!(
            Map::<usize, usize>::new().insert(0, 0),
            Map::new().extend([(0, 0)])
        );
    }

    #[test]
    fn index() {
        assert_eq!(
            Map::<String, usize>::new().insert("foo".to_string(), 42)["foo"],
            42,
        );
    }

    mod into_iterator {
        use super::*;

        #[test]
        fn iterate() {
            for _ in Map::<usize, usize>::new() {}
        }

        #[test]
        fn iterate_borrowed() {
            for _ in &Map::<usize, usize>::new() {}
        }
    }

    mod from_iterator {
        use super::*;

        #[test]
        fn collect_empty() {
            assert_eq!(Map::<usize, usize>::new(), [].into_iter().collect());
        }

        #[test]
        fn collect_one_element() {
            assert_eq!(
                Map::<usize, usize>::new().insert(0, 0),
                [(0, 0)].into_iter().collect()
            );
        }

        #[test]
        fn collect_two_elements() {
            assert_eq!(
                Map::<usize, usize>::new().insert(0, 0).insert(1, 1),
                [(0, 0), (1, 1)].into_iter().collect()
            );
        }

        #[test]
        fn collect_with_reversed_order() {
            assert_eq!(
                Map::<usize, usize>::new().insert(0, 0).insert(1, 1),
                [(1, 1), (0, 0)].into_iter().collect()
            );
        }

        #[test]
        fn collect_duplicate_keys() {
            assert_eq!(
                Map::<usize, usize>::new().insert(0, 0),
                [(0, 0), (0, 0)].into_iter().collect()
            );
        }

        #[test]
        fn collect_many_elements() {
            let keys = (0..100).collect::<Vec<_>>();
            let mut map = Map::<usize, usize>::new();

            for &key in &keys {
                map = map.insert(key, key);
            }

            assert_eq!(map, keys.into_iter().map(|key| (key, key)).collect());
        }
    }
}
