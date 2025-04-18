use crate::hamt::{ClonedHamtIterator, Hamt, HamtIterator};
use std::{borrow::Borrow, hash::Hash, sync::Arc};

/// Set data structure of HAMT.
///
/// Note that every method does not modify the original set but creates a new
/// one if necessary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Set<T> {
    size: usize,
    hamt: Arc<Hamt<T, ()>>,
}

impl<T: Hash + Eq> Set<T> {
    /// Creates a new set.
    pub fn new() -> Self {
        Self {
            size: 0,
            hamt: Hamt::new().into(),
        }
    }

    /// Checks if a value is contained in a set.
    pub fn contains<Q: Hash + Eq + ?Sized>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
    {
        self.hamt.get(value).is_some()
    }
}

impl<T: Clone + Hash + Eq> Set<T> {
    /// Inserts a value into a set.
    #[must_use]
    pub fn insert(&self, value: T) -> Self {
        let (hamt, ok) = self.hamt.insert(value, ());

        Self {
            size: self.size + (ok as usize),
            hamt: hamt.into(),
        }
    }

    /// Removes a value from a set if any.
    #[must_use]
    pub fn remove<Q: Hash + Eq + ?Sized>(&self, value: &Q) -> Self
    where
        T: Borrow<Q>,
    {
        if let Some(hamt) = self.hamt.remove(value) {
            Self {
                size: self.size - 1,
                hamt: hamt.into(),
            }
        } else {
            self.clone()
        }
    }

    /// Extends a set with an iterator of values.
    #[must_use]
    pub fn extend(&self, iterator: impl IntoIterator<Item = T>) -> Self {
        let mut set = self.clone();

        for value in iterator {
            set = set.insert(value);
        }

        set
    }

    /// Returns a size of a set.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns true if a set is empty.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Returns values in a set
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.into_iter()
    }

    /// Removes the first element in a set and returns a new set containing the
    /// rest of elements.
    #[must_use]
    pub fn first_rest(&self) -> Option<(&T, Self)> {
        self.hamt.first_rest().map(|(key, _, hamt)| {
            (
                key,
                Self {
                    size: self.size - 1,
                    hamt: hamt.into(),
                },
            )
        })
    }

    /// Calculate intersection of two sets.
    pub fn intersection(&self, other: &Self) -> Self {
        let mut size = 0;
        let mut hamt = Hamt::new();

        for element in self {
            if other.contains(element) && hamt.insert_mut(element.clone(), ()) {
                size += 1;
            }
        }

        Self {
            hamt: hamt.into(),
            size,
        }
    }

    /// Calculate difference of two sets.
    pub fn difference(&self, other: &Self) -> Self {
        let mut size = 0;
        let mut hamt = Hamt::new();

        for element in self {
            if !other.contains(element) && hamt.insert_mut(element.clone(), ()) {
                size += 1;
            }
        }

        Self {
            hamt: hamt.into(),
            size,
        }
    }
}

impl<T: Clone + Hash + Eq> Default for Set<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Hash + Eq> FromIterator<T> for Set<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iterator: I) -> Self {
        let mut size = 0;
        let mut hamt = Hamt::new();

        for value in iterator {
            size += hamt.insert_mut(value, ()) as usize;
        }

        Self {
            size,
            hamt: hamt.into(),
        }
    }
}

pub struct SetIterator<'a, T: 'a>(HamtIterator<'a, T, ()>);

impl<'a, T> Iterator for SetIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(key, _)| key)
    }
}

impl<'a, T> IntoIterator for &'a Set<T> {
    type IntoIter = SetIterator<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter {
        SetIterator(self.hamt.into_iter())
    }
}

pub struct ClonedSetIterator<T: Clone>(ClonedHamtIterator<T, ()>);

impl<T: Clone> Iterator for ClonedSetIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(key, _)| key)
    }
}

impl<T: Clone> IntoIterator for Set<T> {
    type IntoIter = ClonedSetIterator<T>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        ClonedSetIterator(self.hamt.as_ref().clone().into_iter())
    }
}

#[cfg(test)]
mod test {
    use super::Set;
    use rand::{random, seq::SliceRandom, thread_rng};
    use std::thread::spawn;

    const ITERATION_COUNT: usize = 1 << 12;

    #[test]
    fn new() {
        Set::<u8>::new();
    }

    #[test]
    fn insert() {
        let set = Set::new();

        assert_eq!(set.len(), 0);
        assert_eq!(set.insert(0).len(), 1);
        assert_eq!(set.insert(0).insert(0).len(), 1);
        assert_eq!(set.insert(0).insert(1).len(), 2);
    }

    #[test]
    fn insert_many_in_order() {
        let mut set = Set::new();

        for index in 0..ITERATION_COUNT {
            set = set.insert(index);
            assert_eq!(set.len(), index + 1);
        }
    }

    #[test]
    fn insert_many_at_random() {
        let mut set: Set<usize> = Set::new();

        for index in 0..ITERATION_COUNT {
            let value = random();
            set = set.insert(value);
            assert_eq!(set.len(), index + 1);
        }
    }

    #[test]
    fn remove() {
        let set = Set::new();

        assert_eq!(set.insert(0).remove(&0), set);
        assert_eq!(set.insert(0).remove(&1), set.insert(0));
        assert_eq!(set.insert(0).insert(1).remove(&0), set.insert(1));
        assert_eq!(set.insert(0).insert(1).remove(&1), set.insert(0));
        assert_eq!(set.insert(0).insert(1).remove(&2), set.insert(0).insert(1));
    }

    #[test]
    fn insert_remove_many() {
        let mut set = Set::<i16>::new();

        for _ in 0..ITERATION_COUNT {
            let value = random();
            let size = set.len();
            let found = set.contains(&value);

            if random() {
                set = set.insert(value);

                assert_eq!(set.len(), if found { size } else { size + 1 });
                assert!(set.contains(&value));
            } else {
                set = set.remove(&value);

                assert_eq!(set.len(), if found { size - 1 } else { size });
                assert!(!set.contains(&value));
            }
        }
    }

    #[test]
    fn contains() {
        let set = Set::new();

        assert!(set.insert(0).contains(&0));
        assert!(!set.insert(0).contains(&1));
        assert!(!set.insert(1).contains(&0));
        assert!(set.insert(1).contains(&1));
        assert!(set.insert(0).insert(1).contains(&0));
        assert!(set.insert(0).insert(1).contains(&1));
        assert!(!set.insert(0).insert(1).contains(&2));
    }

    #[test]
    fn contains_borrowed() {
        assert!(Set::<String>::new()
            .insert("foo".to_string())
            .contains("foo"));
    }

    #[test]
    fn first_rest() {
        let mut set: Set<i16> = Set::new();

        for _ in 0..ITERATION_COUNT {
            set = set.insert(random());
        }

        for _ in 0..set.len() {
            let (value, rest) = set.first_rest().unwrap();

            assert_eq!(rest.len(), set.len() - 1);
            assert!(!rest.contains(value));

            set = rest;
        }

        assert_eq!(set, Set::new());
    }

    #[test]
    fn intersection() {
        assert_eq!(
            Set::new().insert(42).intersection(&Set::new().insert(42)),
            Set::new().insert(42)
        );
        assert_eq!(Set::new().insert(42).intersection(&Set::new()), Set::new());
        assert_eq!(
            Set::new()
                .insert(1)
                .insert(2)
                .intersection(&Set::new().insert(1)),
            Set::new().insert(1)
        );
        assert_eq!(
            Set::new()
                .insert(1)
                .insert(2)
                .intersection(&Set::new().insert(2)),
            Set::new().insert(2)
        );
        assert_eq!(
            Set::new()
                .insert(1)
                .insert(2)
                .insert(3)
                .insert(4)
                .intersection(&Set::new().insert(1).insert(3)),
            Set::new().insert(1).insert(3)
        );
    }

    #[test]
    fn difference() {
        assert_eq!(
            Set::new().insert(42).difference(&Set::new().insert(42)),
            Set::new()
        );
        assert_eq!(
            Set::new().insert(42).difference(&Set::new()),
            Set::new().insert(42)
        );
        assert_eq!(
            Set::new()
                .insert(1)
                .insert(2)
                .difference(&Set::new().insert(1)),
            Set::new().insert(2)
        );
        assert_eq!(
            Set::new()
                .insert(1)
                .insert(2)
                .difference(&Set::new().insert(2)),
            Set::new().insert(1)
        );
        assert_eq!(
            Set::new()
                .insert(1)
                .insert(2)
                .insert(3)
                .insert(4)
                .difference(&Set::new().insert(1).insert(3)),
            Set::new().insert(2).insert(4)
        );
    }

    #[test]
    fn equality() {
        for _ in 0..8 {
            let mut sets: [Set<i16>; 2] = [Set::new(), Set::new()];
            let mut inserted_values: Vec<i16> = (0..ITERATION_COUNT).map(|_| random()).collect();
            let mut deleted_values: Vec<i16> = (0..ITERATION_COUNT).map(|_| random()).collect();

            for set in sets.iter_mut() {
                inserted_values.shuffle(&mut thread_rng());
                deleted_values.shuffle(&mut thread_rng());

                for value in &inserted_values {
                    *set = set.insert(*value);
                }

                for value in &deleted_values {
                    *set = set.remove(value);
                }
            }

            assert_eq!(sets[0], sets[1]);
        }
    }

    #[test]
    fn send_and_sync() {
        let set: Set<usize> = Set::new();
        spawn(move || set);

        let set: Set<String> = Set::new();
        spawn(move || set);
    }

    #[test]
    fn extend() {
        assert_eq!(Set::<usize>::new().insert(0), Set::new().extend([0]));
    }

    mod into_iterator {
        use super::*;

        #[test]
        fn iterate() {
            for _ in Set::<usize>::new() {}
        }

        #[test]
        fn iterate_borrowed() {
            for _ in &Set::<usize>::new() {}
        }
    }

    mod from_iterator {
        use super::*;

        #[test]
        fn collect_empty() {
            assert_eq!(Set::<usize>::new(), [].into_iter().collect());
        }

        #[test]
        fn collect_one_element() {
            assert_eq!(Set::<usize>::new().insert(0), [0].into_iter().collect());
        }

        #[test]
        fn collect_two_elements() {
            assert_eq!(
                Set::<usize>::new().insert(0).insert(1),
                [0, 1].into_iter().collect()
            );
        }

        #[test]
        fn collect_with_reversed_order() {
            assert_eq!(
                Set::<usize>::new().insert(0).insert(1),
                [1, 0].into_iter().collect()
            );
        }

        #[test]
        fn collect_duplicate_values() {
            assert_eq!(Set::<usize>::new().insert(0), [0, 0].into_iter().collect());
        }

        #[test]
        fn collect_many_elements() {
            let values = (0..100).collect::<Vec<_>>();
            let mut set = Set::<usize>::new();

            for &value in &values {
                set = set.insert(value);
            }

            assert_eq!(set, values.into_iter().collect());
        }
    }
}
