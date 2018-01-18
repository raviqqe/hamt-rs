use std::sync::Arc;

use bucket::Bucket;

use self::Entry::*;

enum Entry<K> {
    Empty,
    Key(K),
    Hamt(Hamt<K>),
    Bucket(Bucket<K>),
}

impl<K> Default for Entry<K> {
    fn default() -> Self {
        Empty
    }
}

pub struct Hamt<K>(Arc<Inner<K>>);

struct Inner<K> {
    bitmap: i32,
    entries: [Entry<K>; 32],
}

impl<K> Hamt<K> {
    fn new(k: K) -> Self {
        let mut es: [Entry<K>; 32] = Default::default();

        es[0] = Key(k);

        Hamt(Arc::new(Inner {
            bitmap: 0,
            entries: es,
        }))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        Hamt::new(42);
    }
}
