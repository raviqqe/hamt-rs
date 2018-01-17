use std::sync::Arc;

pub struct Hamt<K>(Arc<Inner<K>>);

struct Inner<K> {
    bitmap: i32,
    entries: [Option<K>; 32],
}

impl<K> Hamt<K> {
    fn new(k: K) -> Self {
        let mut es: [Option<K>; 32] = Default::default();

        es[0] = Some(k);

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
