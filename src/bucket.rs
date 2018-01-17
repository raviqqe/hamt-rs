use std::sync::Arc;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Bucket<K: Ord>(Arc<Vec<K>>);

impl<K: Ord> Bucket<K> {
    fn new(k: K) -> Self {
        Bucket(Arc::new(vec![k]))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn bucket_new() {
        Bucket::new(42);
    }
}
