#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KeyValue<K, V> {
    key: K,
    value: V,
}

impl<K, V> KeyValue<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Self { key, value }
    }
}

impl<K, V> KeyValue<K, V> {
    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn value(&self) -> &V {
        &self.value
    }
}
