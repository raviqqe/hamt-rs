use criterion::{criterion_group, criterion_main, Bencher, Criterion};
use std::collections::HashMap;

fn generate_keys() -> Vec<usize> {
    (0..10000).collect()
}

fn hash_map_get(bencher: &mut Bencher) {
    let keys = generate_keys();
    let mut map = HashMap::new();

    for key in &keys {
        map.insert(key, key);
    }

    bencher.iter(|| {
        for key in &keys {
            map.get(&key);
        }
    });
}

fn hash_map_insert(bencher: &mut Bencher) {
    let keys = generate_keys();

    bencher.iter(|| {
        let mut map = HashMap::new();

        for key in &keys {
            map.insert(key, key);
        }
    });
}

fn hash_map_insert_functional(bencher: &mut Bencher) {
    let keys = generate_keys();

    bencher.iter(|| {
        let mut map = HashMap::new();

        for key in &keys {
            map = map.clone();

            map.insert(key, key);
        }
    });
}

fn benchmark(criterion: &mut Criterion) {
    criterion.bench_function("hash map get", hash_map_get);
    criterion.bench_function("hash map insert", hash_map_insert);
    criterion.bench_function("hash map insert (functional)", hash_map_insert_functional);
}

criterion_group!(benchmark_group, benchmark);
criterion_main!(benchmark_group);
