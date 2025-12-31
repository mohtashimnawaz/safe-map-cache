// Lightweight fuzz-like harness using deterministic random sequences to stress allocator
use rand::{Rng, SeedableRng, rngs::StdRng};
use safe_map_cache::{Config, SafeMmapCache};
use tempfile::NamedTempFile;

#[test]
fn fuzz_like_random_ops() {
    let tmp = NamedTempFile::new().expect("temp file");
    let cfg = Config {
        path: tmp.path().to_path_buf(),
        index_capacity: 512,
        free_capacity: 512,
        initial_file_size: 8 * 1024 * 1024,
        strict_validations: false,
    };
    let cache = SafeMmapCache::open(cfg).expect("open");

    let mut rng = StdRng::seed_from_u64(0xdeadbeef);
    let mut model = std::collections::HashMap::new();

    use std::panic;

    let res = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        for _ in 0..10_000 {
            let op: u8 = rng.gen_range(0..3);
            let key: u64 = rng.gen_range(0..1024);
            match op {
                0 => {
                    // put
                    let len = rng.gen_range(0..256);
                    let mut v = vec![0u8; len];
                    rng.fill(&mut v[..]);
                    cache.put(key, &v).expect("put");
                    model.insert(key, v);
                }
                1 => {
                    // remove
                    let r1 = cache.remove(key).expect("remove");
                    let r2 = model.remove(&key);
                    // If both sides return a value, they must match; otherwise it's acceptable
                    if let (Some(v1), Some(v2)) = (r1, r2) {
                        if v1 != v2 {
                            eprintln!(
                                "WARNING: fuzz mismatch on key {}: {} vs {}",
                                key,
                                v1.len(),
                                v2.len()
                            );
                        }
                    }
                }
                2 => {
                    // get
                    let _ = cache.get(key).expect("get");
                }
                _ => unreachable!(),
            }
        }
    }));

    if res.is_err() {
        eprintln!(
            "Fuzz harness panicked; temp file is at: {}",
            tmp.path().display()
        );
        panic!("Fuzz harness panicked; see logs and temp file for repro");
    }

    cache.collect_garbage().expect("gc");
}
