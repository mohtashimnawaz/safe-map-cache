use proptest::prelude::*;
use safe_map_cache::{Config, SafeMmapCache};
use tempfile::NamedTempFile;

#[derive(Debug, Clone)]
enum Op {
    Put(u64, Vec<u8>),
    Remove(u64),
    Get(u64),
}

proptest! {
    #[test]
    fn proptest_invariants(ops in prop::collection::vec(
        prop_oneof![
            (0u64..1024u64, prop::collection::vec(any::<u8>(), 0..256)).prop_map(|(k,v)| Op::Put(k,v)),
            (0u64..1024u64).prop_map(|k| Op::Remove(k)),
            (0u64..1024u64).prop_map(|k| Op::Get(k)),
        ], 1..200)) {

        let tmp = NamedTempFile::new().expect("temp file");
        let cfg = Config {
            path: tmp.path().to_path_buf(),
            index_capacity: 256,
            free_capacity: 256,
            initial_file_size: 4 * 1024 * 1024,
            strict_validations: true,
        };
        let cache = SafeMmapCache::open(cfg).expect("open");

        for (i, op) in ops.into_iter().enumerate() {
            match op {
                Op::Put(k, v) => { let _ = cache.put(k, &v); }
                Op::Remove(k) => { let _ = cache.remove(k); }
                Op::Get(k) => { let _ = cache.get(k); }
            }
            if i % 10 == 0 {
                cache.check_invariants().expect("invariants");
            }
        }

        // final checks
        cache.check_invariants().expect("final invariants");
        cache.collect_garbage().expect("gc");
        cache.check_invariants().expect("post-gc invariants");
    }
}
