use proptest::prelude::*;
use safe_map_cache::{Config, SafeMmapCache};
use std::collections::HashMap;
use tempfile::NamedTempFile;

#[derive(Debug, Clone)]
enum Op {
    Put(u64, Vec<u8>),
    Remove(u64),
    Get(u64),
}

fn arb_op() -> impl Strategy<Value = Op> {
    prop_oneof![
        (0u64..50u64, prop::collection::vec(any::<u8>(), 0..64)).prop_map(|(k, v)| Op::Put(k, v)),
        (0u64..50u64).prop_map(Op::Remove),
        (0u64..50u64).prop_map(Op::Get),
    ]
}

proptest! {
    #[test]
    fn proptest_sequence(ops in prop::collection::vec(arb_op(), 1..200)) {
        let tmp = NamedTempFile::new().expect("temp file");
        let cfg = Config { path: tmp.path().to_path_buf(), index_capacity: 256, free_capacity: 256, initial_file_size: 4*1024*1024, strict_validations: false };
        let cache = SafeMmapCache::open(cfg).expect("open");

        let mut model = HashMap::new();

        for op in ops {
            match op {
                Op::Put(k, v) => {
                    cache.put(k, &v).expect("put");
                    model.insert(k, v);
                }
                Op::Remove(k) => {
                    let r1 = cache.remove(k).expect("remove");
                    let r2 = model.remove(&k);
                    if r2.is_some() {
                        assert_eq!(r1, r2);
                    } else {
                        assert_eq!(r1, None);
                    }
                }
                Op::Get(k) => {
                    let r1 = cache.get(k).expect("get");
                    let r2 = model.get(&k).cloned();
                    assert_eq!(r1, r2);
                }
            }
        }

        // run GC and ensure all live entries still match
        cache.collect_garbage().expect("gc");
        for (k, v) in model {
            assert_eq!(cache.get(k).unwrap(), Some(v));
        }
    }
}
