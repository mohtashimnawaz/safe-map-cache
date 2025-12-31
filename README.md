# safe-map-cache

A safe, concurrent memory-mapped LRU cache with a persisted on-disk index and optional strict validation mode for debugging and tests.

Features
- Memory-mapped backing (fast reads)
- Variable-size values with a persistent index and free-list
- LRU eviction and optional compaction (GC)
- Property tests and cargo-fuzz integration for stress testing

Quick start

```rust
use safe_map_cache::{Config, SafeMmapCache};
use tempfile::NamedTempFile;

let tmp = NamedTempFile::new().unwrap();
let cfg = Config {
    path: tmp.path().to_path_buf(),
    index_capacity: 512,
    free_capacity: 512,
    initial_file_size: 8 * 1024 * 1024,
    strict_validations: false,
};
let cache = SafeMmapCache::open(cfg).unwrap();
cache.put(1, b"one").unwrap();
assert_eq!(cache.get(1).unwrap(), Some(b"one".to_vec()));
```

Fuzzing & testing
- `tests/fuzz_like.rs` deterministic fuzz-like harness used in CI
- `fuzz/` folder contains a `cargo-fuzz` target (`fuzz_ops`) for deeper fuzzing

License & Contributing
- Licensed under MIT (see `LICENSE`)
- PRs, issues and fuzz cases welcome.
