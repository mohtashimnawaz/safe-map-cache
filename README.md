# safe-mmap-cache

A small example crate implementing a memory-mapped, fixed-slot, LRU-backed cache.

Features:
- Backed by a memory-mapped file (`memmap2`) for fast IO and persistence
- In-memory LRU tracking (via `lru`) to evict cold entries
- Simple, safe API: `SafeMmapCache::open`, `get`, `put`, `remove`, `flush`
- Thread-safe (uses `parking_lot::RwLock`)

Example
-------

```rust
use safe_map_cache::{Config, SafeMmapCache};
use tempfile::NamedTempFile;

let tmp = NamedTempFile::new().unwrap();
let cfg = Config { path: tmp.path().to_path_buf(), slot_size: 256, capacity: 128 };
let cache = SafeMmapCache::open(cfg).unwrap();

cache.put(42, b"hello").unwrap();
assert_eq!(cache.get(42).unwrap(), Some(b"hello".to_vec()));

cache.remove(42).unwrap();
```

Notes & limitations
-------------------
- Current implementation uses fixed-size slots. This keeps the allocator simple and avoids fragmentation, but limits maximum value size to `slot_size - 8` bytes.
- Index is in-memory only. The on-disk format stores raw slot blobs; the in-memory index is rebuilt on fresh open (future work: persistent index).
- This crate is an educational example and not yet optimized for production workloads.

Safety
------
- Mmap creation uses `memmap2`'s `MmapOptions::map_mut`, which is `unsafe` because it creates a mapping of a file into memory. This crate keeps the backing `File` alive for the lifetime of the mapping and always unmaps (drops) the mapping before changing the file size (see `src/mmap.rs`).
- Invariants to preserve: do not truncate or replace the underlying file while a mapping exists; call `resize` to safely change mapping size; avoid mutating the file backing the mapping from other processes without coordinating.
- All uses of `unsafe` are confined to `src/mmap.rs` and explained with a `SAFETY` doc comment.

Contributing
------------
PRs and issues welcome. Consider adding variable-size allocation, persistent index, benchmarks and more thorough tests.
