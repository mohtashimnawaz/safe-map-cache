#![no_main]
use libfuzzer_sys::fuzz_target;
use safe_map_cache::{Config, SafeMmapCache};
use tempfile::NamedTempFile;

fuzz_target!(|data: &[u8]| {
    // Lightweight fuzz target: drive put/remove/get from byte stream
    let tmp = NamedTempFile::new().unwrap();
    let cfg = Config {
        path: tmp.path().to_path_buf(),
        index_capacity: 512,
        free_capacity: 512,
        initial_file_size: 8 * 1024 * 1024,
        strict_validations: false,
    };
    let cache = match SafeMmapCache::open(cfg) {
        Ok(c) => c,
        Err(_) => return,
    };

    let mut i = 0usize;
    while i + 4 <= data.len() {
        let op = data[i] % 3; i += 1;
        let key = ((data[i] as u64) | ((data[i+1] as u64) << 8)) % 1024; i += 2;
        let len = (data[i] as usize) % 256; i += 1;
        if op == 0 {
            let end = usize::min(i + len, data.len());
            let val = data[i..end].to_vec();
            let _ = cache.put(key, &val);
            i = end;
        } else if op == 1 {
            let _ = cache.remove(key);
        } else {
            let _ = cache.get(key);
        }
    }
});
