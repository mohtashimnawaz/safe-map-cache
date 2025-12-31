use std::{io, path::PathBuf, sync::Arc};

use lru::LruCache;
use parking_lot::RwLock;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CacheError {
    #[error("io: {0}")]
    Io(#[from] io::Error),
    #[error("not found")]
    NotFound,
    #[error("insufficient space")]
    InsufficientSpace,
}

#[derive(Debug, Clone)]
pub struct Config {
    pub path: PathBuf,
    /// size of each fixed slot (bytes)
    pub slot_size: usize,
    /// number of slots in the file
    pub capacity: usize,
}

struct Inner {
    // mmap backing store
    mmap: crate::mmap::MmapFile,
    // LRU index: key -> slot_index
    lru: LruCache<u64, usize>,
    // free slot stack
    free_slots: Vec<usize>,
    slot_size: usize,
}

/// A safe, concurrent, memory-mapped LRU cache.
///
/// This implementation uses a fixed-size slot allocator (simple, safe)
/// where each slot stores a u64 length header followed by the payload.
pub struct SafeMmapCache {
    inner: Arc<RwLock<Inner>>,
}

impl SafeMmapCache {
    /// Open or create a cache file according to `cfg`.
    pub fn open(cfg: Config) -> Result<Self, CacheError> {
        let file_size = cfg.slot_size.checked_mul(cfg.capacity).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "slot_size * capacity overflow")
        })?;

        if cfg.capacity == 0 {
            return Err(CacheError::Io(io::Error::new(
                io::ErrorKind::InvalidInput,
                "capacity must be > 0",
            )));
        }

        let mmap = crate::mmap::MmapFile::open(cfg.path, file_size)?;

        let free_slots = (0..cfg.capacity).rev().collect();

        let cap_nz = std::num::NonZeroUsize::new(cfg.capacity).unwrap();

        let inner = Inner {
            mmap,
            lru: LruCache::new(cap_nz),
            free_slots,
            slot_size: cfg.slot_size,
        };

        Ok(SafeMmapCache {
            inner: Arc::new(RwLock::new(inner)),
        })
    }

    /// Get a value by key.
    pub fn get(&self, key: u64) -> Result<Option<Vec<u8>>, CacheError> {
        let mut guard = self.inner.write();
        if let Some(slot_idx) = guard.lru.get(&key).cloned() {
            // slot base offset
            let slot_size = guard.slot_size;
            let base = slot_idx * slot_size;
            let buf = guard.mmap.as_mut_slice();
            if base + 8 > buf.len() {
                return Err(CacheError::Io(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "corrupt slot header",
                )));
            }
            let len = u64::from_le_bytes(buf[base..base + 8].try_into().unwrap()) as usize;
            if len == 0 {
                return Ok(None);
            }
            if base + 8 + len > buf.len() || len > slot_size - 8 {
                return Err(CacheError::Io(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "corrupt slot length",
                )));
            }
            let data = buf[base + 8..base + 8 + len].to_vec();
            // `get` already promoted recency inside LruCache
            return Ok(Some(data));
        }
        Ok(None)
    }

    /// Put a key/value pair into the cache.
    pub fn put(&self, key: u64, value: &[u8]) -> Result<(), CacheError> {
        let mut guard = self.inner.write();
        if value.len() > guard.slot_size - 8 {
            return Err(CacheError::InsufficientSpace);
        }

        // If already present, overwrite the slot
        if let Some(slot_idx) = guard.lru.get(&key).cloned() {
            let base = slot_idx * guard.slot_size;
            let buf = guard.mmap.as_mut_slice();
            buf[base..base + 8].copy_from_slice(&(value.len() as u64).to_le_bytes());
            buf[base + 8..base + 8 + value.len()].copy_from_slice(value);
            guard.lru.put(key, slot_idx); // refresh recency
            return Ok(());
        }

        // allocate a slot
        let slot_idx = if let Some(s) = guard.free_slots.pop() {
            s
        } else {
            // evict least recently used
            if let Some((_old_key, old_slot)) = guard.lru.pop_lru() {
                // reuse slot
                old_slot
            } else {
                return Err(CacheError::InsufficientSpace);
            }
        };

        // write to slot
        let base = slot_idx * guard.slot_size;
        let buf = guard.mmap.as_mut_slice();
        buf[base..base + 8].copy_from_slice(&(value.len() as u64).to_le_bytes());
        buf[base + 8..base + 8 + value.len()].copy_from_slice(value);

        guard.lru.put(key, slot_idx);
        Ok(())
    }

    /// Remove a key from the cache, returning its value if present.
    pub fn remove(&self, key: u64) -> Result<Option<Vec<u8>>, CacheError> {
        let mut guard = self.inner.write();
        if let Some(slot_idx) = guard.lru.pop(&key) {
            let base = slot_idx * guard.slot_size;
            let buf = guard.mmap.as_mut_slice();
            let len = u64::from_le_bytes(buf[base..base + 8].try_into().unwrap()) as usize;
            let data = if len == 0 {
                None
            } else {
                Some(buf[base + 8..base + 8 + len].to_vec())
            };
            // mark slot free
            guard.free_slots.push(slot_idx);
            return Ok(data);
        }
        Ok(None)
    }

    /// Flush mmap to disk
    pub fn flush(&self) -> Result<(), CacheError> {
        let guard = self.inner.read();
        guard.mmap.flush()?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::NamedTempFile;

    #[test]
    fn open_creates_and_maps() {
        let tmp = NamedTempFile::new().expect("temp file");
        let cfg = Config {
            path: tmp.path().to_path_buf(),
            slot_size: 256,
            capacity: 16,
        };

        let c = SafeMmapCache::open(cfg).expect("open cache");
        c.flush().expect("flush");
    }

    #[test]
    fn put_get_remove_and_eviction() {
        let tmp = NamedTempFile::new().expect("temp file");
        let cfg = Config {
            path: tmp.path().to_path_buf(),
            slot_size: 64,
            capacity: 2,
        };

        let cache = SafeMmapCache::open(cfg).expect("open");

        cache.put(1, b"one").expect("put1");
        cache.put(2, b"two").expect("put2");

        assert_eq!(cache.get(1).unwrap(), Some(b"one".to_vec()));
        assert_eq!(cache.get(2).unwrap(), Some(b"two".to_vec()));

        // access key 1 to make key 2 the LRU
        cache.get(1).unwrap();

        // inserting a new key should evict key 2
        cache.put(3, b"three").expect("put3");

        assert_eq!(cache.get(2).unwrap(), None);
        assert_eq!(cache.get(1).unwrap(), Some(b"one".to_vec()));
        assert_eq!(cache.get(3).unwrap(), Some(b"three".to_vec()));

        // remove 1
        let r = cache.remove(1).expect("remove");
        assert_eq!(r, Some(b"one".to_vec()));
        assert_eq!(cache.get(1).unwrap(), None);
    }
}
