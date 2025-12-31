use std::{io, path::PathBuf, sync::Arc};

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
    /// initial file size in bytes
    pub file_size: usize,
}

struct Inner {
    // mmap backing store
    mmap: crate::mmap::MmapFile,
    // future: index, free-list, LRU structures
}

/// A safe, concurrent, memory-mapped LRU cache.
///
/// This is an initial skeleton; the implementation will be filled in incrementally.
pub struct SafeMmapCache {
    inner: Arc<RwLock<Inner>>,
}

impl SafeMmapCache {
    /// Open or create a cache file according to `cfg`.
    pub fn open(cfg: Config) -> Result<Self, CacheError> {
        let mmap = crate::mmap::MmapFile::open(cfg.path, cfg.file_size)?;

        let inner = Inner { mmap };

        Ok(SafeMmapCache {
            inner: Arc::new(RwLock::new(inner)),
        })
    }

    /// Get a value by key. Currently a stub that always returns `Ok(None)`.
    pub fn get(&self, _key: u64) -> Result<Option<Vec<u8>>, CacheError> {
        // TODO: implement lookup in in-memory index and read bytes from mmap
        Ok(None)
    }

    /// Put a key/value pair into the cache. Currently a stub.
    pub fn put(&self, _key: u64, _value: &[u8]) -> Result<(), CacheError> {
        // TODO: implement allocation in the mmap region, LRU updates, and eviction
        Ok(())
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
            file_size: 1024 * 16,
        };

        let c = SafeMmapCache::open(cfg).expect("open cache");
        c.flush().expect("flush");
    }
}
