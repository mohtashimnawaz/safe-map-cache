use std::{io, path::PathBuf, sync::Arc};

use lru::LruCache;
use parking_lot::RwLock;
use thiserror::Error;

const HEADER_MAGIC: &[u8; 8] = b"SMAPCACH";
const HEADER_SIZE: usize = 16; // magic (8) + version (4) + index_capacity (4)
const RECORD_SIZE: usize = 32; // key(8) offset(8) len(8) flags(8)
const FREE_ENTRY_SIZE: usize = 16; // offset(8) len(8)

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
    /// number of index entries
    pub index_capacity: usize,
    /// number of free-list entries to persist
    pub free_capacity: usize,
    /// initial file size in bytes
    pub initial_file_size: usize,
}

#[derive(Clone, Copy, Debug)]
struct IndexRecord {
    key: u64,
    offset: u64,
    len: u64,
    flags: u64,
}

impl IndexRecord {
    fn from_bytes(b: &[u8]) -> Self {
        let key = u64::from_le_bytes(b[0..8].try_into().unwrap());
        let offset = u64::from_le_bytes(b[8..16].try_into().unwrap());
        let len = u64::from_le_bytes(b[16..24].try_into().unwrap());
        let flags = u64::from_le_bytes(b[24..32].try_into().unwrap());
        IndexRecord { key, offset, len, flags }
    }

    fn to_bytes(&self, b: &mut [u8]) {
        b[0..8].copy_from_slice(&self.key.to_le_bytes());
        b[8..16].copy_from_slice(&self.offset.to_le_bytes());
        b[16..24].copy_from_slice(&self.len.to_le_bytes());
        b[24..32].copy_from_slice(&self.flags.to_le_bytes());
    }
}

struct Inner {
    mmap: crate::mmap::MmapFile,
    lru: LruCache<u64, usize>, // key -> index_slot
    free_slots: Vec<usize>,
    // free_extents: (offset, len, freelist_slot)
    free_extents: Vec<(usize, usize, usize)>,
    index_capacity: usize,
    free_capacity: usize,
    freelist_start: usize,
    data_start: usize,
    next_data_offset: usize,
}

/// A safe, concurrent, memory-mapped LRU cache with a persisted index.
///
/// This implementation stores an index in the first region of the file that is
/// rebuilt on open. Values are variable-sized blobs appended into the data
/// section; evicted entries free their index slot for reuse (data is not
/// reclaimed yet).
pub struct SafeMmapCache {
    inner: Arc<RwLock<Inner>>,
}

impl SafeMmapCache {
    /// Open or create a cache file according to `cfg`.
    pub fn open(cfg: Config) -> Result<Self, CacheError> {
        let meta_region = HEADER_SIZE + RECORD_SIZE * cfg.index_capacity + FREE_ENTRY_SIZE * cfg.free_capacity;
        let initial = cfg.initial_file_size.max(meta_region + 1024);
        let mmap = crate::mmap::MmapFile::open(cfg.path, initial)?;

        let mut inner = Inner {
            mmap,
            lru: LruCache::new(std::num::NonZeroUsize::new(cfg.index_capacity).unwrap()),
            free_slots: Vec::new(),
            free_extents: Vec::new(),
            index_capacity: cfg.index_capacity,
            free_capacity: cfg.free_capacity,
            freelist_start: HEADER_SIZE + cfg.index_capacity * RECORD_SIZE,
            data_start: HEADER_SIZE + cfg.index_capacity * RECORD_SIZE + cfg.free_capacity * FREE_ENTRY_SIZE,
            next_data_offset: 0,
        };

        // initialize header if needed and read index and free-list
        inner.init_and_load_index()?;

        Ok(SafeMmapCache {
            inner: Arc::new(RwLock::new(inner)),
        })
    }

    /// Get a value by key.
    pub fn get(&self, key: u64) -> Result<Option<Vec<u8>>, CacheError> {
        let mut guard = self.inner.write();
        if let Some(slot) = guard.lru.get(&key).cloned() {
            let rec = guard.read_index_slot(slot)?;
            if rec.flags == 0 {
                return Ok(None);
            }
            let offset = rec.offset as usize;
            let len = rec.len as usize;
            let buf = guard.mmap.as_mut_slice();
            if offset + len > buf.len() {
                return Err(CacheError::Io(io::Error::new(io::ErrorKind::UnexpectedEof, "corrupt data")));
            }
            let data = buf[offset..offset + len].to_vec();
            return Ok(Some(data));
        }
        Ok(None)
    }

    /// Put a key/value pair into the cache.
    pub fn put(&self, key: u64, value: &[u8]) -> Result<(), CacheError> {
        let mut guard = self.inner.write();
        // if exists and fits, overwrite in place
        if let Some(slot) = guard.lru.get(&key).cloned() {
            let rec = guard.read_index_slot(slot)?;
            if rec.flags != 0 && (value.len() as u64) <= rec.len {
                let offset = rec.offset as usize;
                let buf = guard.mmap.as_mut_slice();
                buf[offset..offset + value.len()].copy_from_slice(value);
                // update length if changed
                let mut new_rec = rec;
                new_rec.len = value.len() as u64;
                guard.write_index_slot(slot, new_rec)?;
                guard.lru.put(key, slot);
                return Ok(());
            }
        }

        // find a free index slot
        let slot = if let Some(s) = guard.free_slots.pop() {
            s
        } else if guard.lru.len() < guard.index_capacity {
            // find first empty slot
            let mut s = 0usize;
            loop {
                let rec = guard.read_index_slot(s)?;
                if rec.flags == 0 {
                    break s;
                }
                s += 1;
            }
        } else {
            // evict LRU
            let (_old_key, old_slot) = guard.lru.pop_lru().ok_or(CacheError::InsufficientSpace)?;
            // invalidate old slot
            let mut old = guard.read_index_slot(old_slot)?;
            old.flags = 0;
            guard.write_index_slot(old_slot, old)?;
            old_slot
        };

        // allocate data (try to reuse free extents first)
        let needed = value.len();
        // select a free extent without mutably borrowing the vector
        let chosen = guard
            .free_extents
            .iter()
            .enumerate()
            .find(|(_i, (_off, len, _slot_idx))| *len >= needed)
            .map(|(i, (off, len, slot_idx))| (i, *off, *len, *slot_idx));

        let write_offset = if let Some((i, off, len, slot_idx)) = chosen {
            // adjust or remove the chosen extent
            if len == needed {
                // consume entire free extent slot
                // swap_remove to avoid shifting
                guard.free_extents.swap_remove(i);
                guard.write_free_slot(slot_idx, None)?;
            } else {
                // consume from front; adjust extent
                guard.free_extents[i].0 = off + needed;
                guard.free_extents[i].1 = len - needed;
                guard.write_free_slot(slot_idx, Some((off + needed, len - needed)))?;
            }
            off
        } else {
            // append at end
            let mut offset = guard.next_data_offset;
            if offset + needed > guard.mmap.len() {
                // grow file
                let grow_to = (guard.mmap.len().max(offset + needed) + 4095) & !4095usize;
                guard.mmap.resize(grow_to)?;
            }
            guard.next_data_offset = offset + needed;
            offset
        };

        // write data
        let buf = guard.mmap.as_mut_slice();
        buf[write_offset..write_offset + needed].copy_from_slice(value);

        let new_rec = IndexRecord { key, offset: write_offset as u64, len: needed as u64, flags: 1 };
        guard.write_index_slot(slot, new_rec)?;
        guard.lru.put(key, slot);

        Ok(())
    }

    /// Remove a key from the cache, returning its value if present.
    pub fn remove(&self, key: u64) -> Result<Option<Vec<u8>>, CacheError> {
        let mut guard = self.inner.write();
        if let Some(slot) = guard.lru.pop(&key) {
            let rec = guard.read_index_slot(slot)?;
            let data = if rec.flags == 0 { None } else {
                let buf = guard.mmap.as_mut_slice();
                Some(buf[rec.offset as usize..rec.offset as usize + rec.len as usize].to_vec())
            };
            // invalidate index slot and mark free
            let mut inv = rec;
            inv.flags = 0;
            guard.write_index_slot(slot, inv)?;
            guard.free_slots.push(slot);

            // record freed data extent into persistent free-list (if space)
            for i in 0..guard.free_capacity {
                let start = guard.freelist_start + i * FREE_ENTRY_SIZE;
                let _off = u64::from_le_bytes(guard.mmap.as_slice()[start..start + 8].try_into().unwrap()) as usize;
                let len = u64::from_le_bytes(guard.mmap.as_slice()[start + 8..start + 16].try_into().unwrap()) as usize;
                if len == 0 {
                    guard.write_free_slot(i, Some((rec.offset as usize, rec.len as usize)))?;
                    guard.free_extents.push((rec.offset as usize, rec.len as usize, i));
                    break;
                }
            }
            // if free-list full, we leave the blob for later GC
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

    /// Run garbage collection / compaction to reclaim free space.
    pub fn collect_garbage(&self) -> Result<(), CacheError> {
        let mut guard = self.inner.write();
        guard.collect_garbage()?;
        Ok(())
    }
}

// --- Inner helpers ---
impl Inner {
    fn init_and_load_index(&mut self) -> Result<(), io::Error> {
        // ensure header
        {
            let buf = self.mmap.as_mut_slice();
            if buf.len() < HEADER_SIZE {
                return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "file too small"));
            }
            if &buf[0..8] != HEADER_MAGIC {
                // initialize header
                buf[0..8].copy_from_slice(HEADER_MAGIC);
                buf[8..12].copy_from_slice(&1u32.to_le_bytes()); // version
                buf[12..16].copy_from_slice(&(self.index_capacity as u32).to_le_bytes());
                // zero index region
                let idx_len = self.index_capacity * RECORD_SIZE;
                let start = HEADER_SIZE;
                for b in &mut buf[start..start + idx_len] {
                    *b = 0;
                }
                // `buf` goes out of scope here, releasing the mutable borrow
                self.mmap.flush()?;
            }
        }

        // load index (use immutable borrow for reads)
        self.next_data_offset = self.data_start;
        let buf = self.mmap.as_slice();
        for i in 0..self.index_capacity {
            let start = HEADER_SIZE + i * RECORD_SIZE;
            let rec = IndexRecord::from_bytes(&buf[start..start + RECORD_SIZE]);
            if rec.flags != 0 {
                // valid
                self.lru.put(rec.key, i);
                let end = rec.offset as usize + rec.len as usize;
                if end > self.next_data_offset {
                    self.next_data_offset = end;
                }
            } else {
                self.free_slots.push(i);
            }
        }

        // load free-list entries (immutable borrow)
        for i in 0..self.free_capacity {
            let start = self.freelist_start + i * FREE_ENTRY_SIZE;
            let off = u64::from_le_bytes(buf[start..start + 8].try_into().unwrap()) as usize;
            let len = u64::from_le_bytes(buf[start + 8..start + 16].try_into().unwrap()) as usize;
            if len != 0 {
                self.free_extents.push((off, len, i));
            }
        }

        Ok(())
    }

    fn read_index_slot(&self, slot: usize) -> Result<IndexRecord, io::Error> {
        // read without holding mutable borrow on mmap
        let buf = self.mmap.as_slice();
        let start = HEADER_SIZE + slot * RECORD_SIZE;
        let mut tmp = [0u8; RECORD_SIZE];
        tmp.copy_from_slice(&buf[start..start + RECORD_SIZE]);
        Ok(IndexRecord::from_bytes(&tmp))
    }

    fn write_index_slot(&mut self, slot: usize, rec: IndexRecord) -> Result<(), io::Error> {
        let buf = self.mmap.as_mut_slice();
        let start = HEADER_SIZE + slot * RECORD_SIZE;
        rec.to_bytes(&mut buf[start..start + RECORD_SIZE]);
        // flush index area to persist update
        self.mmap.flush()?;
        Ok(())
    }

    fn write_free_slot(&mut self, free_slot: usize, val: Option<(usize, usize)>) -> Result<(), io::Error> {
        let buf = self.mmap.as_mut_slice();
        let start = self.freelist_start + free_slot * FREE_ENTRY_SIZE;
        match val {
            Some((off, len)) => {
                buf[start..start + 8].copy_from_slice(&(off as u64).to_le_bytes());
                buf[start + 8..start + 16].copy_from_slice(&(len as u64).to_le_bytes());
            }
            None => {
                for b in &mut buf[start..start + FREE_ENTRY_SIZE] {
                    *b = 0;
                }
            }
        }
        self.mmap.flush()?;
        Ok(())
    }

    /// Compact data area by moving live blobs to a contiguous region starting at data_start.
    fn collect_garbage(&mut self) -> Result<(), io::Error> {
        // Build a list of live entries and capture their data into temporaries
        let mut next = self.data_start;
        let buf = self.mmap.as_slice();
        let mut live = Vec::new(); // (index_slot, IndexRecord, data)
        for i in 0..self.index_capacity {
            let start = HEADER_SIZE + i * RECORD_SIZE;
            let rec = IndexRecord::from_bytes(&buf[start..start + RECORD_SIZE]);
            if rec.flags != 0 {
                let old_off = rec.offset as usize;
                let len = rec.len as usize;
                let data = buf[old_off..old_off + len].to_vec();
                live.push((i, rec, data));
            }
        }

        // Now write all live data sequentially into the data area and update index
        {
            let buf_mut = self.mmap.as_mut_slice();
            for (i, mut rec, data) in live.into_iter() {
                let len = data.len();
                let dst = next;
                buf_mut[dst..dst + len].copy_from_slice(&data);
                rec.offset = dst as u64;
                // write updated index bytes
                rec.to_bytes(&mut buf_mut[HEADER_SIZE + i * RECORD_SIZE..HEADER_SIZE + i * RECORD_SIZE + RECORD_SIZE]);
                next += len;
            }

            // zero free-list
            for i in 0..self.free_capacity {
                let start = self.freelist_start + i * FREE_ENTRY_SIZE;
                for b in &mut buf_mut[start..start + FREE_ENTRY_SIZE] {
                    *b = 0;
                }
            }
        }

        self.free_extents.clear();
        self.next_data_offset = next;
        self.mmap.flush()?;
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
            index_capacity: 16,
            free_capacity: 16,
            initial_file_size: 16 * 1024,
        };

        let c = SafeMmapCache::open(cfg).expect("open cache");
        c.flush().expect("flush");
    }

    #[test]
    fn put_get_remove_and_eviction() {
        let tmp = NamedTempFile::new().expect("temp file");
        let cfg = Config {
            path: tmp.path().to_path_buf(),
            index_capacity: 2,
            free_capacity: 4,
            initial_file_size: 4096,
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

    #[test]
    fn concurrent_access() {
        use std::thread;

        let tmp = NamedTempFile::new().expect("temp file");
        let cfg = Config {
            path: tmp.path().to_path_buf(),
            index_capacity: 256,
            free_capacity: 256,
            initial_file_size: 256 * 1024,
        };

        let cache = std::sync::Arc::new(SafeMmapCache::open(cfg).expect("open"));

        let mut handles = Vec::new();

        for t in 0..4u64 {
            let c = cache.clone();
            handles.push(thread::spawn(move || {
                for i in 0..50u64 {
                    let key = t * 1000 + i;
                    let val = format!("v{}_{}", t, i);
                    c.put(key, val.as_bytes()).expect("put");
                    // immediate get should succeed
                    let got = c.get(key).expect("get");
                    assert_eq!(got, Some(val.into_bytes()));
                }
            }));
        }

        for h in handles {
            h.join().expect("thread join");
        }
    }

    #[test]
    fn free_list_and_gc() {
        let tmp = NamedTempFile::new().expect("temp file");
        let cfg = Config {
            path: tmp.path().to_path_buf(),
            index_capacity: 8,
            free_capacity: 8,
            initial_file_size: 16 * 1024,
        };

        let cache = SafeMmapCache::open(cfg).expect("open");

        cache.put(1, b"aaaa").expect("put1");
        cache.put(2, b"bbbbbbbb").expect("put2");
        cache.put(3, b"cccc").expect("put3");

        // remove middle
        cache.remove(2).expect("remove2");

        // put new value that fits into freed slot
        cache.put(4, b"bbbx").expect("put4");
        assert_eq!(cache.get(4).unwrap(), Some(b"bbbx".to_vec()));

        // induce GC and ensure data still correct
        cache.collect_garbage().expect("gc");
        assert_eq!(cache.get(1).unwrap(), Some(b"aaaa".to_vec()));
        assert_eq!(cache.get(3).unwrap(), Some(b"cccc".to_vec()));
        assert_eq!(cache.get(4).unwrap(), Some(b"bbbx".to_vec()));
    }
}
