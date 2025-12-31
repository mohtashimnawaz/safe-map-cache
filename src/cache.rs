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
            // validate and possibly repair the index slot
            let rec = guard.get_valid_index_slot(slot)?;
            if rec.flags == 0 {
                return Ok(None);
            }
            let offset = rec.offset as usize;
            let len = rec.len as usize;
            let buf = guard.mmap.as_mut_slice();
            let end = offset.checked_add(len).ok_or_else(|| CacheError::Io(io::Error::new(io::ErrorKind::UnexpectedEof, "corrupt data (overflow)")))?;
            if end > buf.len() {
                // treat as not found after repair
                return Ok(None);
            }
            let data = buf[offset..end].to_vec();
            return Ok(Some(data));
        }
        Ok(None)
    }

    /// Put a key/value pair into the cache.
    pub fn put(&self, key: u64, value: &[u8]) -> Result<(), CacheError> {
        let mut guard = self.inner.write();
        // if exists and fits, overwrite in place
        if let Some(slot) = guard.lru.get(&key).cloned() {
            let rec = guard.get_valid_index_slot(slot)?;
            if rec.flags != 0 && (value.len() as u64) <= rec.len {
                let offset = rec.offset as usize;
                let end = offset.checked_add(value.len()).ok_or_else(|| CacheError::Io(io::Error::new(io::ErrorKind::UnexpectedEof, "corrupt data (overflow)")))?;
                let buf = guard.mmap.as_mut_slice();
                if end > buf.len() {
                    // corrupt slot; clear and fall through to allocate
                    let mut inv = rec;
                    inv.flags = 0;
                    guard.write_index_slot(slot, inv)?;
                } else {
                    buf[offset..end].copy_from_slice(value);
                    // update length if changed
                    let mut new_rec = rec;
                    new_rec.len = value.len() as u64;
                    guard.write_index_slot(slot, new_rec)?;
                    guard.lru.put(key, slot);
                    return Ok(());
                }
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
        // collect candidate free extents (length sufficient) without holding an immutable borrow
        let candidates: Vec<(usize, usize, usize, usize)> = guard
            .free_extents
            .iter()
            .enumerate()
            .filter_map(|(i, (off, len, slot_idx))| if *len >= needed { Some((i, *off, *len, *slot_idx)) } else { None })
            .collect();

        // check each candidate for overlap with live records (we have mutable access to guard)
        let mut chosen: Option<(usize, usize, usize, usize)> = None;
        for (i, off, len, slot_idx) in candidates {
            let mut overlap = false;
            for idx in 0..guard.index_capacity {
                let rec = match guard.get_valid_index_slot(idx) {
                    Ok(r) => r,
                    Err(_) => continue,
                };
                if rec.flags != 0 {
                    let a0 = rec.offset as usize;
                    let a1 = match a0.checked_add(rec.len as usize) { Some(v) => v, None => { continue; }};
                    let b0 = off;
                    let b1 = match off.checked_add(len) { Some(v) => v, None => { continue; }};
                    if a0 < b1 && b0 < a1 {
                        overlap = true;
                        break;
                    }
                }
            }
            if !overlap {
                chosen = Some((i, off, len, slot_idx));
                break;
            }
        }

        let write_offset = if let Some((i, off, len, slot_idx)) = chosen {
            // adjust or remove the chosen extent
            if len == needed {
                // consume entire free extent slot
                // swap_remove to avoid shifting
                guard.free_extents.swap_remove(i);
                if slot_idx != usize::MAX {
                    guard.write_free_slot(slot_idx, None)?;
                }
            } else {
                // consume from front; adjust extent
                guard.free_extents[i].0 = off + needed;
                guard.free_extents[i].1 = len - needed;
                if slot_idx != usize::MAX {
                    guard.write_free_slot(slot_idx, Some((off + needed, len - needed)))?;
                }
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
            let rec = guard.get_valid_index_slot(slot)?;
            let data = if rec.flags == 0 { None } else {
                let buf = guard.mmap.as_mut_slice();
                let offset = rec.offset as usize;
                let len = rec.len as usize;
                let end = offset.checked_add(len).ok_or_else(|| CacheError::Io(io::Error::new(io::ErrorKind::UnexpectedEof, "corrupt data (overflow)")))?;
                if end > buf.len() {
                    // already cleaned by get_valid_index_slot, but be defensive
                    return Ok(None);
                }
                Some(buf[offset..end].to_vec())
            };
            // if slot was already cleared by validation, just mark free and return
            if rec.flags == 0 {
                guard.free_slots.push(slot);
                return Ok(data);
            }

            // invalidate index slot and mark free
            let mut inv = rec;
            inv.flags = 0;
            guard.write_index_slot(slot, inv)?;
            guard.free_slots.push(slot);

            // record freed data extent into persistent free-list (if space), coalescing with neighbors
            guard.insert_free_extent(rec.offset as usize, rec.len as usize)?;
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
        // read-only pass in its own scope so we can do mutations after
        let mut clear_index_slots: Vec<(usize, IndexRecord)> = Vec::new();
        let mut clear_free_slots: Vec<usize> = Vec::new();
        {
            let buf = self.mmap.as_slice();
            for i in 0..self.index_capacity {
                let start = HEADER_SIZE + i * RECORD_SIZE;
                let rec = IndexRecord::from_bytes(&buf[start..start + RECORD_SIZE]);
                if rec.flags != 0 {
                    // verify offsets and lengths are sane
                    let off = rec.offset as usize;
                    let len = rec.len as usize;
                    if let Some(end) = off.checked_add(len) {
                        if end <= buf.len() {
                            self.lru.put(rec.key, i);
                            if end > self.next_data_offset {
                                self.next_data_offset = end;
                            }
                        } else {
                            // mark clear
                            clear_index_slots.push((i, rec));
                        }
                    } else {
                        // overflow: mark clear
                        clear_index_slots.push((i, rec));
                    }
                } else {
                    // empty
                    self.free_slots.push(i);
                }
            }

            // load free-list entries (immutable borrow)
            for i in 0..self.free_capacity {
                let start = self.freelist_start + i * FREE_ENTRY_SIZE;
                let off = u64::from_le_bytes(buf[start..start + 8].try_into().unwrap()) as usize;
                let len = u64::from_le_bytes(buf[start + 8..start + 16].try_into().unwrap()) as usize;
                if len != 0 {
                    if let Some(end) = off.checked_add(len) {
                        if end <= buf.len() {
                            self.free_extents.push((off, len, i));
                        } else {
                            // mark clear
                            clear_free_slots.push(i);
                        }
                    } else {
                        // overflow: mark clear
                        clear_free_slots.push(i);
                    }
                }
            }
        }

        // perform clears collected
        for (i, mut rec) in clear_index_slots {
            rec.flags = 0;
            self.write_index_slot(i, rec)?;
            self.free_slots.push(i);
        }

        for i in clear_free_slots {
            self.write_free_slot(i, None)?;
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

    /// Read an index slot and validate it; if corrupt, clear it and return a zeroed record.
    fn get_valid_index_slot(&mut self, slot: usize) -> Result<IndexRecord, io::Error> {
        let rec = self.read_index_slot(slot)?;
        if rec.flags != 0 {
            let offset = rec.offset as usize;
            let len = rec.len as usize;
            // validate range
            if let Some(end) = offset.checked_add(len) {
                if end > self.mmap.len() {
                    // corrupt: clear slot
                    let mut inv = rec;
                    inv.flags = 0;
                    self.write_index_slot(slot, inv)?;
                    self.free_slots.push(slot);
                    return Ok(inv);
                }
            } else {
                // overflow
                let mut inv = rec;
                inv.flags = 0;
                self.write_index_slot(slot, inv)?;
                self.free_slots.push(slot);
                return Ok(inv);
            }
        }
        Ok(rec)
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

    /// Insert a free extent and coalesce with adjacent free extents if present.
    fn insert_free_extent(&mut self, mut off: usize, mut len: usize) -> Result<(), io::Error> {
        // Merge adjacent extents robustly and coalesce persistent slots.
        // We'll repeatedly look for extents adjacent to [off, off+len) and merge them.
        loop {
            let mut merged_index: Option<usize> = None;
            for idx in 0..self.free_extents.len() {
                let (e_off, e_len, e_slot) = self.free_extents[idx];
                // previous adjacent
                if let Some(sum) = e_off.checked_add(e_len) {
                    if sum == off {
                        // merge into existing extent
                        let new_off = e_off;
                        let new_len = match e_len.checked_add(len) { Some(v) => v, None => continue };
                        self.free_extents[idx].0 = new_off;
                        self.free_extents[idx].1 = new_len;
                        // persist merge
                        if e_slot != usize::MAX {
                            self.write_free_slot(e_slot, Some((new_off, new_len)))?;
                        }
                        off = new_off;
                        len = new_len;
                        merged_index = Some(idx);
                        break;
                    }
                }
                // next adjacent
                if let Some(sum) = off.checked_add(len) {
                    if sum == e_off {
                        let new_off = off;
                        let new_len = match len.checked_add(e_len) { Some(v) => v, None => continue };
                        self.free_extents[idx].0 = new_off;
                        self.free_extents[idx].1 = new_len;
                        if e_slot != usize::MAX {
                            self.write_free_slot(e_slot, Some((new_off, new_len)))?;
                        }
                        off = new_off;
                        len = new_len;
                        merged_index = Some(idx);
                        break;
                    }
                }
            }

            if let Some(idx) = merged_index {
                // After merging we should also look for any other extent that now overlaps and fold it in
                // We'll continue the loop which will find more adjacent extents.
                continue;
            }
            break;
        }

        // If exact match already exists in free_extents, we're done
        for &(_o, _l, _slot) in &self.free_extents {
            if _o == off && _l == len {
                return Ok(());
            }
        }

        // Try to persist into free-list
        let buf = self.mmap.as_mut_slice();
        for i in 0..self.free_capacity {
            let start = self.freelist_start + i * FREE_ENTRY_SIZE;
            let len_existing = u64::from_le_bytes(buf[start + 8..start + 16].try_into().unwrap()) as usize;
            if len_existing == 0 {
                self.write_free_slot(i, Some((off, len)))?;
                self.free_extents.push((off, len, i));
                return Ok(());
            }
        }

        // no persistent slot available: store in-memory
        self.free_extents.push((off, len, usize::MAX));
        Ok(())
    }

    /// Compact data area by moving live blobs to a contiguous region starting at data_start.
    fn collect_garbage(&mut self) -> Result<(), io::Error> {
        // Build a list of live entries and capture their data into temporaries
        let mut next = self.data_start;
        let buf = self.mmap.as_slice();
        let mut live = Vec::new(); // (index_slot, IndexRecord, data)
        for i in 0..self.index_capacity {
            let rec = match self.get_valid_index_slot(i) {
                Ok(r) => r,
                Err(_) => continue,
            };
            if rec.flags != 0 {
                let buf = self.mmap.as_slice();
                let old_off = rec.offset as usize;
                let len = rec.len as usize;
                let end = old_off.checked_add(len).ok_or_else(|| io::Error::new(io::ErrorKind::UnexpectedEof, "corrupt data (overflow)"))?;
                if end > buf.len() {
                    // invalid entry, clear
                    let mut inv = rec;
                    inv.flags = 0;
                    self.write_index_slot(i, inv)?;
                    continue;
                }
                let data = buf[old_off..end].to_vec();
                live.push((i, rec, data));
            }
        }

        // Now write all live data sequentially into the data area and update index
        {
            for (i, mut rec, data) in live.into_iter() {
                let len = data.len();
                let dst = next;
                let end = dst.checked_add(len).ok_or_else(|| io::Error::new(io::ErrorKind::UnexpectedEof, "collect_garbage would overflow"))?;
                // check current length (immutable borrow) and grow if needed
                let cur_len = self.mmap.as_slice().len();
                if end > cur_len {
                    let grow_to = (cur_len.max(end) + 4095) & !4095usize;
                    self.mmap.resize(grow_to)?;
                }
                // safe to reborrow mutable slice now
                let mut buf_mut = self.mmap.as_mut_slice();
                buf_mut[dst..end].copy_from_slice(&data);
                rec.offset = dst as u64;
                // write updated index bytes
                rec.to_bytes(&mut buf_mut[HEADER_SIZE + i * RECORD_SIZE..HEADER_SIZE + i * RECORD_SIZE + RECORD_SIZE]);
                next = end;
            }

            // zero free-list
            let mut buf_mut = self.mmap.as_mut_slice();
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
