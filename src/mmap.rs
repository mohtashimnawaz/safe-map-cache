use std::{fs::File, fs::OpenOptions, io, path::PathBuf};

use memmap2::{MmapMut, MmapOptions};

/// A small safe wrapper around a file-backed mutable mmap.
///
/// SAFETY:
/// - `MmapOptions::map_mut` is `unsafe` because it creates a memory mapping of a
///   file into the process address space. The mapping becomes invalid if the
///   underlying file is truncated while the mapping exists. This wrapper ensures
///   the mapping is dropped (unmapped) before the file is resized.
/// - The `File` object is kept alive as long as the mapping exists, satisfying
///   the requirement that the file backing the mapping remains valid.
pub struct MmapFile {
    _path: PathBuf,
    file: File,
    mmap: Option<MmapMut>,
    len: usize,
}

impl MmapFile {
    /// Open (creating if needed) a file and map it with at least `len` bytes.
    pub fn open(path: PathBuf, len: usize) -> Result<Self, io::Error> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&path)?;
        file.set_len(len as u64)?;
        // SAFETY: mapping is safe because `file` is newly opened and will be kept
        // alive inside the returned `MmapFile` for the lifetime of the mapping.
        let mmap = Some(unsafe { MmapOptions::new().map_mut(&file)? });

        Ok(MmapFile {
            _path: path,
            file,
            mmap,
            len,
        })
    }

    /// Get an immutable view of the mapping.
    pub fn as_slice(&self) -> &[u8] {
        &self.mmap.as_ref().expect("mapping present")[..]
    }

    /// Get a mutable view of the mapping.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.mmap.as_mut().expect("mapping present")[..]
    }

    /// Flush the mapping to disk.
    pub fn flush(&self) -> Result<(), io::Error> {
        if let Some(m) = &self.mmap {
            m.flush()?;
        }
        Ok(())
    }

    /// Resize the backing file and remap.
    pub fn resize(&mut self, new_len: usize) -> Result<(), io::Error> {
        if new_len == self.len {
            return Ok(());
        }
        // Drop (unmap) current mapping before changing file size.
        if let Some(old) = self.mmap.take() {
            drop(old);
        }
        self.file.set_len(new_len as u64)?;
        // SAFETY: remap after file has been resized and ensured to be stable.
        self.mmap = Some(unsafe { MmapOptions::new().map_mut(&self.file)? });
        self.len = new_len;
        Ok(())
    }

    /// Current mapped length.
    pub fn len(&self) -> usize {
        self.len
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::NamedTempFile;

    #[test]
    fn open_write_and_resize() {
        let tmp = NamedTempFile::new().expect("temp file");
        let mut mm = MmapFile::open(tmp.path().to_path_buf(), 4096).expect("open mmap");
        let s = mm.as_mut_slice();
        assert!(s.len() >= 4096);
        s[0] = 42;
        mm.flush().expect("flush");

        mm.resize(8192).expect("resize");
        let s2 = mm.as_mut_slice();
        assert!(s2.len() >= 8192);
        assert_eq!(s2[0], 42);
    }
}
