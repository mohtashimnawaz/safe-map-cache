use std::{fs::File, fs::OpenOptions, io, path::PathBuf};

use memmap2::{MmapMut, MmapOptions};

/// A small safe wrapper around a file-backed mutable mmap.
pub struct MmapFile {
    path: PathBuf,
    file: File,
    mmap: MmapMut,
    len: usize,
}

impl MmapFile {
    /// Open (creating if needed) a file and map it with at least `len` bytes.
    pub fn open(path: PathBuf, len: usize) -> Result<Self, io::Error> {
        let file = OpenOptions::new().read(true).write(true).create(true).open(&path)?;
        file.set_len(len as u64)?;
        let mmap = unsafe { MmapOptions::new().map_mut(&file)? };

        Ok(MmapFile { path, file, mmap, len })
    }

    /// Get a mutable view of the mapping.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.mmap[..]
    }

    /// Flush the mapping to disk.
    pub fn flush(&self) -> Result<(), io::Error> {
        self.mmap.flush()?;
        Ok(())
    }

    /// Resize the backing file and remap.
    pub fn resize(&mut self, new_len: usize) -> Result<(), io::Error> {
        if new_len == self.len {
            return Ok(());
        }
        // Dropping mmap before changing file size ensures remap works across platforms.
        drop(&self.mmap);
        self.file.set_len(new_len as u64)?;
        self.mmap = unsafe { MmapOptions::new().map_mut(&self.file)? };
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
