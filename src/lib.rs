//! safe-mmap-cache: a memory-mapped LRU cache
//!
//! This crate provides a safe API around a memory-mapped file that can be used
//! as a cache. Implementation is a work in progress.

pub mod cache;

pub use cache::{CacheError, Config, SafeMmapCache};
