# Changelog

## 0.1.0 (unreleased)

- Initial implementation: `SafeMmapCache` with variable-size values, persisted index, free-list, LRU eviction, and compaction (collect_garbage).
- Added property tests and a deterministic fuzz-like harness.
- Added cargo-fuzz target `fuzz_ops` and a short CI fuzz workflow.
- Added `strict_validations` mode and invariant checks.
