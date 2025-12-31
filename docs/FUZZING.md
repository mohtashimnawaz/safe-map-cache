Fuzzing and property tests

This repository includes:
- `tests/proptest_ops.rs`: proptest-based property test generating random sequences of put/get/remove operations.
- `tests/fuzz_like.rs`: a lightweight, deterministic, randomized stress test (a "fuzz-like" harness) that runs many random ops and reports any inconsistencies or panics.

Reproducing a failing fuzz run

When the fuzz harness panics it prints the path to the temporary backing file; you can reproduce the state by inspecting that file or copying it and opening it with the library (e.g., run a small program that opens the file using `SafeMmapCache::open` and replays a short sequence).

If you want to run a more aggressive, native fuzzing workflow using `cargo-fuzz`:

1. Install cargo-fuzz:
   cargo install cargo-fuzz

2. Initialize fuzz directory:
   cargo fuzz init

3. Add a fuzz target that imports `safe_map_cache` and invokes sequences of operations.

The included harness is intentionally lightweight so it can be run in CI without special tooling; it caught an index corruption in local testing — further investigation and more intrusive fuzzing (`cargo-fuzz`) is encouraged for deeper coverage.

cargo-fuzz (added)
------------------
We added a `fuzz` folder with a `fuzz_ops` target under `fuzz/fuzz_targets/fuzz_ops.rs` that drives randomized put/get/remove sequences.

To run locally:

- Install cargo-fuzz: `cargo install cargo-fuzz`
- Run the fuzz target: `cargo fuzz run fuzz_ops -- -max_total_time=60`

The GitHub Actions workflow `fuzz.yml` runs a short session (30s) to catch obvious regressions and uploads any artifacts.

Notes:
- cargo-fuzz is much more thorough if run for long periods and with a persistent corpus; the minimal integration here gives you an easy starting point.
