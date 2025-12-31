use criterion::{Criterion, black_box, criterion_group, criterion_main};
use std::io::{Read, Seek, SeekFrom, Write};
use tempfile::NamedTempFile;

use safe_map_cache::{Config, SafeMmapCache};

fn bench_mmap_put_get(c: &mut Criterion) {
    let tmp = NamedTempFile::new().expect("temp file");
    let cfg = Config {
        path: tmp.path().to_path_buf(),
        index_capacity: 1024,
        initial_file_size: 4 * 1024 * 1024,
    };
    let cache = SafeMmapCache::open(cfg).expect("open");

    c.bench_function("mmap_put", |b| {
        b.iter(|| {
            for i in 0..100u64 {
                let key = black_box(i);
                let val = format!("value{}", i);
                cache.put(key, val.as_bytes()).unwrap();
            }
        })
    });

    // prefill for gets
    for i in 0..100u64 {
        let val = format!("value{}", i);
        cache.put(i, val.as_bytes()).unwrap();
    }

    c.bench_function("mmap_get", |b| {
        b.iter(|| {
            for i in 0..100u64 {
                let _ = cache.get(black_box(i)).unwrap();
            }
        })
    });
}

fn bench_file_write_read(c: &mut Criterion) {
    let mut tmp = NamedTempFile::new().expect("temp file");

    c.bench_function("file_write", |b| {
        b.iter(|| {
            tmp.as_file_mut().seek(SeekFrom::Start(0)).unwrap();
            for i in 0..100u64 {
                let val = format!("value{}\n", i);
                tmp.as_file_mut().write_all(val.as_bytes()).unwrap();
            }
            tmp.as_file_mut().flush().unwrap();
        })
    });

    // prepare for reads
    tmp.as_file_mut().seek(SeekFrom::Start(0)).unwrap();
    for i in 0..100u64 {
        let val = format!("value{}\n", i);
        tmp.as_file_mut().write_all(val.as_bytes()).unwrap();
    }
    tmp.as_file_mut().flush().unwrap();

    c.bench_function("file_read", |b| {
        b.iter(|| {
            let mut s = String::new();
            tmp.as_file_mut().seek(SeekFrom::Start(0)).unwrap();
            tmp.as_file_mut().read_to_string(&mut s).unwrap();
            black_box(&s);
        })
    });
}

criterion_group!(benches, bench_mmap_put_get, bench_file_write_read);
criterion_main!(benches);
