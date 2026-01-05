use std::{collections::HashSet, hint::black_box};

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use multi_ranged::{MultiRange, MultiRanged};
use rand::prelude::*;
use sux::bits::bit_vec::BitVec;
use sux::traits::{BitVecOps, BitVecOpsMut};

fn benchmark_insertion_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("Insertion Random");
    let sizes = [100, 1000, 10000];

    for size in sizes {
        let mut rng = StdRng::seed_from_u64(42);
        let random_numbers: Vec<i32> = (0..size).map(|_| rng.random_range(0..size * 2)).collect();

        group.bench_with_input(BenchmarkId::new("Vec", size), &size, |b, &_s| {
            b.iter(|| {
                let mut v = Vec::new();
                for &i in &random_numbers {
                    v.push(black_box(i));
                }
                v
            })
        });

        group.bench_with_input(BenchmarkId::new("HashSet", size), &size, |b, &_s| {
            b.iter(|| {
                let mut h = HashSet::new();
                for &i in &random_numbers {
                    h.insert(black_box(i));
                }
                h
            })
        });

        group.bench_with_input(BenchmarkId::new("MultiRange", size), &size, |b, &_s| {
            b.iter(|| {
                let mut m = MultiRange::default();
                for &i in &random_numbers {
                    let _ = m.insert(black_box(i));
                }
                m
            })
        });

        group.bench_with_input(BenchmarkId::new("BitVec", size), &size, |b, &_s| {
            b.iter(|| {
                let mut bv = BitVec::new((size * 2) as usize);
                for &i in &random_numbers {
                    bv.set(black_box(i) as usize, true);
                }
                bv
            })
        });
    }
    group.finish();
}

fn benchmark_contains_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("Contains Random");
    let sizes = [100, 1000, 10000];

    for size in sizes {
        let mut rng = StdRng::seed_from_u64(42);
        let random_numbers: Vec<i32> = (0..size).map(|_| rng.random_range(0..size * 2)).collect();

        let vec = random_numbers.clone();
        let hash_set: HashSet<i32> = random_numbers.iter().cloned().collect();
        let mut multi_range = MultiRange::default();
        for &i in &random_numbers {
            let _ = multi_range.insert(i);
        }
        let mut bit_vec = BitVec::new((size * 4) as usize);
        for &i in &random_numbers {
            bit_vec.set(i as usize, true);
        }

        // Pick a number that is likely in the set and one that is likely not
        let target_in = random_numbers[size as usize / 2];
        let target_out = size * 3; // Likely not in range 0..size*2

        group.bench_with_input(BenchmarkId::new("Vec", size), &size, |b, &_s| {
            b.iter(|| {
                black_box(vec.contains(&target_in));
                black_box(vec.contains(&target_out));
            })
        });

        group.bench_with_input(BenchmarkId::new("HashSet", size), &size, |b, &_s| {
            b.iter(|| {
                black_box(hash_set.contains(&target_in));
                black_box(hash_set.contains(&target_out));
            })
        });

        group.bench_with_input(BenchmarkId::new("MultiRange", size), &size, |b, &_s| {
            b.iter(|| {
                black_box(multi_range.contains(target_in));
                black_box(multi_range.contains(target_out));
            })
        });

        group.bench_with_input(BenchmarkId::new("BitVec", size), &size, |b, &_s| {
            b.iter(|| {
                black_box(bit_vec.get(target_in as usize));
                black_box(bit_vec.get(target_out as usize));
            })
        });
    }
    group.finish();
}

fn benchmark_union_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("Union Random");
    let sizes = [100, 1000, 10000];

    for size in sizes {
        let mut rng = StdRng::seed_from_u64(42);
        let range1: Vec<i32> = (0..size).map(|_| rng.random_range(0..size * 2)).collect();
        let range2: Vec<i32> = (0..size).map(|_| rng.random_range(0..size * 2)).collect();

        let vec1 = range1.clone();
        let vec2 = range2.clone();

        let set1: HashSet<i32> = range1.iter().cloned().collect();
        let set2: HashSet<i32> = range2.iter().cloned().collect();

        let mut mr1 = MultiRange::default();
        for &i in &range1 {
            let _ = mr1.insert(i);
        }
        let mut mr2 = MultiRange::default();
        for &i in &range2 {
            let _ = mr2.insert(i);
        }

        group.bench_with_input(BenchmarkId::new("Vec", size), &size, |b, &_s| {
            b.iter(|| {
                let mut v = vec1.clone();
                v.extend(&vec2);
                v.sort();
                v.dedup();
                v
            })
        });

        group.bench_with_input(BenchmarkId::new("HashSet", size), &size, |b, &_s| {
            b.iter(|| {
                let mut s = set1.clone();
                s.extend(&set2);
                s
            })
        });

        group.bench_with_input(BenchmarkId::new("MultiRange", size), &size, |b, &_s| {
            b.iter(|| {
                let m1 = mr1.clone();
                let m2 = mr2.clone();
                m1 | m2
            })
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    benchmark_insertion_random,
    benchmark_contains_random,
    benchmark_union_random
);
criterion_main!(benches);
