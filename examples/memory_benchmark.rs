use std::{
    collections::HashSet,
    time::{Duration, Instant},
};

use indicatif::{ProgressBar, ProgressStyle};
use mem_dbg::{MemSize, SizeFlags};
use multi_ranged::{MultiRange, MultiRanged};
use plotters::prelude::*;
use plotters::coord::types::RangedCoordf64;
use rand::prelude::*;
use sux::{
    bits::bit_vec::BitVec,
    traits::{BitVecOps, BitVecOpsMut},
};

struct BenchmarkResult {
    density: f64,
    vec_size: usize,
    hashset_size: usize,
    multirange_size: usize,
    bitvec_size: usize,
    vec_insert_time: Duration,
    hashset_insert_time: Duration,
    multirange_insert_time: Duration,
    bitvec_insert_time: Duration,
    vec_contains_time: Duration,
    hashset_contains_time: Duration,
    multirange_contains_time: Duration,
    bitvec_contains_time: Duration,
}

const PANTONE_CLASSIC_BLUE: RGBColor = RGBColor(15, 76, 129);
const PANTONE_VIVA_MAGENTA: RGBColor = RGBColor(187, 38, 73);
const PANTONE_GREENERY: RGBColor = RGBColor(136, 176, 75);
const PANTONE_ULTRA_VIOLET: RGBColor = RGBColor(95, 75, 139);

macro_rules! define_draw_plot {
    ($name:ident, $y_type:ty) => {
        fn $name<'a, DB>(
            chart: &mut ChartContext<'a, DB, Cartesian2d<RangedCoordf64, $y_type>>,
            y_label: &str,
            results: &[BenchmarkResult],
            extractors: [fn(&BenchmarkResult) -> f64; 4],
            log_scale: bool,
        ) -> Result<(), Box<dyn std::error::Error>>
        where
            DB: DrawingBackend + 'a,
            <DB as DrawingBackend>::ErrorType: 'static,
        {
            chart
                .configure_mesh()
                .x_desc("Density")
                .y_desc(y_label)
                .axis_desc_style(("sans-serif", 20))
                .draw()?;

            let colors = [
                &PANTONE_CLASSIC_BLUE,
                &PANTONE_VIVA_MAGENTA,
                &PANTONE_GREENERY,
                &PANTONE_ULTRA_VIOLET,
            ];
            let labels = ["Vec", "HashSet", "MultiRange", "BitVec"];

            for i in 0..4 {
                chart
                    .draw_series(LineSeries::new(
                        results.iter().map(|r| {
                            let val = extractors[i](r);
                            (r.density, if log_scale { val.max(1.0) } else { val })
                        }),
                        colors[i],
                    ))?
                    .label(labels[i])
                    .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], colors[i]));
            }

            chart
                .configure_series_labels()
                .background_style(&WHITE.mix(0.8))
                .border_style(&BLACK)
                .draw()?;

            Ok(())
        }
    };
}

define_draw_plot!(draw_plot_linear, RangedCoordf64);
define_draw_plot!(draw_plot_log, LogCoord<f64>);

fn generate_plot(
    filename: &str,
    caption: &str,
    y_label: &str,
    results: &[BenchmarkResult],
    extractors: [fn(&BenchmarkResult) -> f64; 4],
    log_scale: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let root = BitMapBackend::new(filename, (1024, 768)).into_drawing_area();
    root.fill(&WHITE)?;

    let max_val = results
        .iter()
        .flat_map(|r| extractors.iter().map(move |e| e(r)))
        .reduce(f64::max)
        .unwrap_or(1.0);

    if log_scale {
        let mut chart = ChartBuilder::on(&root)
            .caption(caption, ("sans-serif", 50).into_font())
            .margin(10)
            .x_label_area_size(40)
            .y_label_area_size(60)
            .build_cartesian_2d(0f64..1f64, (1f64..max_val).log_scale())?;

        draw_plot_log(&mut chart, y_label, results, extractors, true)?;
    } else {
        let mut chart = ChartBuilder::on(&root)
            .caption(caption, ("sans-serif", 50).into_font())
            .margin(10)
            .x_label_area_size(40)
            .y_label_area_size(60)
            .build_cartesian_2d(0f64..1f64, 0f64..max_val)?;

        draw_plot_linear(&mut chart, y_label, results, extractors, false)?;
    }

    root.present()?;
    println!("Plot saved to {}", filename);
    Ok(())
}

const CONTAINS_REPEATS: u32 = 100;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let max_val: i32 = 100_000;
    let seeds: u64 = 10;
    let step_size = 500;

    let mut results: Vec<BenchmarkResult> = Vec::with_capacity((max_val / step_size + 1) as usize);

    // Initialize results with 0s
    for i in 0..=(max_val / step_size) {
        results.push(BenchmarkResult {
            density: (i * step_size) as f64 / max_val as f64,
            vec_size: 0,
            hashset_size: 0,
            multirange_size: 0,
            bitvec_size: 0,
            vec_insert_time: Duration::ZERO,
            hashset_insert_time: Duration::ZERO,
            multirange_insert_time: Duration::ZERO,
            bitvec_insert_time: Duration::ZERO,
            vec_contains_time: Duration::ZERO,
            hashset_contains_time: Duration::ZERO,
            multirange_contains_time: Duration::ZERO,
            bitvec_contains_time: Duration::ZERO,
        });
    }

    let total_steps = seeds * (max_val as u64);
    let pb = ProgressBar::new(total_steps);
    pb.set_style(
        ProgressStyle::default_bar()
            .template(
                "{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} ({eta})",
            )?
            .progress_chars("#>-"),
    );

    for seed in 0..seeds {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut random_numbers: Vec<i32> = (0..max_val).collect();
        random_numbers.shuffle(&mut rng);

        let mut vec = Vec::new();
        let mut hash_set = HashSet::new();
        let mut multi_range = MultiRange::default();
        let mut bit_vec = BitVec::new(max_val as usize);

        for (i, &num) in random_numbers.iter().enumerate() {
            pb.inc(1);
            let start = Instant::now();
            if !vec.contains(&num) {
                vec.push(num);
            }
            let vec_insert = start.elapsed();

            let start = Instant::now();
            hash_set.insert(num);
            let hashset_insert = start.elapsed();

            let start = Instant::now();
            let _ = multi_range.insert(num);
            let multirange_insert = start.elapsed();

            let start = Instant::now();
            bit_vec.set(num as usize, true);
            let bitvec_insert = start.elapsed();

            if (i + 1) % step_size as usize == 0 {
                let index = (i + 1) / step_size as usize;
                if index < results.len() {
                    let flags = SizeFlags::default() | SizeFlags::CAPACITY | SizeFlags::FOLLOW_REFS;
                    results[index].vec_size += vec.mem_size(flags);
                    results[index].hashset_size += hash_set.mem_size(flags);
                    results[index].multirange_size += multi_range.mem_size(flags);
                    results[index].bitvec_size += bit_vec.mem_size(flags);

                    results[index].vec_insert_time += vec_insert;
                    results[index].hashset_insert_time += hashset_insert;
                    results[index].multirange_insert_time += multirange_insert;
                    results[index].bitvec_insert_time += bitvec_insert;

                    // Measure contains time (average of 100 lookups)
                    let mut vec_contains_sum = Duration::ZERO;
                    let mut hashset_contains_sum = Duration::ZERO;
                    let mut multirange_contains_sum = Duration::ZERO;
                    let mut bitvec_contains_sum = Duration::ZERO;

                    for _ in 0..CONTAINS_REPEATS {
                        let target = rng.random_range(0..max_val);

                        let start = Instant::now();
                        black_box(vec.contains(&target));
                        vec_contains_sum += start.elapsed();

                        let start = Instant::now();
                        black_box(hash_set.contains(&target));
                        hashset_contains_sum += start.elapsed();

                        let start = Instant::now();
                        black_box(multi_range.contains(target));
                        multirange_contains_sum += start.elapsed();

                        let start = Instant::now();
                        black_box(bit_vec.get(target as usize));
                        bitvec_contains_sum += start.elapsed();
                    }

                    results[index].vec_contains_time += vec_contains_sum / CONTAINS_REPEATS;
                    results[index].hashset_contains_time += hashset_contains_sum / CONTAINS_REPEATS;
                    results[index].multirange_contains_time +=
                        multirange_contains_sum / CONTAINS_REPEATS;
                    results[index].bitvec_contains_time += bitvec_contains_sum / CONTAINS_REPEATS;
                }
            }
        }
    }

    pb.finish_with_message("Benchmark complete");

    // Average the results
    for result in &mut results {
        result.vec_size /= seeds as usize;
        result.hashset_size /= seeds as usize;
        result.multirange_size /= seeds as usize;
        result.bitvec_size /= seeds as usize;

        result.vec_insert_time /= seeds as u32;
        result.hashset_insert_time /= seeds as u32;
        result.multirange_insert_time /= seeds as u32;
        result.bitvec_insert_time /= seeds as u32;

        result.vec_contains_time /= seeds as u32;
        result.hashset_contains_time /= seeds as u32;
        result.multirange_contains_time /= seeds as u32;
        result.bitvec_contains_time /= seeds as u32;
    }

    // Plotting
    let configs: [(&str, &str, &str, [fn(&BenchmarkResult) -> f64; 4]); 5] = [
        (
            "Memory Usage",
            "memory_benchmark",
            "Memory Usage (Bytes)",
            [
                |r| r.vec_size as f64,
                |r| r.hashset_size as f64,
                |r| r.multirange_size as f64,
                |r| r.bitvec_size as f64,
            ],
        ),
        (
            "Insertion Time",
            "insert_time_benchmark",
            "Insertion Time (ns)",
            [
                |r| r.vec_insert_time.as_nanos() as f64,
                |r| r.hashset_insert_time.as_nanos() as f64,
                |r| r.multirange_insert_time.as_nanos() as f64,
                |r| r.bitvec_insert_time.as_nanos() as f64,
            ],
        ),
        (
            "Contains Time",
            "contains_time_benchmark",
            "Contains Time (ns)",
            [
                |r| r.vec_contains_time.as_nanos() as f64,
                |r| r.hashset_contains_time.as_nanos() as f64,
                |r| r.multirange_contains_time.as_nanos() as f64,
                |r| r.bitvec_contains_time.as_nanos() as f64,
            ],
        ),
        (
            "Insertion Time * Memory",
            "insert_time_memory_product",
            "Time * Memory (ns * bytes)",
            [
                |r| r.vec_insert_time.as_nanos() as f64 * r.vec_size as f64,
                |r| r.hashset_insert_time.as_nanos() as f64 * r.hashset_size as f64,
                |r| r.multirange_insert_time.as_nanos() as f64 * r.multirange_size as f64,
                |r| r.bitvec_insert_time.as_nanos() as f64 * r.bitvec_size as f64,
            ],
        ),
        (
            "Contains Time * Memory",
            "contains_time_memory_product",
            "Time * Memory (ns * bytes)",
            [
                |r| r.vec_contains_time.as_nanos() as f64 * r.vec_size as f64,
                |r| r.hashset_contains_time.as_nanos() as f64 * r.hashset_size as f64,
                |r| r.multirange_contains_time.as_nanos() as f64 * r.multirange_size as f64,
                |r| r.bitvec_contains_time.as_nanos() as f64 * r.bitvec_size as f64,
            ],
        ),
    ];

    for (name, file_prefix, y_label, extractors) in configs {
        generate_plot(
            &format!("{}_linear.png", file_prefix),
            &format!("{} vs Density (Linear)", name),
            y_label,
            &results,
            extractors,
            false,
        )?;
        generate_plot(
            &format!("{}_log.png", file_prefix),
            &format!("{} vs Density (Log)", name),
            y_label,
            &results,
            extractors,
            true,
        )?;
    }

    // Also print table for verification
    println!("| Density | Vec (bytes) | HashSet (bytes) | MultiRange (bytes) | BitVec (bytes) |");
    println!("|---------|-------------|-----------------|--------------------|----------------|");
    for r in results.iter().step_by(10) {
        // Print every 10th result to save space
        println!(
            "| {:.2}    | {:<11} | {:<15} | {:<18} | {:<14} |",
            r.density, r.vec_size, r.hashset_size, r.multirange_size, r.bitvec_size
        );
    }

    Ok(())
}

fn black_box<T>(dummy: T) -> T {
    std::hint::black_box(dummy)
}
