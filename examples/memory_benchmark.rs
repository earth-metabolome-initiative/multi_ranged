use std::{
    collections::{BTreeSet, HashSet},
    io::Write,
    time::{Duration, Instant},
};

use comfy_table::{Table, presets::ASCII_MARKDOWN};
use indicatif::{ProgressBar, ProgressStyle};
use mem_dbg::{MemSize, SizeFlags};
use multi_ranged::{MultiRange, MultiRanged};
use plotters::{
    coord::types::{LogCoord, RangedCoordf64},
    prelude::*,
};
use rand::prelude::*;
use sux::{
    bits::bit_vec::BitVec,
    traits::{BitVecOps, BitVecOpsMut},
};

const PANTONE_CLASSIC_BLUE: RGBColor = RGBColor(15, 76, 129);
const PANTONE_VIVA_MAGENTA: RGBColor = RGBColor(187, 38, 73);
const PANTONE_GREENERY: RGBColor = RGBColor(136, 176, 75);
const PANTONE_ULTRA_VIOLET: RGBColor = RGBColor(95, 75, 139);
const PANTONE_TANGERINE: RGBColor = RGBColor(255, 140, 0);

trait BenchmarkCollection {
    fn name() -> &'static str;
    fn color() -> RGBColor;
    fn new(capacity: usize) -> Self;
    fn insert(&mut self, val: i32);
    fn contains(&self, val: i32) -> bool;
    fn get_mem_size(&self) -> usize;
}

impl BenchmarkCollection for Vec<i32> {
    fn name() -> &'static str {
        "Vec"
    }
    fn color() -> RGBColor {
        PANTONE_CLASSIC_BLUE
    }
    fn new(capacity: usize) -> Self {
        Vec::with_capacity(capacity)
    }
    fn insert(&mut self, val: i32) {
        if !self.as_slice().contains(&val) {
            self.push(val);
        }
    }
    fn contains(&self, val: i32) -> bool {
        self.as_slice().contains(&val)
    }
    fn get_mem_size(&self) -> usize {
        self.mem_size(SizeFlags::default() | SizeFlags::CAPACITY | SizeFlags::FOLLOW_REFS)
    }
}

impl BenchmarkCollection for HashSet<i32> {
    fn name() -> &'static str {
        "HashSet"
    }
    fn color() -> RGBColor {
        PANTONE_VIVA_MAGENTA
    }
    fn new(capacity: usize) -> Self {
        HashSet::with_capacity(capacity)
    }
    fn insert(&mut self, val: i32) {
        HashSet::insert(self, val);
    }
    fn contains(&self, val: i32) -> bool {
        HashSet::contains(self, &val)
    }
    fn get_mem_size(&self) -> usize {
        self.mem_size(SizeFlags::default() | SizeFlags::CAPACITY | SizeFlags::FOLLOW_REFS)
    }
}

impl BenchmarkCollection for BTreeSet<i32> {
    fn name() -> &'static str {
        "BTreeSet"
    }
    fn color() -> RGBColor {
        PANTONE_TANGERINE
    }
    fn new(_capacity: usize) -> Self {
        BTreeSet::new()
    }
    fn insert(&mut self, val: i32) {
        BTreeSet::insert(self, val);
    }
    fn contains(&self, val: i32) -> bool {
        BTreeSet::contains(self, &val)
    }
    fn get_mem_size(&self) -> usize {
        self.mem_size(SizeFlags::default() | SizeFlags::CAPACITY | SizeFlags::FOLLOW_REFS)
    }
}

impl BenchmarkCollection for MultiRange<i32> {
    fn name() -> &'static str {
        "MultiRange"
    }
    fn color() -> RGBColor {
        PANTONE_GREENERY
    }
    fn new(_capacity: usize) -> Self {
        MultiRange::default()
    }
    fn insert(&mut self, val: i32) {
        let _ = MultiRanged::insert(self, val);
    }
    fn contains(&self, val: i32) -> bool {
        MultiRanged::contains(self, val)
    }
    fn get_mem_size(&self) -> usize {
        self.mem_size(SizeFlags::default() | SizeFlags::CAPACITY | SizeFlags::FOLLOW_REFS)
    }
}

impl BenchmarkCollection for BitVec {
    fn name() -> &'static str {
        "BitVec"
    }
    fn color() -> RGBColor {
        PANTONE_ULTRA_VIOLET
    }
    fn new(capacity: usize) -> Self {
        BitVec::new(capacity)
    }
    fn insert(&mut self, val: i32) {
        self.set(val as usize, true);
    }
    fn contains(&self, val: i32) -> bool {
        self.get(val as usize)
    }
    fn get_mem_size(&self) -> usize {
        self.mem_size(SizeFlags::default() | SizeFlags::CAPACITY | SizeFlags::FOLLOW_REFS)
    }
}

#[derive(Clone, Default)]
struct RunMetrics {
    mem_size: usize,
    insert_time: Duration,
    contains_time: Duration,
}

#[derive(Clone)]
struct AlgoResults {
    name: &'static str,
    color: RGBColor,
    steps: Vec<Vec<RunMetrics>>, // Outer: density steps, Inner: seeds
}

fn black_box<T>(dummy: T) -> T {
    std::hint::black_box(dummy)
}

fn run_benchmark_for_type<T: BenchmarkCollection>(
    all_test_data: &[Vec<i32>],
    max_val: i32,
    step_size: usize,
    num_steps: usize,
    pb: &ProgressBar,
) -> AlgoResults {
    let seeds = all_test_data.len();
    let mut step_results: Vec<Vec<RunMetrics>> = vec![Vec::with_capacity(seeds); num_steps];

    for (seed_idx, random_numbers) in all_test_data.iter().enumerate() {
        let mut collection = T::new(max_val as usize);

        for (i, &num) in random_numbers.iter().enumerate() {
            pb.inc(1);

            let start = Instant::now();
            collection.insert(num);
            let insert_time = start.elapsed();

            if (i + 1) % step_size == 0 {
                let step_idx = (i + 1) / step_size;
                if step_idx < num_steps {
                    let mem_size = collection.get_mem_size();

                    let mut contains_sum = Duration::ZERO;
                    let repeats = 100;
                    let mut rng = StdRng::seed_from_u64((seed_idx as u64) * 1000 + (i as u64));

                    for _ in 0..repeats {
                        let target = rng.random_range(0..max_val);
                        let start = Instant::now();
                        black_box(collection.contains(target));
                        contains_sum += start.elapsed();
                    }
                    let contains_avg = contains_sum / repeats;

                    let metrics = RunMetrics { mem_size, insert_time, contains_time: contains_avg };

                    if step_results[step_idx].len() <= seed_idx {
                        step_results[step_idx].push(metrics);
                    } else {
                        step_results[step_idx][seed_idx] = metrics;
                    }
                }
            }
        }
    }

    AlgoResults { name: T::name(), color: T::color(), steps: step_results }
}

struct Stats {
    mean: f64,
    std: f64,
}

fn compute_stats(values: &[f64]) -> Stats {
    let mean = values.iter().sum::<f64>() / values.len() as f64;
    let variance = values.iter().map(|&x| (x - mean).powi(2)).sum::<f64>() / values.len() as f64;
    Stats { mean, std: variance.sqrt() }
}

fn fmt_stat(stats: &Stats) -> String {
    format!("{:.2} ± {:.2}", stats.mean, stats.std)
}

fn generate_plot(
    filename: &str,
    caption: &str,
    y_label: &str,
    densities: &[f64],
    results: &[AlgoResults],
    extractor: impl Fn(&AlgoResults, usize) -> Stats,
    log_scale: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let root = BitMapBackend::new(filename, (1024, 768)).into_drawing_area();
    root.fill(&WHITE)?;

    let mut max_val = 0.0f64;
    for algo in results {
        for step_idx in 0..densities.len() {
            let val = extractor(algo, step_idx).mean;
            if val > max_val {
                max_val = val;
            }
        }
    }
    max_val = max_val.max(1.0);

    macro_rules! draw_on_chart {
        ($chart:expr) => {
            $chart
                .configure_mesh()
                .x_desc("Density")
                .y_desc(y_label)
                .axis_desc_style(("sans-serif", 20))
                .draw()?;

            for algo in results {
                let data: Vec<_> = densities
                    .iter()
                    .enumerate()
                    .map(|(i, &d)| {
                        let val = extractor(algo, i).mean;
                        (d, if log_scale { val.max(1.0) } else { val })
                    })
                    .collect();

                $chart
                    .draw_series(LineSeries::new(data.clone(), algo.color))?
                    .label(algo.name)
                    .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], algo.color));

                $chart.draw_series(PointSeries::of_element(
                    data,
                    1,
                    algo.color.filled(),
                    &|coord, size, style| {
                        EmptyElement::at(coord) + Circle::new((0, 0), size, style)
                    },
                ))?;
            }

            $chart
                .configure_series_labels()
                .position(SeriesLabelPosition::UpperLeft)
                .background_style(&WHITE.mix(0.8))
                .border_style(&BLACK)
                .draw()?;
        };
    }

    if log_scale {
        let mut chart = ChartBuilder::on(&root)
            .caption(caption, ("sans-serif", 50).into_font())
            .margin(10)
            .x_label_area_size(40)
            .y_label_area_size(60)
            .build_cartesian_2d(0f64..1f64, (1f64..max_val).log_scale())?;
        draw_on_chart!(chart);
    } else {
        let mut chart = ChartBuilder::on(&root)
            .caption(caption, ("sans-serif", 50).into_font())
            .margin(10)
            .x_label_area_size(40)
            .y_label_area_size(60)
            .build_cartesian_2d(0f64..1f64, 0f64..max_val)?;
        draw_on_chart!(chart);
    }

    root.present()?;
    println!("Plot saved to {}", filename);
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let max_val: i32 = 100_000;
    let seeds: usize = 10;
    let step_size = 500;

    let num_steps = max_val as usize / step_size;
    let total_ops = seeds * (max_val as usize) * 5;

    let mut all_test_data = Vec::with_capacity(seeds);
    for seed in 0..seeds {
        let mut rng = StdRng::seed_from_u64(seed as u64);
        let mut nums: Vec<i32> = (0..max_val).collect();
        nums.shuffle(&mut rng);
        all_test_data.push(nums);
    }

    let pb = ProgressBar::new(total_ops as u64);
    pb.set_style(
        ProgressStyle::default_bar()
            .template(
                "{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} ({eta})",
            )?
            .progress_chars("#>-"),
    );

    let results = vec![
        run_benchmark_for_type::<Vec<i32>>(&all_test_data, max_val, step_size, num_steps, &pb),
        run_benchmark_for_type::<HashSet<i32>>(&all_test_data, max_val, step_size, num_steps, &pb),
        run_benchmark_for_type::<BTreeSet<i32>>(&all_test_data, max_val, step_size, num_steps, &pb),
        run_benchmark_for_type::<MultiRange<i32>>(
            &all_test_data,
            max_val,
            step_size,
            num_steps,
            &pb,
        ),
        run_benchmark_for_type::<BitVec>(&all_test_data, max_val, step_size, num_steps, &pb),
    ];

    pb.finish_with_message("Benchmark complete");

    let densities: Vec<f64> =
        (1..=num_steps).map(|i| (i * step_size) as f64 / max_val as f64).collect();

    let mut csv_file = std::fs::File::create("benchmark_results.csv")?;
    write!(csv_file, "Density")?;
    for algo in &results {
        write!(
            csv_file,
            ",{0} Mem Mean,{0} Mem Std,{0} Ins Mean,{0} Ins Std,{0} Con Mean,{0} Con Std",
            algo.name
        )?;
    }
    writeln!(csv_file)?;

    let mut mem_table_full = Table::new();
    let mut ins_table_full = Table::new();
    let mut con_table_full = Table::new();

    let setup_table = |t: &mut Table, headers: &[String]| {
        t.load_preset(ASCII_MARKDOWN);
        let mut h = vec!["Density".to_string()];
        h.extend(headers.iter().cloned());
        t.set_header(h);
    };

    let algo_names: Vec<&str> = results.iter().map(|r| r.name).collect();
    let header_names: Vec<String> = algo_names.iter().map(|n| format!("{} (Bytes)", n)).collect();
    setup_table(&mut mem_table_full, &header_names);

    let header_ins: Vec<String> = algo_names.iter().map(|n| format!("{} (ns)", n)).collect();
    setup_table(&mut ins_table_full, &header_ins);

    let header_con: Vec<String> = algo_names.iter().map(|n| format!("{} (ns)", n)).collect();
    setup_table(&mut con_table_full, &header_con);

    let mut mem_table_short = mem_table_full.clone();
    let mut ins_table_short = ins_table_full.clone();
    let mut con_table_short = con_table_full.clone();

    let target_densities = [0.1, 0.5, 0.9, 0.95, 0.99];
    let is_target = |d: f64| target_densities.iter().any(|&t| (d - t).abs() < 1e-4);

    for (step_idx, &density) in densities.iter().enumerate() {
        if step_idx >= num_steps {
            break;
        }

        let mut row_mem = vec![format!("{:.4}", density)];
        let mut row_ins = vec![format!("{:.4}", density)];
        let mut row_con = vec![format!("{:.4}", density)];

        write!(csv_file, "{:.4}", density)?;

        for algo in &results {
            if step_idx < algo.steps.len() {
                let runs = &algo.steps[step_idx];
                let mem_vals: Vec<f64> = runs.iter().map(|m| m.mem_size as f64).collect();
                let ins_vals: Vec<f64> =
                    runs.iter().map(|m| m.insert_time.as_nanos() as f64).collect();
                let con_vals: Vec<f64> =
                    runs.iter().map(|m| m.contains_time.as_nanos() as f64).collect();

                let s_mem = compute_stats(&mem_vals);
                let s_ins = compute_stats(&ins_vals);
                let s_con = compute_stats(&con_vals);

                write!(
                    csv_file,
                    ",{:.2},{:.2},{:.2},{:.2},{:.2},{:.2}",
                    s_mem.mean, s_mem.std, s_ins.mean, s_ins.std, s_con.mean, s_con.std
                )?;

                row_mem.push(fmt_stat(&s_mem));
                row_ins.push(fmt_stat(&s_ins));
                row_con.push(fmt_stat(&s_con));
            } else {
                for _ in 0..6 {
                    write!(csv_file, ",0,0")?;
                }
                row_mem.push("-".into());
                row_ins.push("-".into());
                row_con.push("-".into());
            }
        }
        writeln!(csv_file)?;

        mem_table_full.add_row(&row_mem);
        ins_table_full.add_row(&row_ins);
        con_table_full.add_row(&row_con);

        if is_target(density) {
            mem_table_short.add_row(row_mem);
            ins_table_short.add_row(row_ins);
            con_table_short.add_row(row_con);
        }
    }
    println!("CSV saved to benchmark_results.csv");

    let mut table_file = std::fs::File::create("BENCHMARK_TABLES.md")?;
    writeln!(table_file, "## Memory Usage (Bytes)\n\n{}", mem_table_full)?;
    writeln!(table_file, "\n## Insertion Time (ns)\n\n{}", ins_table_full)?;
    writeln!(table_file, "\n## Contains Time (ns)\n\n{}", con_table_full)?;
    println!("Markdown tables saved to BENCHMARK_TABLES.md");

    update_readme(
        &mem_table_short.to_string(),
        &ins_table_short.to_string(),
        &con_table_short.to_string(),
    )?;

    generate_plot(
        "memory_benchmark_linear.png",
        "Memory Usage Linear",
        "Memory (Bytes)",
        &densities,
        &results,
        |a, i| compute_stats(&a.steps[i].iter().map(|m| m.mem_size as f64).collect::<Vec<_>>()),
        false,
    )?;
    generate_plot(
        "memory_benchmark_log.png",
        "Memory Usage Log",
        "Memory (Bytes)",
        &densities,
        &results,
        |a, i| compute_stats(&a.steps[i].iter().map(|m| m.mem_size as f64).collect::<Vec<_>>()),
        true,
    )?;

    generate_plot(
        "insert_time_benchmark_linear.png",
        "Insertion Time Linear",
        "Time (ns)",
        &densities,
        &results,
        |a, i| {
            compute_stats(
                &a.steps[i].iter().map(|m| m.insert_time.as_nanos() as f64).collect::<Vec<_>>(),
            )
        },
        false,
    )?;
    generate_plot(
        "insert_time_benchmark_log.png",
        "Insertion Time Log",
        "Time (ns)",
        &densities,
        &results,
        |a, i| {
            compute_stats(
                &a.steps[i].iter().map(|m| m.insert_time.as_nanos() as f64).collect::<Vec<_>>(),
            )
        },
        true,
    )?;

    generate_plot(
        "contains_time_benchmark_linear.png",
        "Contains Time Linear",
        "Time (ns)",
        &densities,
        &results,
        |a, i| {
            compute_stats(
                &a.steps[i].iter().map(|m| m.contains_time.as_nanos() as f64).collect::<Vec<_>>(),
            )
        },
        false,
    )?;
    generate_plot(
        "contains_time_benchmark_log.png",
        "Contains Time Log",
        "Time (ns)",
        &densities,
        &results,
        |a, i| {
            compute_stats(
                &a.steps[i].iter().map(|m| m.contains_time.as_nanos() as f64).collect::<Vec<_>>(),
            )
        },
        true,
    )?;

    generate_plot(
        "insert_time_memory_product_linear.png",
        "Ins Time * Memory",
        "Product",
        &densities,
        &results,
        |a, i| {
            compute_stats(
                &a.steps[i]
                    .iter()
                    .map(|m| (m.insert_time.as_nanos() as f64) * (m.mem_size as f64))
                    .collect::<Vec<_>>(),
            )
        },
        false,
    )?;
    generate_plot(
        "insert_time_memory_product_log.png",
        "Ins Time * Memory Log",
        "Product",
        &densities,
        &results,
        |a, i| {
            compute_stats(
                &a.steps[i]
                    .iter()
                    .map(|m| (m.insert_time.as_nanos() as f64) * (m.mem_size as f64))
                    .collect::<Vec<_>>(),
            )
        },
        true,
    )?;
    generate_plot(
        "contains_time_memory_product_linear.png",
        "Con Time * Memory",
        "Product",
        &densities,
        &results,
        |a, i| {
            compute_stats(
                &a.steps[i]
                    .iter()
                    .map(|m| (m.contains_time.as_nanos() as f64) * (m.mem_size as f64))
                    .collect::<Vec<_>>(),
            )
        },
        false,
    )?;
    generate_plot(
        "contains_time_memory_product_log.png",
        "Con Time * Memory Log",
        "Product",
        &densities,
        &results,
        |a, i| {
            compute_stats(
                &a.steps[i]
                    .iter()
                    .map(|m| (m.contains_time.as_nanos() as f64) * (m.mem_size as f64))
                    .collect::<Vec<_>>(),
            )
        },
        true,
    )?;

    Ok(())
}

fn update_readme(mem_table: &str, ins_table: &str, con_table: &str) -> std::io::Result<()> {
    let path = "README.md";
    let content = std::fs::read_to_string(path)?;

    let mem_note = "\n**Note:** `MultiRange` shows higher standard deviation in memory usage because its capacity adapts to the number of disjoint ranges (fragmentation), which varies significantly with random input distribution at specific densities. `shrink_to_fit` is used to minimize footprint, reflecting this structural variance.\n\n";

    let mem_full = format!("{}{}", mem_note, mem_table);
    let ins_full = format!("\n{}", ins_table);
    let con_full = format!("\n{}", con_table);

    let replace_block =
        |source: &str, start_marker: &str, end_marker: &str, new_block: &str| -> String {
            if let Some(start_pos) = source.find(start_marker) {
                let after_start = start_pos + start_marker.len();
                if let Some(end_pos) = source[after_start..].find(end_marker) {
                    let absolute_end = after_start + end_pos;
                    return format!(
                        "{}{}\n\n{}\n\n{}",
                        &source[..after_start],
                        "",
                        new_block.trim(),
                        &source[absolute_end..]
                    );
                }
            }
            source.to_string()
        };

    let content = replace_block(&content, "### Memory Usage", "![Memory Usage]", &mem_full);
    let content = replace_block(&content, "### Insertion Time", "![Insertion Time]", &ins_full);
    let content = replace_block(&content, "### Contains Time", "![Contains Time]", &con_full);

    std::fs::write(path, content)?;
    println!("Updated README.md");
    Ok(())
}
