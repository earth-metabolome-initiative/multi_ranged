# Multi Ranged

[![CI](https://github.com/earth-metabolome-initiative/multi_ranged/workflows/Rust%20CI/badge.svg)](https://github.com/earth-metabolome-initiative/multi_ranged/actions)
[![Security Audit](https://github.com/earth-metabolome-initiative/multi_ranged/workflows/Security%20Audit/badge.svg)](https://github.com/earth-metabolome-initiative/multi_ranged/actions)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Codecov](https://codecov.io/gh/earth-metabolome-initiative/multi_ranged/branch/main/graph/badge.svg)](https://codecov.io/gh/earth-metabolome-initiative/multi_ranged)
[![Crates.io](https://img.shields.io/crates/v/multi_ranged.svg)](https://crates.io/crates/multi_ranged)
[![Docs.rs](https://docs.rs/multi_ranged/badge.svg)](https://docs.rs/multi_ranged)

Efficient data structures for representing and manipulating ranges of discrete values. The crate provides three range types with a unified [`MultiRanged`](https://docs.rs/multi_ranged/latest/multi_ranged/multi_ranged/trait.MultiRanged.html) trait: [`SimpleRange`](https://docs.rs/multi_ranged/latest/multi_ranged/structs/simple_range/struct.SimpleRange.html) for contiguous ranges similar to Rust's [`std::ops::Range`](https://doc.rust-lang.org/std/ops/struct.Range.html) but with stable semantics, [`BiRange`](https://docs.rs/multi_ranged/latest/multi_ranged/structs/birange/enum.BiRange.html) for ranges split into two parts, and [`MultiRange`](https://docs.rs/multi_ranged/latest/multi_ranged/structs/multi_range/struct.MultiRange.html) for arbitrary collections of disjoint ranges. All types support incremental insertion, merging, and efficient iteration over their elements. The [`Step`](https://docs.rs/multi_ranged/latest/multi_ranged/step/trait.Step.html) trait abstracts over numeric types that can be used as range boundaries, providing operations for stepping forward and backward with [saturating arithmetic](https://en.wikipedia.org/wiki/Saturation_arithmetic).

## Examples

### Simple Range

A contiguous range from start to end. See [`SimpleRange`](https://docs.rs/multi_ranged/latest/multi_ranged/structs/simple_range/struct.SimpleRange.html) for more details.

```rust
use multi_ranged::{SimpleRange, MultiRanged};

// Create a range [0, 10)
let mut range = SimpleRange::try_from((0, 10))?;
assert_eq!(range.len(), 10);
assert!(range.contains(5));
assert!(!range.contains(15));

// Extend the range to [0, 11)
range.insert(10)?;
assert_eq!(range.len(), 11);
# Ok::<(), multi_ranged::errors::Error<i32>>(())
```

### Bi Range

A range that can be split into at most two non-contiguous parts. See [`BiRange`](https://docs.rs/multi_ranged/latest/multi_ranged/structs/birange/enum.BiRange.html) for more details.

```rust
use multi_ranged::{BiRange, MultiRanged};

// Create a BiRange from a slice of integers.
// This creates two disjoint ranges: [1, 3) and [5, 7).
let mut range = BiRange::try_from([1, 2, 5, 6])?;
assert!(!range.is_dense());
assert_eq!(range.len(), 4);

// Insert a value that bridges the gap.
range.insert(3)?; // Now we have [1, 4) and [5, 7)
range.insert(4)?; // Now we have [1, 7)

assert!(range.is_dense());
assert_eq!(range.absolute_start(), Some(1));
assert_eq!(range.absolute_end(), Some(7));
# Ok::<(), multi_ranged::errors::Error<i32>>(())
```

### Multi Range

Multiple disjoint ranges that can be built incrementally. See [`MultiRange`](https://docs.rs/multi_ranged/latest/multi_ranged/structs/multi_range/struct.MultiRange.html) for more details.

```rust
use multi_ranged::{MultiRange, MultiRanged};

// Create a MultiRange from a slice of integers.
// This creates two disjoint ranges: [1, 4) and [10, 13).
let mut range = MultiRange::try_from([1, 2, 3, 10, 11, 12])?;
assert!(!range.is_dense());

// Insert values that bridge the gap between [1, 4) and [10, 13).
range.insert(4)?; // Now we have [1, 5) and [10, 13)
range.insert(5)?; // Now we have [1, 6) and [10, 13)
range.insert(6)?; // Now we have [1, 7) and [10, 13)
range.insert(7)?; // Now we have [1, 8) and [10, 13)
range.insert(8)?; // Now we have [1, 9) and [10, 13)
range.insert(9)?; // Now we have [1, 13)

// The ranges have merged into a single contiguous range: [1, 13).
assert!(range.is_dense());
assert_eq!(range.absolute_start(), Some(1));
assert_eq!(range.absolute_end(), Some(13));
# Ok::<(), multi_ranged::errors::Error<i32>>(())
```

## Trait Overview

The [`MultiRanged`](https://docs.rs/multi_ranged/latest/multi_ranged/multi_ranged/trait.MultiRanged.html) trait provides a common interface for all range types with methods for insertion, merging, containment checking, and iteration. The [`Step`](https://docs.rs/multi_ranged/latest/multi_ranged/step/trait.Step.html) trait enables generic range operations over any numeric type supporting saturating arithmetic and ordering.
