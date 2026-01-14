//! Submodule for honggfuzz fuzzing of multi_ranged crate

use honggfuzz::fuzz;
use multi_ranged::{MultiRange, MultiRanged};
use std::collections::HashSet;

fn main() {
    loop {
        fuzz!(|candidate: Vec<(u8, u16)>| {
            let mut range = MultiRange::<u16>::default();
            let mut oracle = HashSet::new();

            for (op, val_raw) in candidate {
                let val = u16::from(val_raw);
                match op % 3 {
                    0 => {
                        let _ = range.insert(val);
                        oracle.insert(val);
                    }
                    1 => {
                        // Merge a randomly constructed range
                        let len = ((usize::from(op) >> 8) as u16) % 16 + 1;
                        let end = val.saturating_add(len);
                        
                        // Build the range to merge
                        let mut other = MultiRange::<u16>::default();
                        for i in val..end {
                            let _ = other.insert(i);
                            oracle.insert(i);
                        }
                        
                        let _ = range.merge(&other);
                    }
                    2 => {
                        // Check consistency for a specific value
                        assert_eq!(range.contains(val), oracle.contains(&val), 
                            "Mismatch for value {}. Range: {:?}, Oracle: {:?}", val, range, oracle);
                    }
                    _ => unreachable!(),
                }
            }

            // Full consistency check at the end
            for i in 0..=255 {
                assert_eq!(range.contains(i), oracle.contains(&i),
                    "Final mismatch for value {}. Range: {:?}, Oracle: {:?}", i, range, oracle);
            }
        });
    }
}
