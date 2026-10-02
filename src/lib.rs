#![doc = include_str!("../README.md")]
#![no_std]

extern crate alloc;

pub mod errors;
pub mod multi_ranged;
pub use multi_ranged::MultiRanged;
pub mod structs;
pub use structs::{BiRange, MultiRange, SimpleRange};
pub mod step;
pub use step::Step;
