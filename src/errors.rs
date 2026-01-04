//! Submodule providing the errors which may occur when using the `Ranged`
//! trait.

use std::fmt::Display;

/// Error enumeration associated with the `Ranged` trait.
///
/// # Examples
///
/// ```
/// use multi_ranged::{MultiRanged, SimpleRange, errors::Error};
/// let mut range = SimpleRange::from(5);
/// let err = range.insert(5).unwrap_err();
/// assert!(matches!(err, Error::DuplicateElement(5)));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, thiserror::Error)]
pub enum Error<N: Display> {
    #[error("Element `{0}` is out of range")]
    /// The provided element cannot be added to the range.
    OutOfRange(N),
    #[error("Range is not dense")]
    /// The provided range is not dense.
    NotDense,
    #[error("Element `{0}` already exists in the range")]
    /// The provided element already exists in the range.
    DuplicateElement(N),
    #[error("Element `{0}` is not sorted correctly")]
    /// The provided element is not sorted correctly.
    NotSorted(N),
}
