//! Common trait for range types.

use std::ops::{Mul, MulAssign};

use crate::{Step, errors::Error};

/// Common interface for range data structures.
pub trait MultiRanged:
    core::fmt::Debug
    + Clone
    + Default
    + ExactSizeIterator<Item = <Self as MultiRanged>::Step>
    + DoubleEndedIterator<Item = <Self as MultiRanged>::Step>
    + Mul<Self::Step, Output = Self>
    + MulAssign<Self::Step>
    + TryFrom<(Self::Step, Self::Step), Error = Error<Self::Step>>
    + From<Self::Step>
    + 'static
{
    /// The type of the elements in the range.
    type Step: Step;

    /// Inserts an element into the range.
    ///
    /// # Examples
    ///
    /// ```
    /// use multi_ranged::{MultiRanged, SimpleRange};
    /// # fn main() -> Result<(), multi_ranged::errors::Error<i32>> {
    /// let mut range = SimpleRange::default();
    /// range.insert(5)?;
    /// assert!(range.contains(5));
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if the element cannot be added or already exists.
    fn insert(&mut self, element: Self::Step) -> Result<(), Error<Self::Step>>;

    /// Merges another range into this one.
    ///
    /// # Examples
    ///
    /// ```
    /// use multi_ranged::{MultiRanged, SimpleRange};
    /// # fn main() -> Result<(), multi_ranged::errors::Error<i32>> {
    /// let mut range1 = SimpleRange::from(5);
    /// let range2 = SimpleRange::from(6);
    /// range1.merge(&range2)?;
    /// assert!(range1.contains(5));
    /// assert!(range1.contains(6));
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if the ranges cannot be merged.
    fn merge<Rhs: MultiRanged<Step = Self::Step>>(
        &mut self,
        other: &Rhs,
    ) -> Result<(), Error<Self::Step>>;

    /// Returns whether the element is in the range.
    ///
    /// # Examples
    ///
    /// ```
    /// use multi_ranged::{MultiRanged, SimpleRange};
    /// let range = SimpleRange::from(5);
    /// assert!(range.contains(5));
    /// assert!(!range.contains(6));
    /// ```
    fn contains(&self, element: Self::Step) -> bool;

    /// Returns the start of the range, if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use multi_ranged::{MultiRanged, SimpleRange};
    /// let range = SimpleRange::from(5);
    /// assert_eq!(range.absolute_start(), Some(5));
    /// ```
    fn absolute_start(&self) -> Option<Self::Step>;

    /// Returns the end of the range, if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use multi_ranged::{MultiRanged, SimpleRange};
    /// let range = SimpleRange::from(5);
    /// assert_eq!(range.absolute_end(), Some(6));
    /// ```
    fn absolute_end(&self) -> Option<Self::Step>;

    /// Returns whether the range is contiguous (not split).
    ///
    /// # Examples
    ///
    /// ```
    /// use multi_ranged::{MultiRanged, SimpleRange};
    /// let range = SimpleRange::from(5);
    /// assert!(range.is_dense());
    /// ```
    fn is_dense(&self) -> bool;
}
