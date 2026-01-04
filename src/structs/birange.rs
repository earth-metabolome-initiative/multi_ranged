//! Submodule providing the `BiRange` struct.

use std::ops::{Mul, MulAssign};

use super::SimpleRange;
use crate::{MultiRanged, Step, errors::Error};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// A struct representing a range which may be split into two parts.
///
/// # Examples
///
/// ```
/// use multi_ranged::{BiRange, MultiRanged};
/// # fn main() -> Result<(), multi_ranged::errors::Error<i32>> {
/// let mut range = BiRange::from(5);
/// range.insert(10)?;
/// assert!(range.contains(5));
/// assert!(range.contains(10));
/// # Ok(())
/// # }
/// ```
pub enum BiRange<N> {
    /// A single range.
    Single(SimpleRange<N>),
    /// A double range.
    Double(SimpleRange<N>, SimpleRange<N>),
}

impl<N: Step> MultiRanged for BiRange<N> {
    type Step = N;

    fn insert(&mut self, element: Self::Step) -> Result<(), Error<N>> {
        match self {
            Self::Single(range) => {
                if let Err(err) = range.insert(element) {
                    match err {
                        Error::OutOfRange(out_of_range_element) => {
                            // If the element is out of the range, we can split the range.
                            if out_of_range_element
                                < range.absolute_start().expect("Range must have a start")
                            {
                                *self = Self::Double(
                                    SimpleRange::try_from((
                                        out_of_range_element,
                                        out_of_range_element + Self::Step::ONE,
                                    ))?,
                                    range.clone(),
                                );
                            } else if out_of_range_element
                                >= range.absolute_end().expect("Range must have an end")
                            {
                                *self = Self::Double(
                                    range.clone(),
                                    SimpleRange::try_from((
                                        out_of_range_element,
                                        out_of_range_element + Self::Step::ONE,
                                    ))?,
                                );
                            }
                            Ok(())
                        }
                        err => {
                            // If the element is a duplicate or not sorted, we return the error.
                            Err(err)
                        }
                    }
                } else {
                    Ok(())
                }
            }
            Self::Double(left, right) => {
                left.insert(element).or_else(|_| right.insert(element))?;
                if left.absolute_end() == right.absolute_start() {
                    *self = Self::try_from((
                        left.absolute_start().expect("Range must have a start"),
                        right.absolute_end().expect("Range must have an end"),
                    ))?;
                }
                Ok(())
            }
        }
    }

    fn merge<Rhs: MultiRanged<Step = Self::Step>>(
        &mut self,
        other: &Rhs,
    ) -> Result<(), Error<Self::Step>> {
        match self {
            Self::Single(range) => {
                range.merge(other)?;
                Ok(())
            }
            Self::Double(left, right) => {
                let outcome = left.merge(other);
                if outcome.is_ok() || right.merge(other).is_ok() {
                    if left.absolute_end() == right.absolute_start() {
                        *self = Self::try_from((
                            left.absolute_start().expect("Range must have a start"),
                            right.absolute_end().expect("Range must have an end"),
                        ))?;
                    }
                    Ok(())
                } else {
                    outcome
                }
            }
        }
    }

    #[inline]
    fn absolute_start(&self) -> Option<Self::Step> {
        match self {
            Self::Single(range) => range.absolute_start(),
            Self::Double(left, _) => left.absolute_start(),
        }
    }

    #[inline]
    fn absolute_end(&self) -> Option<Self::Step> {
        match self {
            Self::Single(range) => range.absolute_end(),
            Self::Double(_, right) => right.absolute_end(),
        }
    }

    fn contains(&self, element: Self::Step) -> bool {
        match self {
            Self::Single(range) => range.contains(element),
            Self::Double(left, right) => left.contains(element) || right.contains(element),
        }
    }

    fn is_dense(&self) -> bool {
        match self {
            Self::Single(_) => true,
            Self::Double(_, _) => false,
        }
    }
}

impl<N: Step> Default for BiRange<N> {
    #[inline]
    fn default() -> Self {
        Self::Single(SimpleRange::default())
    }
}

impl<N: Step> Iterator for BiRange<N> {
    type Item = N;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Single(range) => range.next(),
            Self::Double(range1, range2) => range1.next().or_else(|| range2.next()),
        }
    }
}

impl<N: Step> DoubleEndedIterator for BiRange<N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            Self::Single(range) => range.next_back(),
            Self::Double(range1, range2) => range2.next_back().or_else(|| range1.next_back()),
        }
    }
}

impl<N: Step> ExactSizeIterator for BiRange<N> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            Self::Single(range) => range.len(),
            Self::Double(range1, range2) => range1.len() + range2.len(),
        }
    }
}

impl<N: Step> From<SimpleRange<N>> for BiRange<N> {
    #[inline]
    fn from(range: SimpleRange<N>) -> Self {
        Self::Single(range)
    }
}

impl<N: Step> TryFrom<(N, N)> for BiRange<N> {
    type Error = Error<N>;

    #[inline]
    fn try_from((start, end): (N, N)) -> Result<Self, Self::Error> {
        Ok(SimpleRange::try_from((start, end))?.into())
    }
}

impl<N: Step> TryFrom<&[N]> for BiRange<N> {
    type Error = Error<N>;

    fn try_from(slice: &[N]) -> Result<Self, Self::Error> {
        let mut birange = Self::default();
        for element in slice {
            birange.insert(*element)?;
        }
        Ok(birange)
    }
}

impl<N: Step> TryFrom<Vec<N>> for BiRange<N> {
    type Error = Error<N>;

    fn try_from(vec: Vec<N>) -> Result<Self, Self::Error> {
        Self::try_from(vec.as_slice())
    }
}

impl<N: Step> From<N> for BiRange<N> {
    #[inline]
    fn from(step: N) -> Self {
        Self::Single(SimpleRange::from(step))
    }
}

impl<N: Step> Mul<N> for BiRange<N> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: N) -> Self::Output {
        match self {
            Self::Single(range) => Self::Single(range * rhs),
            Self::Double(left, right) => Self::Double(left * rhs, right * rhs),
        }
    }
}

impl<N: Step> MulAssign<N> for BiRange<N> {
    #[inline]
    fn mul_assign(&mut self, rhs: N) {
        match self {
            Self::Single(range) => range.mul_assign(rhs),
            Self::Double(left, right) => {
                left.mul_assign(rhs);
                right.mul_assign(rhs);
            }
        }
    }
}

impl<N: Step> From<BiRange<N>> for Vec<N> {
    #[inline]
    fn from(multi_range: BiRange<N>) -> Self {
        let mut elements = Vec::new();
        for element in multi_range {
            elements.push(element);
        }
        elements
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert() -> Result<(), Error<i32>> {
        let mut range = BiRange::from(5);
        range.insert(6)?;
        assert!(range.contains(5));
        assert!(range.contains(6));
        assert!(range.is_dense());

        range.insert(10)?;
        assert!(range.contains(10));
        assert!(!range.is_dense());

        // Test inserting into Double range
        range.insert(11)?;
        assert!(range.contains(11));

        // Test inserting before start (split to Double)
        let mut range_split_before = BiRange::from(5);
        range_split_before.insert(1)?;
        assert!(range_split_before.contains(1));
        assert!(range_split_before.contains(5));
        assert!(!range_split_before.is_dense());

        // Test duplicate element
        let mut range_dup = BiRange::from(5);
        let err = range_dup.insert(5).unwrap_err();
        assert!(matches!(err, Error::DuplicateElement(5)));

        // Test merging Double back to Single
        let mut range = BiRange::try_from((1, 3))?; // [1, 2]
        range.insert(4)?; // [1, 2] and [4, 5]
        range.insert(3)?; // [1, 2, 3, 4, 5] -> [1, 6)
        assert!(range.is_dense());
        assert_eq!(range.absolute_start(), Some(1));
        assert_eq!(range.absolute_end(), Some(5));

        // Test insert failure in Double range
        let mut range_double_fail = BiRange::from(1);
        range_double_fail.insert(10)?;
        let err = range_double_fail.insert(5).unwrap_err();
        assert!(matches!(err, Error::OutOfRange(5)));

        Ok(())
    }

    #[test]
    fn test_merge() -> Result<(), Error<i32>> {
        let mut range1 = BiRange::from(5);
        let range2 = BiRange::from(6);
        range1.merge(&range2)?;
        assert!(range1.contains(5));
        assert!(range1.contains(6));
        assert!(range1.is_dense());

        let range3 = BiRange::from(10);
        range1.merge(&range3).unwrap_err(); // Should fail as it's not contiguous

        // But we can't easily create a Double range to test merge on it without insert
        // Let's try to merge into a Double range
        let mut range_double = BiRange::from(1);
        range_double.insert(10)?;
        assert!(!range_double.is_dense());

        let range_merge = BiRange::from(2);
        range_double.merge(&range_merge)?;
        assert!(range_double.contains(2));

        // Test merge failure in Double range
        let mut range_double_fail = BiRange::from(1);
        range_double_fail.insert(10)?;
        let range_fail = BiRange::from(5);
        let err = range_double_fail.merge(&range_fail).unwrap_err();
        assert!(matches!(err, Error::OutOfRange(_)));

        Ok(())
    }

    #[test]
    fn test_absolute_start_end() -> Result<(), Error<i32>> {
        let range = BiRange::from(5);
        assert_eq!(range.absolute_start(), Some(5));
        assert_eq!(range.absolute_end(), Some(6));

        let mut range_double = BiRange::from(1);
        range_double.insert(10)?;
        assert_eq!(range_double.absolute_start(), Some(1));
        assert_eq!(range_double.absolute_end(), Some(11));
        Ok(())
    }

    #[test]
    fn test_contains() -> Result<(), Error<i32>> {
        let mut range = BiRange::from(5);
        assert!(range.contains(5));
        assert!(!range.contains(6));

        range.insert(10)?;
        assert!(range.contains(5));
        assert!(range.contains(10));
        assert!(!range.contains(6));
        Ok(())
    }

    #[test]
    fn test_is_dense() -> Result<(), Error<i32>> {
        let mut range = BiRange::from(5);
        assert!(range.is_dense());

        range.insert(10)?;
        assert!(!range.is_dense());
        Ok(())
    }

    #[test]
    fn test_default() {
        let range: BiRange<i32> = BiRange::default();
        assert!(range.is_dense());
        assert_eq!(range.len(), 0);
    }

    #[test]
    fn test_iterator() -> Result<(), Error<i32>> {
        let mut range = BiRange::try_from((1, 3))?;
        assert_eq!(range.next(), Some(1));
        assert_eq!(range.next(), Some(2));
        assert_eq!(range.next(), None);

        let mut range_double = BiRange::from(1);
        range_double.insert(3)?;
        assert_eq!(range_double.next(), Some(1));
        assert_eq!(range_double.next(), Some(3));
        assert_eq!(range_double.next(), None);
        Ok(())
    }

    #[test]
    fn test_double_ended_iterator() -> Result<(), Error<i32>> {
        let mut range = BiRange::try_from((1, 3))?;
        assert_eq!(range.next_back(), Some(2));
        assert_eq!(range.next_back(), Some(1));
        assert_eq!(range.next_back(), None);

        let mut range_double = BiRange::from(1);
        range_double.insert(3)?;
        assert_eq!(range_double.next_back(), Some(3));
        assert_eq!(range_double.next_back(), Some(1));
        assert_eq!(range_double.next_back(), None);
        Ok(())
    }

    #[test]
    fn test_len() -> Result<(), Error<i32>> {
        let range = BiRange::try_from((1, 4))?;
        assert_eq!(range.len(), 3);

        let mut range_double = BiRange::from(1);
        range_double.insert(3)?;
        assert_eq!(range_double.len(), 2);
        Ok(())
    }

    #[test]
    fn test_from_simple_range() -> Result<(), Error<i32>> {
        let simple = SimpleRange::try_from((1, 3))?;
        let bi: BiRange<i32> = BiRange::from(simple);
        assert!(bi.is_dense());
        assert_eq!(bi.len(), 2);
        Ok(())
    }

    #[test]
    fn test_try_from_tuple() -> Result<(), Error<i32>> {
        let range = BiRange::try_from((1, 3))?;
        assert!(range.contains(1));
        assert!(range.contains(2));
        assert!(!range.contains(3));
        Ok(())
    }

    #[test]
    fn test_try_from_slice() -> Result<(), Error<i32>> {
        let slice = [1, 3, 4];
        let range = BiRange::try_from(&slice[..])?;
        assert!(range.contains(1));
        assert!(range.contains(3));
        assert!(range.contains(4));
        assert!(!range.contains(2));
        Ok(())
    }

    #[test]
    fn test_try_from_vec() -> Result<(), Error<i32>> {
        let vec = vec![1, 3, 4];
        let range = BiRange::try_from(vec)?;
        assert!(range.contains(1));
        assert!(range.contains(3));
        assert!(range.contains(4));
        Ok(())
    }

    #[test]
    fn test_from_step() {
        let range = BiRange::from(5);
        assert!(range.contains(5));
        assert_eq!(range.len(), 1);
    }

    #[test]
    fn test_mul() -> Result<(), Error<i32>> {
        let range = BiRange::try_from((1, 3))?;
        let scaled = range * 2;
        assert!(scaled.contains(2));
        assert!(scaled.contains(4));
        assert!(scaled.contains(3));

        let mut range_double = BiRange::from(1);
        range_double.insert(3)?;
        let scaled_double = range_double * 2;
        // [1, 2) -> [2, 3) (contains 2)
        // [3, 4) -> [6, 7) (contains 6)
        assert!(scaled_double.contains(2));
        assert!(scaled_double.contains(6));
        Ok(())
    }

    #[test]
    fn test_mul_assign() -> Result<(), Error<i32>> {
        let mut range = BiRange::try_from((1, 3))?;
        range *= 2;
        assert!(range.contains(2));
        assert!(range.contains(3));
        assert!(range.contains(4));

        let mut range_double = BiRange::from(1);
        range_double.insert(3)?;
        range_double *= 2;
        assert!(range_double.contains(2));
        assert!(range_double.contains(6));
        Ok(())
    }

    #[test]
    fn test_into_vec() -> Result<(), Error<i32>> {
        let mut range = BiRange::from(1);
        range.insert(3)?;
        let vec: Vec<i32> = range.into();
        assert_eq!(vec, vec![1, 3]);
        Ok(())
    }

    #[test]
    fn test_insert_gap() -> Result<(), Error<i32>> {
        // [1, 2) and [3, 4)
        let mut range = BiRange::from(1);
        range.insert(3)?;
        assert!(!range.is_dense());

        // Insert 2 to bridge the gap
        range.insert(2)?;
        assert!(range.is_dense());
        assert_eq!(range.len(), 3);
        assert!(range.contains(1));
        assert!(range.contains(2));
        assert!(range.contains(3));
        Ok(())
    }

    #[test]
    fn test_merge_gap() -> Result<(), Error<i32>> {
        // [1, 2) and [4, 5)
        let mut range = BiRange::from(1);
        range.insert(4)?;
        assert!(!range.is_dense());

        // Merge [2, 4) to bridge the gap
        let middle = SimpleRange::try_from((2, 4))?;
        range.merge(&middle)?;

        assert!(range.is_dense());
        assert_eq!(range.len(), 4);
        assert!(range.contains(1));
        assert!(range.contains(2));
        assert!(range.contains(3));
        assert!(range.contains(4));
        Ok(())
    }
}
