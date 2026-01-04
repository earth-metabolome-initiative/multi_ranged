//! Multiple disjoint ranges implementation.

use std::ops::{Mul, MulAssign};

use super::SimpleRange;
use crate::{MultiRanged, Step, errors::Error};

/// A collection of disjoint ranges that can be built incrementally.
///
/// # Examples
///
/// ```
/// use multi_ranged::{MultiRange, MultiRanged};
/// # fn main() -> Result<(), multi_ranged::errors::Error<i32>> {
/// let mut range = MultiRange::default();
/// range.insert(1)?;
/// range.insert(5)?;
/// range.insert(10)?;
/// assert!(range.contains(1));
/// assert!(range.contains(5));
/// assert!(range.contains(10));
/// # Ok(())
/// # }
/// ```
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MultiRange<N> {
    /// A vector of `SimpleRange` instances.
    ranges: Vec<SimpleRange<N>>,
}

impl<N: Step> MultiRanged for MultiRange<N> {
    type Step = N;

    #[inline]
    fn insert(&mut self, element: Self::Step) -> Result<(), Error<N>> {
        if self.ranges.is_empty() {
            // If there are no ranges, create a new one with the element.
            self.ranges.push(SimpleRange::from(element));
            return Ok(());
        }

        match self.ranges.binary_search_by(|probe| {
            let absolute_start = probe.absolute_start().expect("Range must have a start").prev();
            let absolute_end = probe.absolute_end().expect("Range must have an end");
            if element < absolute_start {
                std::cmp::Ordering::Greater
            } else if element > absolute_end {
                std::cmp::Ordering::Less
            } else {
                std::cmp::Ordering::Equal
            }
        }) {
            Ok(mut index) => {
                let _ = self.ranges[index].insert(element);

                // We check whether inserting this element has now merged two ranges.
                if index > 0
                    && self.ranges[index - 1].absolute_end() == self.ranges[index].absolute_start()
                {
                    // Merge with the previous range.
                    let merged_range = self.ranges.remove(index);
                    self.ranges[index - 1].merge(&merged_range)?;
                    index -= 1; // Adjust index after removal.
                }
                if index < self.ranges.len() - 1
                    && self.ranges[index + 1].absolute_start() == self.ranges[index].absolute_end()
                {
                    // Merge with the next range.
                    let merged_range = self.ranges.remove(index + 1);
                    self.ranges[index].merge(&merged_range)?;
                }
            }
            Err(index) => {
                self.ranges.insert(index, SimpleRange::from(element));
            }
        }

        Ok(())
    }

    fn merge<Rhs: MultiRanged<Step = Self::Step>>(
        &mut self,
        _other: &Rhs,
    ) -> Result<(), Error<Self::Step>> {
        todo!("Merging MultiRange is not implemented yet");
    }

    #[inline]
    fn absolute_start(&self) -> Option<Self::Step> {
        self.ranges.first().and_then(MultiRanged::absolute_start)
    }

    #[inline]
    fn absolute_end(&self) -> Option<Self::Step> {
        self.ranges.last().and_then(MultiRanged::absolute_end)
    }

    #[inline]
    fn contains(&self, element: Self::Step) -> bool {
        self.ranges.iter().any(|range| range.contains(element))
    }

    #[inline]
    fn is_dense(&self) -> bool {
        self.ranges.len() == 1
    }
}

impl<N: Step> Default for MultiRange<N> {
    #[inline]
    fn default() -> Self {
        Self { ranges: Vec::new() }
    }
}

impl<N: Step> Iterator for MultiRange<N> {
    type Item = N;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let first_range = self.ranges.first_mut()?;
        first_range.next().or_else(|| {
            // If the first range is exhausted, remove it and try the next one.
            self.ranges.remove(0);
            self.next()
        })
    }
}

impl<N: Step> DoubleEndedIterator for MultiRange<N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let last_range = self.ranges.last_mut()?;
        last_range.next_back().or_else(|| {
            // If the last range is exhausted, remove it and try the next one.
            self.ranges.pop();
            self.next_back()
        })
    }
}

impl<N: Step> ExactSizeIterator for MultiRange<N> {
    #[inline]
    fn len(&self) -> usize {
        self.ranges.iter().map(ExactSizeIterator::len).sum()
    }
}

impl<N: Step> From<SimpleRange<N>> for MultiRange<N> {
    #[inline]
    fn from(range: SimpleRange<N>) -> Self {
        if range.len() == 0 {
            return Self::default();
        }

        Self { ranges: vec![range] }
    }
}

impl<N: Step> TryFrom<(N, N)> for MultiRange<N> {
    type Error = Error<N>;

    #[inline]
    fn try_from((start, end): (N, N)) -> Result<Self, Self::Error> {
        Ok(SimpleRange::try_from((start, end))?.into())
    }
}

impl<N: Step> TryFrom<&[N]> for MultiRange<N> {
    type Error = Error<N>;

    fn try_from(slice: &[N]) -> Result<Self, Self::Error> {
        let mut multi_range = Self::default();
        for element in slice {
            multi_range.insert(*element)?;
        }
        Ok(multi_range)
    }
}

impl<N: Step> TryFrom<Vec<N>> for MultiRange<N> {
    type Error = Error<N>;

    fn try_from(vec: Vec<N>) -> Result<Self, Self::Error> {
        Self::try_from(vec.as_slice())
    }
}

impl<N: Step, const L: usize> TryFrom<[N; L]> for MultiRange<N> {
    type Error = Error<N>;

    fn try_from(array: [N; L]) -> Result<Self, Self::Error> {
        Self::try_from(array.as_slice())
    }
}

impl<N: Step> From<N> for MultiRange<N> {
    #[inline]
    fn from(element: N) -> Self {
        Self::from(SimpleRange::from(element))
    }
}

impl<N: Step> Mul<N> for MultiRange<N> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: N) -> Self::Output {
        Self { ranges: self.ranges.into_iter().map(|range| range * rhs).collect() }
    }
}

impl<N: Step> MulAssign<N> for MultiRange<N> {
    #[inline]
    fn mul_assign(&mut self, rhs: N) {
        for range in &mut self.ranges {
            *range *= rhs;
        }
    }
}

impl<N: Step> MultiRange<N> {
    #[inline]
    /// Computes the multiplication of all elements in the `MultiRange` by a
    /// given factor, checking for overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use multi_ranged::{MultiRange, MultiRanged};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut range = MultiRange::default();
    /// range.insert(1)?;
    /// range.insert(3)?;
    /// let scaled = range.checked_mul(2).ok_or("overflow")?;
    /// assert!(scaled.contains(2));
    /// assert!(scaled.contains(6));
    /// # Ok(())
    /// # }
    /// ```
    pub fn checked_mul(&self, factor: N) -> Option<Self> {
        let mut new_ranges = Vec::with_capacity(self.ranges.len());
        for range in &self.ranges {
            new_ranges.push(range.checked_mul(factor)?);
        }
        Some(Self { ranges: new_ranges })
    }
}

impl<N: Step> From<MultiRange<N>> for Vec<N> {
    #[inline]
    fn from(multi_range: MultiRange<N>) -> Self {
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
        let mut range = MultiRange::default();
        range.insert(1)?;
        range.insert(3)?;
        range.insert(5)?;
        assert!(range.contains(1));
        assert!(range.contains(3));
        assert!(range.contains(5));
        assert!(!range.contains(2));
        assert!(!range.contains(4));
        assert_eq!(range.len(), 3);

        // Insert to merge
        range.insert(2)?; // Merges 1 and 3 -> [1, 2, 3] (which is [1, 4))
        assert!(range.contains(2));
        // Check if merged: [1, 4), [5, 6)
        // 1, 2, 3 are in first range. 5 is in second.

        range.insert(4)?; // Merges [1, 4) and [5, 6) -> [1, 6)
        assert!(range.contains(4));
        assert!(range.is_dense());
        assert_eq!(range.len(), 5);
        assert_eq!(range.absolute_start(), Some(1));
        assert_eq!(range.absolute_end(), Some(6));

        // Test inserting disjoint ranges explicitly to cover binary_search Err branches
        let mut range_disjoint = MultiRange::default();
        range_disjoint.insert(10)?; // Err(0) -> insert at 0
        range_disjoint.insert(1)?; // Err(0) -> insert at 0 (10 becomes index 1)
        range_disjoint.insert(20)?; // Err(2) -> insert at 2

        // Check order
        let vec: Vec<i32> = range_disjoint.into();
        assert_eq!(vec, vec![1, 10, 20]);

        Ok(())
    }

    #[test]
    #[should_panic(expected = "Merging MultiRange is not implemented yet")]
    fn test_merge() {
        let mut range1 = MultiRange::from(1);
        let range2 = MultiRange::from(2);
        let _ = range1.merge(&range2);
    }

    #[test]
    fn test_absolute_start_end() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        assert_eq!(range.absolute_start(), None);
        assert_eq!(range.absolute_end(), None);

        range.insert(5)?;
        assert_eq!(range.absolute_start(), Some(5));
        assert_eq!(range.absolute_end(), Some(6));

        range.insert(1)?;
        assert_eq!(range.absolute_start(), Some(1));
        assert_eq!(range.absolute_end(), Some(6));

        range.insert(10)?;
        assert_eq!(range.absolute_start(), Some(1));
        assert_eq!(range.absolute_end(), Some(11));
        Ok(())
    }

    #[test]
    fn test_contains() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        range.insert(1)?;
        range.insert(3)?;
        assert!(range.contains(1));
        assert!(range.contains(3));
        assert!(!range.contains(2));
        Ok(())
    }

    #[test]
    fn test_is_dense() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        // Empty range is not dense? Implementation: ranges.len() == 1.
        // If empty, len is 0. So false.
        assert!(!range.is_dense());

        range.insert(1)?;
        assert!(range.is_dense());

        range.insert(3)?;
        assert!(!range.is_dense());
        Ok(())
    }

    #[test]
    fn test_default() {
        let range: MultiRange<i32> = MultiRange::default();
        assert_eq!(range.len(), 0);
    }

    #[test]
    fn test_iterator() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        range.insert(1)?;
        range.insert(3)?;
        assert_eq!(range.next(), Some(1));
        assert_eq!(range.next(), Some(3));
        assert_eq!(range.next(), None);
        Ok(())
    }

    #[test]
    fn test_double_ended_iterator() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        range.insert(1)?;
        range.insert(3)?;
        assert_eq!(range.next_back(), Some(3));
        assert_eq!(range.next_back(), Some(1));
        assert_eq!(range.next_back(), None);
        Ok(())
    }

    #[test]
    fn test_len() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        range.insert(1)?;
        range.insert(3)?;
        assert_eq!(range.len(), 2);
        Ok(())
    }

    #[test]
    fn test_from_simple_range() -> Result<(), Error<i32>> {
        let simple = SimpleRange::try_from((1, 3))?;
        let multi = MultiRange::from(simple);
        assert_eq!(multi.len(), 2);
        assert!(multi.is_dense());

        let empty_simple: SimpleRange<i32> = SimpleRange::default();
        let empty_multi = MultiRange::from(empty_simple);
        assert_eq!(empty_multi.len(), 0);
        Ok(())
    }

    #[test]
    fn test_try_from_tuple() -> Result<(), Error<i32>> {
        let range = MultiRange::try_from((1, 3))?;
        assert!(range.contains(1));
        assert!(range.contains(2));
        Ok(())
    }

    #[test]
    fn test_try_from_slice() -> Result<(), Error<i32>> {
        let slice = [1, 3, 5];
        let range = MultiRange::try_from(&slice[..])?;
        assert!(range.contains(1));
        assert!(range.contains(3));
        assert!(range.contains(5));
        assert!(!range.contains(2));
        Ok(())
    }

    #[test]
    fn test_try_from_vec() -> Result<(), Error<i32>> {
        let vec = vec![1, 3, 5];
        let range = MultiRange::try_from(vec)?;
        assert!(range.contains(1));
        assert!(range.contains(3));
        assert!(range.contains(5));
        Ok(())
    }

    #[test]
    fn test_try_from_array() -> Result<(), Error<i32>> {
        let array = [1, 3, 5];
        let range = MultiRange::try_from(array)?;
        assert!(range.contains(1));
        assert!(range.contains(3));
        assert!(range.contains(5));
        Ok(())
    }

    #[test]
    fn test_from_element() {
        let range = MultiRange::from(5);
        assert!(range.contains(5));
        assert_eq!(range.len(), 1);
    }

    #[test]
    fn test_mul() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        range.insert(1)?;
        range.insert(3)?;
        let scaled = range * 2;
        // 1 -> [2, 3) (contains 2)
        // 3 -> [6, 7) (contains 6)
        assert!(scaled.contains(2));
        assert!(scaled.contains(6));
        assert!(!scaled.contains(4));
        Ok(())
    }

    #[test]
    fn test_mul_assign() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        range.insert(1)?;
        range.insert(3)?;
        range *= 2;
        assert!(range.contains(2));
        assert!(range.contains(6));
        Ok(())
    }

    #[test]
    fn test_checked_mul() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        range.insert(1)?;
        range.insert(3)?;
        let scaled = range.checked_mul(2).unwrap();
        assert!(scaled.contains(2));
        assert!(scaled.contains(6));
        Ok(())
    }

    #[test]
    fn test_into_vec() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        range.insert(1)?;
        range.insert(3)?;
        let vec: Vec<i32> = range.into();
        assert_eq!(vec, vec![1, 3]);
        Ok(())
    }

    #[test]
    fn test_insert_merge_next() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        // [1, 2)
        range.insert(1)?;
        // [3, 4)
        range.insert(3)?;

        assert_eq!(range.ranges.len(), 2);

        // Insert 2, which should merge [1, 2) and [3, 4) into [1, 4)
        range.insert(2)?;

        assert_eq!(range.ranges.len(), 1);
        assert!(range.contains(1));
        assert!(range.contains(2));
        assert!(range.contains(3));
        assert_eq!(range.absolute_start(), Some(1));
        assert_eq!(range.absolute_end(), Some(4));
        Ok(())
    }

    #[test]
    fn test_insert_merge_next_middle() -> Result<(), Error<i32>> {
        let mut range = MultiRange::default();
        range.insert(1)?; // [1, 2)
        range.insert(3)?; // [3, 4)
        range.insert(5)?; // [5, 6)

        range.insert(4)?;

        assert_eq!(range.ranges.len(), 2);
        assert!(range.contains(1));
        assert!(range.contains(3));
        assert!(range.contains(4));
        assert!(range.contains(5));

        // ranges[0] is [1, 2)
        // ranges[1] is [3, 6)
        assert!(!range.contains(2));

        Ok(())
    }
}
