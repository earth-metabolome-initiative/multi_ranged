//! Contiguous range implementation.

use alloc::vec::Vec;
#[cfg(feature = "mem_dbg")]
#[allow(unused_imports)]
use alloc::{string::String, vec};
use core::ops::{Mul, MulAssign};

use crate::{MultiRanged, Step, errors::Error};

/// A contiguous range from start to end (inclusive).
///
/// # Examples
///
/// ```
/// use multi_ranged::{MultiRanged, SimpleRange};
/// let range = SimpleRange::from(5);
/// assert!(range.contains(5));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "mem_dbg", derive(mem_dbg::MemSize, mem_dbg::MemDbg), mem_size(flat))]
pub struct SimpleRange<N> {
    /// The start of the range.
    start: N,
    /// The end of the range.
    end: N,
}

impl<N> MultiRanged for SimpleRange<N>
where
    N: Step,
{
    type Step = N;

    fn insert(&mut self, element: Self::Step) -> Result<(), Error<N>> {
        if self.contains(element) {
            return Err(Error::DuplicateElement(element));
        }

        // If the range is currently completely empty,
        // we need to set the start and end relative to the element.
        if self.start > self.end {
            self.start = element;
            self.end = element;
            Ok(())
        } else if element < self.start && element.next() == self.start {
            self.start = element;
            Ok(())
        } else if element > self.end && self.end.next() == element {
            self.end = element;
            Ok(())
        } else {
            Err(Error::OutOfRange(element))
        }
    }

    fn merge<Rhs: MultiRanged<Step = Self::Step>>(
        &mut self,
        other: &Rhs,
    ) -> Result<(), Error<Self::Step>> {
        if other.len() == 0 {
            return Ok(());
        }
        if !other.is_dense() {
            return Err(Error::NotDense);
        }
        if self.len() == 0 {
            self.start = other.absolute_start().unwrap_or(self.start);
            self.end = other.absolute_end().unwrap_or(self.end);
            return Ok(());
        }

        let other_start = other.absolute_start().unwrap();
        let other_end = other.absolute_end().unwrap();

        // Check if overlapping or adjacent (inclusive)
        // Connected if max(starts) <= min(ends) + 1 if we consider adjacency.
        // Or simply:
        // Overlap: s1 <= e2 && s2 <= e1
        // Adjacent: e1+1 == s2 || e2+1 == s1
        // Combined: s1 <= e2+1 && s2 <= e1+1

        let s1 = self.start;
        let e1 = self.end;
        let s2 = other_start;
        let e2 = other_end;

        // Use saturating add for checking adjacency
        let connected = (s1 <= e2.saturating_add(&N::ONE)) && (s2 <= e1.saturating_add(&N::ONE));

        if connected {
            self.start = s1.min(s2);
            self.end = e1.max(e2);
            Ok(())
        } else {
            Err(Error::OutOfRange(other_start))
        }
    }

    #[inline]
    fn absolute_start(&self) -> Option<Self::Step> {
        if self.start <= self.end { Some(self.start) } else { None }
    }

    #[inline]
    fn absolute_end(&self) -> Option<Self::Step> {
        if self.start <= self.end { Some(self.end) } else { None }
    }

    fn contains(&self, element: Self::Step) -> bool {
        element >= self.start && element <= self.end && self.start <= self.end
    }

    fn is_dense(&self) -> bool {
        true
    }
}

impl<N: Step> Default for SimpleRange<N> {
    #[inline]
    fn default() -> Self {
        // Empty state: start > end
        Self { start: N::ONE, end: N::ZERO }
    }
}

impl<N: Step> Iterator for SimpleRange<N> {
    type Item = N;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start <= self.end {
            let current = self.start;
            if self.start == self.end {
                // Determine it becomes empty
                self.start = N::ONE;
                self.end = N::ZERO;
            } else {
                self.start = self.start.next();
            }
            Some(current)
        } else {
            None
        }
    }
}

impl<N: Step> DoubleEndedIterator for SimpleRange<N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start <= self.end {
            let current = self.end;
            if self.start == self.end {
                self.start = N::ONE;
                self.end = N::ZERO;
            } else {
                self.end = self.end.prev();
            }
            Some(current)
        } else {
            None
        }
    }
}

impl<N: Step> ExactSizeIterator for SimpleRange<N> {
    #[inline]
    fn len(&self) -> usize {
        if self.start > self.end {
            0
        } else {
            (self.end - self.start)
                .to_usize()
                .map(|x| x + 1)
                .expect("Step type should implement ToPrimitive")
        }
    }
}

impl<N: Step> TryFrom<(N, N)> for SimpleRange<N> {
    type Error = Error<N>;

    fn try_from((start, end): (N, N)) -> Result<Self, Self::Error> {
        if start > end { Err(Error::OutOfRange(start)) } else { Ok(Self { start, end }) }
    }
}

impl<N: Step> TryFrom<&[N]> for SimpleRange<N> {
    type Error = Error<N>;

    fn try_from(slice: &[N]) -> Result<Self, Self::Error> {
        slice.windows(2).try_for_each(|window| {
            if window[0] >= window[1] {
                return Err(Error::NotSorted(window[0]));
            }
            Ok(())
        })?;
        let start = slice[0];
        let end = slice[slice.len() - 1];
        SimpleRange::try_from((start, end))
    }
}

impl<N: Step> TryFrom<Vec<N>> for SimpleRange<N> {
    type Error = Error<N>;

    fn try_from(vec: Vec<N>) -> Result<Self, Self::Error> {
        Self::try_from(vec.as_slice())
    }
}

impl<N: Step> From<N> for SimpleRange<N> {
    #[inline]
    fn from(element: N) -> Self {
        Self { start: element, end: element }
    }
}

impl<N: Step> Mul<N> for SimpleRange<N> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: N) -> Self::Output {
        Self { start: self.start * rhs, end: self.end * rhs }
    }
}

impl<N: Step> MulAssign<N> for SimpleRange<N> {
    #[inline]
    fn mul_assign(&mut self, rhs: N) {
        self.start *= rhs;
        self.end *= rhs;
    }
}

impl<N: Step> SimpleRange<N> {
    #[inline]
    /// Computes the multiplication of all elements in the `SimpleRange` by a
    /// given factor, checking for overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use multi_ranged::{MultiRanged, SimpleRange};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let range = SimpleRange::try_from((1, 3))?;
    /// let scaled = range.checked_mul(2).ok_or("overflow")?;
    /// assert_eq!(scaled.absolute_start(), Some(2));
    /// assert_eq!(scaled.absolute_end(), Some(6));
    /// # Ok(())
    /// # }
    /// ```
    pub fn checked_mul(&self, factor: N) -> Option<Self> {
        let start = self.start.checked_mul(&factor)?;
        let end = self.end.checked_mul(&factor)?;
        Some(Self { start, end })
    }
}

impl<N: Step> From<SimpleRange<N>> for (N, N) {
    #[inline]
    fn from(range: SimpleRange<N>) -> Self {
        (range.start, range.end)
    }
}

impl<N: Step> From<SimpleRange<N>> for Vec<N> {
    #[inline]
    fn from(range: SimpleRange<N>) -> Self {
        let mut vec = Vec::with_capacity(range.len());
        for element in range {
            vec.push(element);
        }
        vec
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;

    #[test]
    fn test_insert() -> Result<(), Error<i32>> {
        let mut range = SimpleRange::default();
        range.insert(5)?;
        assert!(range.contains(5));
        assert_eq!(range.len(), 1);

        range.insert(6)?;
        assert!(range.contains(6));
        assert_eq!(range.len(), 2);

        range.insert(4)?;
        assert!(range.contains(4));
        assert_eq!(range.len(), 3);

        // Duplicate
        let err = range.insert(5).unwrap_err();
        assert!(matches!(err, Error::DuplicateElement(5)));

        // Out of range (not contiguous)
        let err = range.insert(8).unwrap_err();
        assert!(matches!(err, Error::OutOfRange(8)));

        Ok(())
    }

    #[test]
    fn test_merge() -> Result<(), Error<i32>> {
        let mut range1 = SimpleRange::from(5);
        let range2 = SimpleRange::from(6);
        range1.merge(&range2)?;
        assert!(range1.contains(5));
        assert!(range1.contains(6));
        assert_eq!(range1.len(), 2);

        let range3 = SimpleRange::from(4);
        range1.merge(&range3)?;
        assert!(range1.contains(4));
        assert_eq!(range1.len(), 3);

        // Merge overlapping
        let range4 = SimpleRange::try_from((5, 7))?; // [5, 7] inclusive
        range1.merge(&range4)?;
        assert_eq!(range1.len(), 4); // 4, 5, 6, 7 (4 from range1, 5,6 overlap, 7 from range4)
        assert!(range1.contains(7));

        // Merge disjoint
        let range5 = SimpleRange::from(10);
        let err = range1.merge(&range5).unwrap_err();
        assert!(matches!(err, Error::OutOfRange(10)));

        // Merge adjacent
        let range_adj = SimpleRange::from(8);
        range1.merge(&range_adj)?;
        assert_eq!(range1.len(), 5);

        // Merge empty
        let range_empty = SimpleRange::default();
        range1.merge(&range_empty)?;
        assert_eq!(range1.len(), 5);

        // Merge into empty
        let mut range_empty_dest = SimpleRange::default();
        range_empty_dest.merge(&range1)?;
        assert_eq!(range_empty_dest.len(), 5);
        assert!(range_empty_dest.contains(4));

        Ok(())
    }

    #[test]
    fn test_merge_not_dense() -> Result<(), Error<i32>> {
        use crate::MultiRange;
        let mut range = SimpleRange::from(1);
        let mut multi = MultiRange::default();
        multi.insert(3)?;
        multi.insert(5)?; // Not dense

        let err = range.merge(&multi).unwrap_err();
        assert!(matches!(err, Error::NotDense));
        Ok(())
    }

    #[test]
    fn test_absolute_start_end() -> Result<(), Error<i32>> {
        let range = SimpleRange::try_from((1, 4))?;
        assert_eq!(range.absolute_start(), Some(1));
        assert_eq!(range.absolute_end(), Some(4));

        let empty: SimpleRange<i32> = SimpleRange::default();
        assert_eq!(empty.absolute_start(), None);
        assert_eq!(empty.absolute_end(), None);
        Ok(())
    }

    #[test]
    fn test_contains() -> Result<(), Error<i32>> {
        let range = SimpleRange::try_from((1, 4))?; // [1, 4]
        assert!(range.contains(1));
        assert!(range.contains(2));
        assert!(range.contains(3));
        assert!(range.contains(4));
        assert!(!range.contains(5));
        assert!(!range.contains(0));
        Ok(())
    }

    #[test]
    fn test_is_dense() {
        let range = SimpleRange::from(1);
        assert!(range.is_dense());
    }

    #[test]
    fn test_default() {
        let range: SimpleRange<i32> = SimpleRange::default();
        assert_eq!(range.len(), 0);
        assert!(range.is_dense());
    }

    #[test]
    fn test_iterator() -> Result<(), Error<i32>> {
        let mut range = SimpleRange::try_from((1, 3))?; // [1, 3] -> 1, 2, 3
        assert_eq!(range.next(), Some(1));
        assert_eq!(range.next(), Some(2));
        assert_eq!(range.next(), Some(3));
        assert_eq!(range.next(), None);
        // Ensure empty state remains empty
        assert_eq!(range.next(), None);
        Ok(())
    }

    #[test]
    fn test_double_ended_iterator() -> Result<(), Error<i32>> {
        let mut range = SimpleRange::try_from((1, 3))?; // [1, 3] -> 1, 2, 3
        assert_eq!(range.next_back(), Some(3));
        assert_eq!(range.next_back(), Some(2));
        assert_eq!(range.next_back(), Some(1));
        assert_eq!(range.next_back(), None);
        // Ensure empty state remains empty
        assert_eq!(range.next_back(), None);
        Ok(())
    }

    #[test]
    fn test_len() -> Result<(), Error<i32>> {
        let range = SimpleRange::try_from((1, 4))?; // [1, 4]
        assert_eq!(range.len(), 4);
        Ok(())
    }

    #[test]
    fn test_try_from_tuple() -> Result<(), Error<i32>> {
        let range = SimpleRange::try_from((1, 4))?;
        assert_eq!(range.absolute_start(), Some(1));
        assert_eq!(range.absolute_end(), Some(4));

        let err = SimpleRange::try_from((4, 1)).unwrap_err();
        assert!(matches!(err, Error::OutOfRange(4)));
        Ok(())
    }

    #[test]
    fn test_try_from_slice() -> Result<(), Error<i32>> {
        let slice = [1, 2, 3];
        let range = SimpleRange::try_from(&slice[..])?;
        assert_eq!(range.len(), 3);
        assert_eq!(range.absolute_start(), Some(1));
        assert_eq!(range.absolute_end(), Some(3));

        let slice_unsorted = [1, 3, 2];
        let err = SimpleRange::try_from(&slice_unsorted[..]).unwrap_err();
        assert!(matches!(err, Error::NotSorted(3)));

        let slice_gap = [1, 3];
        let range_gap = SimpleRange::try_from(&slice_gap[..])?;
        // [1, 3] inclusive -> 1, 2, 3.
        assert!(range_gap.contains(2));

        Ok(())
    }

    #[test]
    fn test_try_from_vec() -> Result<(), Error<i32>> {
        let vec = vec![1, 2, 3];
        let range = SimpleRange::try_from(vec)?;
        assert_eq!(range.len(), 3);
        Ok(())
    }

    #[test]
    fn test_from_element() {
        let range = SimpleRange::from(5);
        assert_eq!(range.len(), 1);
        assert!(range.contains(5));
    }

    #[test]
    fn test_mul() -> Result<(), Error<i32>> {
        let range = SimpleRange::try_from((1, 2))?; // [1, 2]
        let scaled = range * 2;
        // start = 1*2 = 2
        // end = 2*2 = 4
        // [2, 4] -> 2, 3, 4
        assert!(scaled.contains(2));
        assert!(scaled.contains(3));
        assert!(scaled.contains(4));
        assert!(!scaled.contains(5));
        Ok(())
    }

    #[test]
    fn test_mul_assign() -> Result<(), Error<i32>> {
        let mut range = SimpleRange::try_from((1, 2))?;
        range *= 2;
        assert!(range.contains(2));
        assert!(range.contains(4));
        Ok(())
    }

    #[test]
    fn test_checked_mul() -> Result<(), Error<i32>> {
        let range = SimpleRange::try_from((1, 2))?;
        let scaled = range.checked_mul(2).unwrap();
        assert!(scaled.contains(2));
        assert!(scaled.contains(4));

        let range_overflow = SimpleRange::from(i32::MAX);
        assert!(range_overflow.checked_mul(2).is_none());
        Ok(())
    }

    #[test]
    fn test_into_tuple() -> Result<(), Error<i32>> {
        let range = SimpleRange::try_from((1, 4))?;
        let (start, end): (i32, i32) = range.into();
        assert_eq!(start, 1);
        assert_eq!(end, 4);
        Ok(())
    }

    #[test]
    fn test_into_vec() -> Result<(), Error<i32>> {
        let range = SimpleRange::try_from((1, 4))?;
        let vec: Vec<i32> = range.into();
        assert_eq!(vec, vec![1, 2, 3, 4]);
        Ok(())
    }
}
