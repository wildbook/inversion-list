#![warn(clippy::all)]

use core::convert::identity;
use core::iter::FromIterator;
use core::mem;
use core::ops::{self, Range, RangeBounds};

mod iter;
mod util;

use crate::util::bounds_to_range;

pub use self::iter::*;

pub trait OrderedIndex:
    Sized + Copy + PartialOrd + Ord + Eq + ops::Sub<Self, Output = Self> + ops::Add<Self, Output = Self>
{
    fn one() -> Self;
    fn min_value() -> Self;
    fn max_value() -> Self;
    fn checked_add(self, v: Self) -> Option<Self>;
}

macro_rules! impl_prim {
    ($($ty:ty)*) => {
        $(
            impl OrderedIndex for $ty {
                fn one() -> Self { 1 }
                fn min_value() -> Self { Self::MIN }
                fn max_value() -> Self { Self::MAX }
                fn checked_add(self, v: Self) -> Option<Self> {
                    Self::checked_add(self, v)
                }
            }
        )*
    };
}
impl_prim! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

/// An inversion list is a data structure that describes a set of non-overlapping numeric ranges, stored in increasing order.
///
/// A few notes regarding the naming convention of the functions:
/// - *_strict: These functions usual check that ranges are strictly the same, and not sub/supersets.
/// - *_at: These functions usually take indices into the backing buffer, while the other versions
///         generally take a value that is contained in a range or ranges directly.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct InversionList<Ty: OrderedIndex = usize>(Vec<Range<Ty>>);

impl<Ty: OrderedIndex> InversionList<Ty> {
    pub fn new() -> Self {
        InversionList(vec![])
    }

    pub fn with_capacity(capacity: usize) -> Self {
        InversionList(Vec::with_capacity(capacity))
    }

    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Checks whether the given usize is inside any of the contained ranges.
    pub fn contains(&self, value: Ty) -> bool {
        self.binary_search(value).is_ok()
    }

    /// Checks whether this InversionList contains a range that is a "superrange" of the given range.
    pub fn contains_range<R: RangeBounds<Ty>>(&self, range: R) -> bool {
        if let Some(Range { start, end }) = bounds_to_range(range) {
            self.binary_search(start)
                .map(|idx_s| end <= self.0[idx_s].end)
                .unwrap_or(false)
        } else {
            false
        }
    }

    /// Checks whether this InversionList contains this exact range.
    pub fn contains_range_strict<R: RangeBounds<Ty>>(&self, range: R) -> bool {
        if let Some(Range { start, end }) = bounds_to_range(range) {
            self.binary_search(start)
                .map(|idx_s| end == self.0[idx_s].end)
                .unwrap_or(false)
        } else {
            false
        }
    }

    /// Check if the given range intersects with any ranges inside of the inversion list.
    pub fn intersects<R: RangeBounds<Ty>>(&self, range: R) -> bool {
        if let Some(Range { start, end }) = bounds_to_range(range) {
            match self.binary_search(start) {
                Ok(_) => true,
                Err(idx_s) => {
                    match self.binary_search(end - Ty::one()) {
                        Ok(_) => true,
                        // check if there is at least one range inside of our range
                        Err(idx_e) => idx_e - idx_s >= 1,
                    }
                }
            }
        } else {
            false
        }
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Checks whether `self` is a subset of `other`, meaning whether self's ranges all lie somewhere inside of `other`.
    pub fn is_subset(&self, other: &Self) -> bool {
        self.iter().all(|range| other.contains_range(range))
    }

    /// Checks whether `self` and `other` are entirely disjoint.
    pub fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
    }

    /// Checks whether `self` is a subset of `other`, meaning whether self's ranges all lie somewhere inside of `other`.
    pub fn is_subset_strict(&self, other: &Self) -> bool {
        self.iter().all(|range| other.contains_range_strict(range))
    }

    /// Checks whether `self` is a strict superset of `other`, meaning whether other containts all of self's ranges.
    pub fn is_superset_strict(&self, other: &Self) -> bool {
        other.is_subset_strict(self)
    }

    /// Checks whether `self` and `other` are entirely disjoint.
    pub fn is_disjoint(&self, other: &Self) -> bool {
        if self.len() <= other.len() {
            !self.iter().any(|range| other.intersects(range))
        } else {
            !other.iter().any(|range| self.intersects(range))
        }
    }

    pub fn remove_range_at(&mut self, idx: usize) -> Option<Range<Ty>> {
        if idx < self.len() {
            Some(self.0.remove(idx))
        } else {
            None
        }
    }

    /// Adds a unit range(index..index + 1) to the inversion list. This is faster than using
    /// [`add_range`] saving a second binary_search.
    ///
    /// If the unit is not part of an existing range, `true` is returned.
    ///
    /// If the unit already exists in a range, `false` is returned.
    ///
    /// # Panics
    ///
    /// Panics if index is equal to usize::MAX.
    pub fn add_unit(&mut self, index: Ty) -> bool {
        if let Err(insert_idx) = self.binary_search(index) {
            // this creates a new unit range that may be directly adjacent to an existing one
            // have a method that tries to merge them directly as well?
            self.0.insert(
                insert_idx,
                index
                    ..index
                        .checked_add(Ty::one())
                        .expect("index is equal to usize::MAX"),
            );

            true
        } else {
            false
        }
    }

    pub fn add_range<R: RangeBounds<Ty>>(&mut self, range: R) {
        let (start, end) = match bounds_to_range(range) {
            Some(range) => (range.start, range.end),
            None => return,
        };

        // check if start is inside a range
        let (idx_s, idx_e) = match self.binary_search(start) {
            // range starts inside another
            Ok(idx_s) => match self.binary_search(end) {
                // and ends in another possibly surrounding other ranges
                Ok(idx_e) => (idx_s, idx_e),
                // and ends in an empty space possibly surrounding other ranges
                Err(idx_e) => {
                    self.0.insert(idx_e, end - Ty::one()..end);
                    (idx_s, idx_e)
                }
            },
            // range starts in an empty space
            Err(idx_s) => {
                // therefor create a dummy range to merge on
                self.0.insert(idx_s, start..start + Ty::one());
                match self.binary_search(end) {
                    // and ends in another possibly surrounding other ranges
                    Ok(idx_e) => (idx_s, idx_e),
                    // and ends in an empty space possibly surrounding other ranges
                    Err(idx_e) => {
                        self.0.insert(idx_e, end - Ty::one()..end);
                        (idx_s, idx_e)
                    }
                }
            }
        };
        self.merge(idx_s, idx_e);
    }

    pub fn remove_range<R: RangeBounds<Ty>>(&mut self, range: R) {
        let (start, end) = match bounds_to_range(range) {
            Some(range) => (range.start, range.end),
            None => return,
        };

        let (idx_s, idx_e) = match self.binary_search(start) {
            Ok(idx_s) => {
                let (_, idx_s) = self.split_impl(idx_s, start);
                match self.binary_search(end) {
                    Ok(idx_e) => {
                        let (_, right) = self.split_impl(idx_e, end);
                        (idx_s, right)
                    }
                    Err(idx_e) => (idx_s, idx_e),
                }
            }
            Err(idx_s) => match self.binary_search(end) {
                Ok(idx_e) => {
                    let (_, right) = self.split_impl(idx_e, end);
                    (idx_s, right)
                }
                Err(idx_e) => (idx_s, idx_e),
            },
        };
        self.0.drain(idx_s..idx_e);
    }

    /// Splits the range that contains `at` in two with `at` being the split point.
    ///
    /// If a range exists that contains `at` the return value are the indices of the
    /// new left and right ranges of the split point. The left range will contain `at`.
    /// If `at` is equal to the start of the range it is in, no split occurs and the left
    /// and right indices will be equal to the index of the range containing the value.
    ///
    /// Split ranges that are right next to each other will not be recognized as one.
    /// Meaning functions like `contains_range` will not work properly if the start and end
    /// points lie in the different parts of the neighbouring ranges. Thus it is important to
    /// either remove these ranges or remerge them.
    pub fn split(&mut self, at: Ty) -> Option<(usize, usize)> {
        self.binary_search(at)
            .ok()
            .map(|idx| self.split_impl(idx, at))
    }

    /// Merges the ranges at `start` and `end`, discarding all ranges inbetween them.
    ///
    /// # Panics
    ///
    /// Panics if the indices dont point to a valid index into the vec.
    pub fn merge(&mut self, start: usize, end: usize) {
        self.0[start].end = self.0[end].end;
        self.0.drain(start + 1..=end);
    }

    /// Merges all ranges together that are directly adjacent to each other.
    pub fn collapse(&mut self) {
        let ranges = &mut self.0;
        let mut i = 1;
        while i < ranges.len() {
            if ranges[i - 1].end == ranges[i].start {
                ranges[i - 1].end = ranges[i].end;
                ranges.remove(i);
            } else {
                i += 1;
            }
        }
    }

    /// Inverts all ranges, meaning existing ranges will be removed and parts that were previously
    /// not covered by ranges will now be covered.
    pub fn invert(&mut self) {
        let prev_len = self.0.len();
        let mut old = mem::replace(&mut self.0, Vec::with_capacity(prev_len)).into_iter();

        let mut last = match old.next() {
            Some(range) if range.start == Ty::min_value() => range.end,
            Some(range) => {
                self.0.push(Ty::min_value()..range.start);
                range.end
            }
            None => return,
        };
        for range in old {
            if range.start != last {
                self.0.push(last..range.start);
            }
            last = range.end;
        }
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[allow(clippy::toplevel_ref_arg)]
    pub fn binary_search(&self, ref key: Ty) -> Result<usize, usize> {
        use std::cmp::Ordering::*;
        self.0.binary_search_by(move |range| {
            match (range.start.cmp(key), key.cmp(&range.end)) {
                // start > key
                (Greater, _) => Greater,
                // start == key
                (Equal, _) => Equal,
                // start < key && key < end
                (Less, Less) => Equal,
                // start < key && key >= end
                (Less, _) => Less,
            }
        })
    }

    // invariant, `at` is inside the range addressed by idx
    // return value is left range and right range indices of the split range.
    // The indices are the same if the split point was at the start of the range.
    fn split_impl(&mut self, idx: usize, at: Ty) -> (usize, usize) {
        debug_assert!(self.0[idx].contains(&at));
        let to_split = &mut self.0[idx];
        if to_split.start != at {
            let end = std::mem::replace(&mut to_split.end, at);
            self.0.insert(idx + 1, at..end);
            (idx, idx + 1)
        } else {
            (idx, idx)
        }
    }

    pub fn end(&self) -> Option<Ty> {
        self.0.last().map(|r| r.end)
    }

    pub fn start(&self) -> Option<Ty> {
        self.0.first().map(|r| r.start)
    }

    /// Returns the complete surrounding range, if any.
    pub fn span(&self) -> Option<Range<Ty>> {
        self.start()
            .and_then(|start| self.end().map(move |end| start..end))
    }
}

// TODO: Can't be changed to `Ty`. Kept for backwards compatibility.
impl<R: RangeBounds<usize>> From<R> for InversionList<usize> {
    fn from(range: R) -> Self {
        InversionList(Vec::from_iter(bounds_to_range(range)))
    }
}

impl<Ty: OrderedIndex> ops::Deref for InversionList<Ty> {
    type Target = [Range<Ty>];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<Ty: OrderedIndex> FromIterator<Range<Ty>> for InversionList<Ty> {
    fn from_iter<T: IntoIterator<Item = Range<Ty>>>(iter: T) -> Self {
        let mut res = InversionList::new();
        for range in iter {
            res.add_range(range);
        }
        res
    }
}

impl<Ty: OrderedIndex> ops::BitAnd<&InversionList<Ty>> for &InversionList<Ty> {
    type Output = InversionList<Ty>;
    fn bitand(self, rhs: &InversionList<Ty>) -> Self::Output {
        let mut res = InversionList::new();

        let (base, iter) = if self.len() < rhs.len() {
            (rhs, self.iter())
        } else {
            (self, rhs.iter())
        };

        for range in iter {
            let start = base.binary_search(range.start).unwrap_or_else(identity);
            let end = base
                .binary_search(range.end)
                .unwrap_or_else(|idx| idx - 1 /*can this ever underflow?*/);
            debug_assert!(start <= end);
            res.add_range(range.start.max(base[start].start)..range.end.min(base[start].end));
            for range in base.get((start + 1)..end).into_iter().flatten() {
                // could just copy slices here for efficiency
                res.add_range(range.clone());
            }
            res.add_range(range.start.max(base[end].start)..range.end.min(base[end].end));
        }

        res
    }
}

impl<Ty: OrderedIndex> ops::BitAnd<InversionList<Ty>> for &InversionList<Ty> {
    type Output = InversionList<Ty>;
    fn bitand(self, rhs: InversionList<Ty>) -> Self::Output {
        <&InversionList<Ty>>::bitand(self, &rhs)
    }
}

impl<Ty: OrderedIndex> ops::BitAnd<&InversionList<Ty>> for InversionList<Ty> {
    type Output = InversionList<Ty>;
    fn bitand(self, rhs: &InversionList<Ty>) -> Self::Output {
        <&InversionList<Ty>>::bitand(&self, rhs)
    }
}

impl<Ty: OrderedIndex> ops::BitAnd<InversionList<Ty>> for InversionList<Ty> {
    type Output = InversionList<Ty>;
    fn bitand(self, rhs: InversionList<Ty>) -> Self::Output {
        <&InversionList<Ty>>::bitand(&self, &rhs)
    }
}

impl<Ty: OrderedIndex> ops::BitAndAssign<InversionList<Ty>> for InversionList<Ty> {
    fn bitand_assign(&mut self, rhs: InversionList<Ty>) {
        *self &= &rhs;
    }
}

impl<Ty: OrderedIndex> ops::BitAndAssign<&InversionList<Ty>> for InversionList<Ty> {
    fn bitand_assign(&mut self, rhs: &InversionList<Ty>) {
        *self = &*self & rhs;
    }
}

impl<Ty: OrderedIndex> ops::BitOr<&InversionList<Ty>> for &InversionList<Ty> {
    type Output = InversionList<Ty>;
    fn bitor(self, rhs: &InversionList<Ty>) -> Self::Output {
        // TODO: optimize these clones away in owned impls
        let (mut res, iter) = if self.len() < rhs.len() {
            (rhs.clone(), self.iter())
        } else {
            (self.clone(), rhs.iter())
        };

        for range in iter {
            res.add_range(range);
        }

        res
    }
}

impl<Ty: OrderedIndex> ops::BitOr<InversionList<Ty>> for &InversionList<Ty> {
    type Output = InversionList<Ty>;
    fn bitor(self, rhs: InversionList<Ty>) -> Self::Output {
        <&InversionList<Ty>>::bitor(self, &rhs)
    }
}

impl<Ty: OrderedIndex> ops::BitOr<&InversionList<Ty>> for InversionList<Ty> {
    type Output = InversionList<Ty>;
    fn bitor(self, rhs: &InversionList<Ty>) -> Self::Output {
        <&InversionList<Ty>>::bitor(&self, rhs)
    }
}

impl<Ty: OrderedIndex> ops::BitOr<InversionList<Ty>> for InversionList<Ty> {
    type Output = InversionList<Ty>;
    fn bitor(self, rhs: InversionList<Ty>) -> Self::Output {
        <&InversionList<Ty>>::bitor(&self, &rhs)
    }
}

impl<Ty: OrderedIndex> ops::BitOrAssign<InversionList<Ty>> for InversionList<Ty> {
    fn bitor_assign(&mut self, rhs: InversionList<Ty>) {
        *self |= &rhs;
    }
}

impl<Ty: OrderedIndex> ops::BitOrAssign<&InversionList<Ty>> for InversionList<Ty> {
    fn bitor_assign(&mut self, rhs: &InversionList<Ty>) {
        *self = &*self | rhs;
    }
}

impl<Ty: OrderedIndex> ops::Not for InversionList<Ty> {
    type Output = InversionList<Ty>;
    fn not(self) -> InversionList<Ty> {
        !&self
    }
}

impl<Ty: OrderedIndex> ops::Not for &InversionList<Ty> {
    type Output = InversionList<Ty>;
    fn not(self) -> InversionList<Ty> {
        let mut res = InversionList::new();
        let mut iter = self.iter();
        if let Some(range) = iter.next() {
            let mut last = if range.start == Ty::min_value() {
                range.end
            } else {
                res.add_range(Ty::min_value()..range.start);
                range.end
            };
            for range in iter {
                res.add_range(last..range.start);
                last = range.end
            }
            res.add_range(last..Ty::max_value());
        }
        res
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn binary_search() {
        let il = InversionList(vec![0..5, 5..15, 20..25]);
        assert_eq!(Ok(0), il.binary_search(0));
        assert_eq!(Ok(0), il.binary_search(1));
        assert_eq!(Ok(1), il.binary_search(5));
        assert_eq!(Err(2), il.binary_search(15));
        assert_eq!(Err(2), il.binary_search(16));
        assert_eq!(Ok(2), il.binary_search(20));
        assert_eq!(Err(3), il.binary_search(25));
    }

    #[test]
    fn merge() {
        let mut il = InversionList(vec![0..5, 5..15, 20..25]);
        il.merge(0, 2);
        assert_eq!(il, InversionList(vec![0..25]));
    }

    #[test]
    fn split_inorder() {
        let mut il = InversionList::from(0..100);
        il.split(5);
        il.split(15);
        il.split(25);
        assert_eq!(il, InversionList(vec![0..5, 5..15, 15..25, 25..100,]));
    }

    #[test]
    fn split_outoforder() {
        let mut il = InversionList::from(0..100);
        il.split(25);
        il.split(5);
        il.split(15);
        assert_eq!(il, InversionList(vec![0..5, 5..15, 15..25, 25..100,]));
    }

    #[test]
    fn split_double() {
        let mut il = InversionList::from(0..100);
        il.split(50);
        il.split(50);
        assert_eq!(il, InversionList(vec![0..50, 50..100]));
    }

    #[test]
    fn split_boundary_left() {
        let mut il = InversionList::from(0..100);
        il.split(0);
        assert_eq!(il, InversionList(vec![0..100]));
    }

    #[test]
    fn split_boundary_right() {
        let mut il = InversionList::from(0..100);
        il.split(100);
        assert_eq!(il, InversionList(vec![0..100]));
    }

    #[test]
    fn split_out_of_bounds() {
        let mut il = InversionList::from(1..100);
        il.split(101);
        il.split(1);
        assert_eq!(il, InversionList(vec![1..100]));
    }

    #[test]
    fn add_range_start() {
        let mut il = InversionList(vec![0..10]);
        il.add_range(0..45);
        assert_eq!(il, InversionList(vec![0..45]));
    }

    #[test]
    fn add_range_end() {
        let mut il = InversionList(vec![0..10, 20..30]);
        il.add_range(5..10);
        il.add_range(15..30);
        assert_eq!(il, InversionList(vec![0..10, 15..30]));
        let mut il = InversionList(vec![0..10, 20..30]);
        il.add_range(15..20);
        assert_eq!(il, InversionList(vec![0..10, 15..30]));
    }

    #[test]
    fn add_range_in_in() {
        let mut il = InversionList(vec![0..10, 20..30, 40..50, 60..70]);
        il.add_range(5..45);
        assert_eq!(il, InversionList(vec![0..50, 60..70]));
    }

    #[test]
    fn add_range_in_out() {
        let mut il = InversionList(vec![0..10, 20..30, 40..50, 60..70]);
        il.add_range(5..35);
        assert_eq!(il, InversionList(vec![0..35, 40..50, 60..70]));
    }

    #[test]
    fn add_range_out_in() {
        let mut il = InversionList(vec![0..10, 20..30, 40..50, 60..70]);
        il.add_range(15..45);
        assert_eq!(il, InversionList(vec![0..10, 15..50, 60..70]));
    }

    #[test]
    fn add_range_out_out() {
        let mut il = InversionList(vec![0..10, 20..30, 40..50, 60..70]);
        il.add_range(15..55);
        assert_eq!(il, InversionList(vec![0..10, 15..55, 60..70]));
    }

    #[test]
    fn add_range_ignore_max_range() {
        // test to make sure we dont overflow
        let mut il = InversionList(vec![0usize..10, 20..30, 40..50, 60..70]);
        il.add_range(!0..!0);
        assert_eq!(il, InversionList(vec![0..10, 20..30, 40..50, 60..70]));
    }

    #[test]
    fn remove_range_in_in() {
        let mut il = InversionList(vec![1..10, 20..30, 40..50]);
        il.remove_range(5..45);
        assert_eq!(il, InversionList(vec![1..5, 45..50]));
        let mut il = InversionList(vec![1..10, 20..30, 40..50]);
        il.remove_range(5..40);
        assert_eq!(il, InversionList(vec![1..5, 40..50]));
    }

    #[test]
    fn remove_range_in_out() {
        let mut il = InversionList(vec![1..10, 20..30, 40..50]);
        il.remove_range(5..35);
        assert_eq!(il, InversionList(vec![1..5, 40..50]));
    }

    #[test]
    fn remove_range_out_in() {
        let mut il = InversionList(vec![1..10, 20..30, 40..50]);
        il.remove_range(15..45);
        assert_eq!(il, InversionList(vec![1..10, 45..50]));
    }

    #[test]
    fn remove_range_out_out() {
        let mut il = InversionList(vec![1..10, 20..30, 40..50]);
        il.remove_range(15..35);
        assert_eq!(il, InversionList(vec![1..10, 40..50]));
    }

    #[test]
    fn remove_range_subset() {
        let mut il = InversionList::from(1..100);
        il.remove_range(50..75);
        assert_eq!(il, InversionList(vec![1..50, 75..100]));
    }

    #[test]
    fn remove_range_superset() {
        let mut il = InversionList::from(1..100);
        il.remove_range(0..175);
        assert_eq!(il, InversionList(vec![]));
    }

    #[test]
    fn remove_range_end() {
        let mut il = InversionList::from(1..100);
        il.remove_range(50..100);
        assert_eq!(il, InversionList(vec![1..50]));
    }

    #[test]
    fn remove_range_start() {
        let mut il = InversionList::from(1..100);
        il.remove_range(1..50);
        assert_eq!(il, InversionList(vec![50..100]));
    }

    #[test]
    fn is_subset() {
        let il = InversionList(vec![1..10, 15..26, 61..100]);
        let il2 = InversionList(vec![1..5, 17..22, 77..88]);
        let il3 = InversionList(vec![1..10, 77..88]);
        assert!(il.is_subset(&il));
        assert!(il2.is_subset(&il));
        assert!(il3.is_subset(&il));
        assert!(!il.is_subset(&il2));
        assert!(!il.is_subset(&il3));

        assert!(il.is_superset(&il));
        assert!(il.is_superset(&il2));
        assert!(il.is_superset(&il3));
        assert!(!il2.is_superset(&il));
        assert!(!il3.is_superset(&il));
    }

    #[test]
    fn is_subset_strict() {
        let il = InversionList(vec![1..10, 15..26, 61..100]);
        let il2 = InversionList(vec![1..10, 17..22, 77..88]);
        let il3 = InversionList(vec![1..10, 77..88]);
        assert!(il.is_subset_strict(&il));
        assert!(!il2.is_subset_strict(&il));
        assert!(il3.is_subset_strict(&il2));

        assert!(il.is_superset_strict(&il));
        assert!(!il.is_superset_strict(&il2));
        assert!(il2.is_superset_strict(&il3));
    }

    #[test]
    fn is_disjoint() {
        let il = InversionList(vec![1..10, 15..26, 61..100]);
        let il2 = InversionList(vec![1..5, 17..22, 77..88, 100..166]);
        let il3 = InversionList(vec![1..10, 37..54, 66..100]);
        let il4 = InversionList(vec![10..15, 44..55, 60..61]);
        assert!(!il.is_disjoint(&il));
        assert!(!il.is_disjoint(&il2));
        assert!(!il.is_disjoint(&il3));
        assert!(il.is_disjoint(&il4));
    }

    #[test]
    fn intersects() {
        let il = InversionList(vec![1..10, 15..26, 61..100]);
        assert!(il.intersects(5..10));
        assert!(!il.intersects(0..1));
        assert!(il.intersects(12..17));
        assert!(il.intersects(20..30));

        assert!(il.intersects(2..8));
        assert!(il.intersects(0..11));
    }

    #[test]
    fn collapse() {
        let mut il = InversionList(vec![1..10, 10..26, 30..33, 33..35, 35..40, 41..45]);
        il.collapse();
        assert_eq!(il, InversionList(vec![1..26, 30..40, 41..45]));
    }

    #[test]
    fn invert() {
        let mut il = InversionList(vec![1..10, 10..26, 30..33, 33..35, 35..40, 41..45]);
        il.invert();
        assert_eq!(il, InversionList(vec![0usize..1, 26..30, 40..41]));
        let mut il = InversionList(vec![0usize..10, 15..26, 26..33, 34..35, 35..36]);
        il.invert();
        assert_eq!(il, InversionList(vec![10..15, 33..34]));
    }

    #[test]
    fn test_bitand() {
        let il = InversionList(vec![0..5, 5..15, 20..25, 50..80]);
        let il2 = InversionList(vec![
            0..5,
            7..10,
            12..18,
            19..27,
            30..40,
            45..55,
            57..60,
            78..82,
        ]);
        assert_eq!(
            il & il2,
            InversionList(vec![0..5, 7..10, 12..15, 20..25, 50..55, 57..60, 78..80])
        );
    }

    #[test]
    fn test_bitor() {
        let il = InversionList(vec![0..5, 5..15, 20..25, 50..80]);
        let il2 = InversionList(vec![
            0..5,
            7..10,
            12..18,
            19..27,
            30..40,
            45..55,
            57..60,
            78..82,
        ]);
        assert_eq!(
            il | il2,
            InversionList(vec![0..5, 5..18, 19..27, 30..40, 45..82])
        );
    }

    #[test]
    fn test_not() {
        let il = InversionList(vec![0usize..5, 5..15, 20..25, 50..80]);
        assert_eq!(!il, InversionList(vec![15..20, 25..50, 80..!0]));
        let il = InversionList(vec![5..15, 20..25, 50..80]);
        assert_eq!(!il, InversionList(vec![0usize..5, 15..20, 25..50, 80..!0]));
    }
}
