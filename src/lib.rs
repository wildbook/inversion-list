use std::iter::FromIterator;
use std::ops::{Bound, Range as StdRange, RangeBounds};

// use #[feature(trait_alias)] once stable
//type RangeBounds = StdRangeBounds<usize>;
type Range = StdRange<usize>;

/// Turn a RangeBounds into a Range, unless the resulting range is empty.
fn bounds_to_range<R: RangeBounds<usize>>(range: R) -> Option<Range> {
    let start = match range.start_bound() {
        Bound::Included(&n) => n,
        Bound::Excluded(&n) => n.checked_add(1).expect("range start bound overflowed"),
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&n) => n.checked_add(1).expect("range end bound overflowed"),
        Bound::Excluded(&n) => n,
        Bound::Unbounded => !0usize,
    };
    if end <= start {
        None
    } else {
        Some(start..end)
    }
}

/// An inversion list is a data structure that describes a set of non-overlapping numeric ranges, stored in increasing order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct InversionList(Vec<Range>);

impl InversionList {
    pub fn new() -> Self {
        InversionList(vec![])
    }

    pub fn with_capacity(capacity: usize) -> Self {
        InversionList(Vec::with_capacity(capacity))
    }

    pub fn remove_range_at(&mut self, idx: usize) -> Option<Range> {
        if idx < self.len() {
            Some(self.0.remove(idx))
        } else {
            None
        }
    }

    pub fn add_single(&mut self, index: usize) {
        if let Err(insert_idx) = self.binary_search(index) {
            // this creates a new unit range that may be directly adjacent to an existing one
            // have a method that tries to merge them directly as well?
            self.0.insert(
                insert_idx,
                index..index.checked_add(1).expect("index is equal to usize::MAX"),
            )
        }
    }

    pub fn add_range<R: RangeBounds<usize>>(&mut self, range: R) {
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
                    self.0.insert(idx_e, end - 1..end);
                    (idx_s, idx_e)
                }
            },
            // range starts in an empty space
            Err(idx_s) => {
                // therefor create a dummy range to merge on
                self.0.insert(idx_s, start..start + 1);
                match self.binary_search(end) {
                    // and ends in another possibly surrounding other ranges
                    Ok(idx_e) => (idx_s, idx_e),
                    // and ends in an empty space possibly surrounding other ranges
                    Err(idx_e) => {
                        self.0.insert(idx_e, end - 1..end);
                        (idx_s, idx_e)
                    }
                }
            }
        };
        self.merge(idx_s, idx_e);
    }

    pub fn remove_range<R: RangeBounds<usize>>(&mut self, range: R) {
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
    pub fn split(&mut self, at: usize) {
        if let Ok(idx) = self.binary_search(at) {
            self.split_impl(idx, at);
        }
    }

    /// Merges the ranges at `start` and `end`, discarding all ranges inbetween them.
    ///
    /// # Panics
    ///
    /// Panics if the indices dont point to a valid index into the vec.
    fn merge(&mut self, start: usize, end: usize) {
        self.0[start].end = self.0[end].end;
        self.0.drain(start + 1..=end);
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    #[allow(clippy::toplevel_ref_arg)]
    fn binary_search(&self, ref key: usize) -> Result<usize, usize> {
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
    fn split_impl(&mut self, idx: usize, at: usize) -> (usize, usize) {
        let to_split = &mut self.0[idx];
        if to_split.start != at {
            let end = std::mem::replace(&mut to_split.end, at);
            self.0.insert(idx + 1, at..end);
            (idx, idx + 1)
        } else {
            (idx, idx)
        }
    }

    pub fn end(&self) -> Option<usize> {
        self.0.last().map(|r| r.end)
    }

    pub fn start(&self) -> Option<usize> {
        self.0.first().map(|r| r.start)
    }

    /// Returns the complete surrounding range, if any.
    pub fn span(&self) -> Option<Range> {
        self.start()
            .and_then(|start| self.end().map(move |end| start..end))
    }

    pub fn ranges<'this>(&'this self) -> impl Iterator<Item = Range> + 'this {
        self.0.iter().cloned()
    }
}

impl<R: RangeBounds<usize>> From<R> for InversionList {
    fn from(range: R) -> Self {
        InversionList(Vec::from_iter(bounds_to_range(range)))
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
        let mut il = InversionList(vec![0..10, 20..30, 40..50, 60..70]);
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
}
