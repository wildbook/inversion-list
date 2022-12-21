use core::ops::{Bound, Range, RangeBounds};

use crate::OrderedIndex;

/// Turn a RangeBounds into a Range, unless the resulting range is empty.
pub(super) fn bounds_to_range<T: OrderedIndex, R: RangeBounds<T>>(range: R) -> Option<Range<T>> {
    let start = match range.start_bound() {
        Bound::Included(&n) => n,
        Bound::Excluded(&n) => n
            .checked_add(T::one())
            .expect("range start bound overflowed"),
        Bound::Unbounded => T::min_value(),
    };
    let end = match range.end_bound() {
        Bound::Included(&n) => n.checked_add(T::one()).expect("range end bound overflowed"),
        Bound::Excluded(&n) => n,
        Bound::Unbounded => T::max_value(),
    };

    if end <= start {
        None
    } else {
        Some(start..end)
    }
}
