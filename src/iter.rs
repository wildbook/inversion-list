use std::iter::{Chain, FusedIterator, IntoIterator};

use crate::{InversionList, Range};

impl InversionList {
    /// An iterator over the inner ranges contained in this list.
    pub fn iter(&self) -> Iter {
        Iter {
            iter: self.0.iter(),
        }
    }

    pub fn difference<'this>(&'this self, other: &'this Self) -> Difference<'this> {
        Difference {
            iter: self.into_iter(),
            other,
        }
    }

    pub fn symmetric_difference<'this>(
        &'this self,
        other: &'this Self,
    ) -> SymmetricDifference<'this> {
        SymmetricDifference {
            iter: self.difference(other).chain(other.difference(self)),
        }
    }

    pub fn intersection<'this>(&'this self, other: &'this Self) -> Intersection<'this> {
        let (iter, other) = if self.len() <= other.len() {
            (self.iter(), other)
        } else {
            (other.iter(), self)
        };
        Intersection { iter, other }
    }

    pub fn union<'this>(&'this self, other: &'this Self) -> Union<'this> {
        Union {
            iter: if self.len() >= other.len() {
                self.iter().chain(other.difference(self))
            } else {
                other.iter().chain(self.difference(other))
            },
        }
    }
}

pub struct Iter<'il> {
    iter: std::slice::Iter<'il, Range>,
}

impl Iterator for Iter<'_> {
    type Item = Range;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().cloned()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl FusedIterator for Iter<'_> {}
impl ExactSizeIterator for Iter<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<'il> IntoIterator for &'il InversionList {
    type Item = Range;
    type IntoIter = Iter<'il>;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            iter: self.0.iter(),
        }
    }
}

pub struct IntoIter {
    iter: std::vec::IntoIter<Range>,
}

impl Iterator for IntoIter {
    type Item = Range;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl FusedIterator for IntoIter {}
impl ExactSizeIterator for IntoIter {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl IntoIterator for InversionList {
    type Item = Range;
    type IntoIter = IntoIter;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            iter: self.0.into_iter(),
        }
    }
}

pub struct Difference<'il> {
    pub(crate) iter: Iter<'il>,
    pub(crate) other: &'il InversionList,
}

impl Iterator for Difference<'_> {
    type Item = Range;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let next = self.iter.next()?;
            if !self.other.contains_range(next.clone()) {
                break Some(next);
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }
}

impl FusedIterator for Difference<'_> {}

pub struct SymmetricDifference<'il> {
    pub(crate) iter: Chain<Difference<'il>, Difference<'il>>,
}

impl Iterator for SymmetricDifference<'_> {
    type Item = Range;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl FusedIterator for SymmetricDifference<'_> {}

pub struct Union<'il> {
    pub(crate) iter: Chain<Iter<'il>, Difference<'il>>,
}

impl Iterator for Union<'_> {
    type Item = Range;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl FusedIterator for Union<'_> {}

pub struct Intersection<'il> {
    pub(crate) iter: Iter<'il>,
    pub(crate) other: &'il InversionList,
}

impl Iterator for Intersection<'_> {
    type Item = Range;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let next = self.iter.next()?;
            if self.other.contains_range(next.clone()) {
                break Some(next);
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }
}

impl FusedIterator for Intersection<'_> {}
