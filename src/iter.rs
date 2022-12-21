use std::{
    iter::{Chain, FusedIterator, IntoIterator},
    ops::Range,
};

use crate::OrderedIndex;

use crate::InversionList;

impl<Ty: OrderedIndex> InversionList<Ty> {
    /// An iterator over the inner ranges contained in this list.
    pub fn iter(&self) -> Iter<Ty> {
        Iter {
            iter: self.0.iter(),
        }
    }

    pub fn difference<'this>(&'this self, other: &'this Self) -> Difference<'this, Ty> {
        Difference {
            iter: self.into_iter(),
            other,
        }
    }

    pub fn symmetric_difference<'this>(
        &'this self,
        other: &'this Self,
    ) -> SymmetricDifference<'this, Ty> {
        SymmetricDifference {
            iter: self.difference(other).chain(other.difference(self)),
        }
    }

    pub fn intersection<'this>(&'this self, other: &'this Self) -> Intersection<'this, Ty> {
        let (iter, other) = if self.len() <= other.len() {
            (self.iter(), other)
        } else {
            (other.iter(), self)
        };
        Intersection { iter, other }
    }

    pub fn union<'this>(&'this self, other: &'this Self) -> Union<'this, Ty> {
        Union {
            iter: if self.len() >= other.len() {
                self.iter().chain(other.difference(self))
            } else {
                other.iter().chain(self.difference(other))
            },
        }
    }
}

pub struct Iter<'il, Ty: OrderedIndex = usize> {
    iter: std::slice::Iter<'il, Range<Ty>>,
}

impl<Ty: OrderedIndex> Iterator for Iter<'_, Ty> {
    type Item = Range<Ty>;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().cloned()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<Ty: OrderedIndex> FusedIterator for Iter<'_, Ty> {}
impl<Ty: OrderedIndex> ExactSizeIterator for Iter<'_, Ty> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<'il, Ty: OrderedIndex> IntoIterator for &'il InversionList<Ty> {
    type Item = Range<Ty>;
    type IntoIter = Iter<'il, Ty>;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            iter: self.0.iter(),
        }
    }
}

pub struct IntoIter<Ty: OrderedIndex = usize> {
    iter: std::vec::IntoIter<Range<Ty>>,
}

impl<Ty: OrderedIndex> Iterator for IntoIter<Ty> {
    type Item = Range<Ty>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<Ty: OrderedIndex> FusedIterator for IntoIter<Ty> {}
impl<Ty: OrderedIndex> ExactSizeIterator for IntoIter<Ty> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<Ty: OrderedIndex> IntoIterator for InversionList<Ty> {
    type Item = Range<Ty>;
    type IntoIter = IntoIter<Ty>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            iter: self.0.into_iter(),
        }
    }
}

pub struct Difference<'il, Ty: OrderedIndex = usize> {
    pub(crate) iter: Iter<'il, Ty>,
    pub(crate) other: &'il InversionList<Ty>,
}

impl<Ty: OrderedIndex> Iterator for Difference<'_, Ty> {
    type Item = Range<Ty>;

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

impl<Ty: OrderedIndex> FusedIterator for Difference<'_, Ty> {}

pub struct SymmetricDifference<'il, Ty: OrderedIndex = usize> {
    pub(crate) iter: Chain<Difference<'il, Ty>, Difference<'il, Ty>>,
}

impl<Ty: OrderedIndex> Iterator for SymmetricDifference<'_, Ty> {
    type Item = Range<Ty>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<Ty: OrderedIndex> FusedIterator for SymmetricDifference<'_, Ty> {}

pub struct Union<'il, Ty: OrderedIndex = usize> {
    pub(crate) iter: Chain<Iter<'il, Ty>, Difference<'il, Ty>>,
}

impl<Ty: OrderedIndex> Iterator for Union<'_, Ty> {
    type Item = Range<Ty>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<Ty: OrderedIndex> FusedIterator for Union<'_, Ty> {}

pub struct Intersection<'il, Ty: OrderedIndex = usize> {
    pub(crate) iter: Iter<'il, Ty>,
    pub(crate) other: &'il InversionList<Ty>,
}

impl<Ty: OrderedIndex> Iterator for Intersection<'_, Ty> {
    type Item = Range<Ty>;

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

impl<Ty: OrderedIndex> FusedIterator for Intersection<'_, Ty> {}
