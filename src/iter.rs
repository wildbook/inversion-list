use std::{
    iter::{Chain, FusedIterator, IntoIterator},
    ops::Range,
};

use num_traits::PrimInt;

use crate::InversionList;

impl<Ty: PrimInt> InversionList<Ty> {
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

pub struct Iter<'il, Ty: PrimInt = usize> {
    iter: std::slice::Iter<'il, Range<Ty>>,
}

impl<Ty: PrimInt> Iterator for Iter<'_, Ty> {
    type Item = Range<Ty>;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().cloned()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<Ty: PrimInt> FusedIterator for Iter<'_, Ty> {}
impl<Ty: PrimInt> ExactSizeIterator for Iter<'_, Ty> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<'il, Ty: PrimInt> IntoIterator for &'il InversionList<Ty> {
    type Item = Range<Ty>;
    type IntoIter = Iter<'il, Ty>;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            iter: self.0.iter(),
        }
    }
}

pub struct IntoIter<Ty: PrimInt = usize> {
    iter: std::vec::IntoIter<Range<Ty>>,
}

impl<Ty: PrimInt> Iterator for IntoIter<Ty> {
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

impl<Ty: PrimInt> FusedIterator for IntoIter<Ty> {}
impl<Ty: PrimInt> ExactSizeIterator for IntoIter<Ty> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<Ty: PrimInt> IntoIterator for InversionList<Ty> {
    type Item = Range<Ty>;
    type IntoIter = IntoIter<Ty>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            iter: self.0.into_iter(),
        }
    }
}

pub struct Difference<'il, Ty: PrimInt = usize> {
    pub(crate) iter: Iter<'il, Ty>,
    pub(crate) other: &'il InversionList<Ty>,
}

impl<Ty: PrimInt> Iterator for Difference<'_, Ty> {
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

impl<Ty: PrimInt> FusedIterator for Difference<'_, Ty> {}

pub struct SymmetricDifference<'il, Ty: PrimInt = usize> {
    pub(crate) iter: Chain<Difference<'il, Ty>, Difference<'il, Ty>>,
}

impl<Ty: PrimInt> Iterator for SymmetricDifference<'_, Ty> {
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

impl<Ty: PrimInt> FusedIterator for SymmetricDifference<'_, Ty> {}

pub struct Union<'il, Ty: PrimInt = usize> {
    pub(crate) iter: Chain<Iter<'il, Ty>, Difference<'il, Ty>>,
}

impl<Ty: PrimInt> Iterator for Union<'_, Ty> {
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

impl<Ty: PrimInt> FusedIterator for Union<'_, Ty> {}

pub struct Intersection<'il, Ty: PrimInt = usize> {
    pub(crate) iter: Iter<'il, Ty>,
    pub(crate) other: &'il InversionList<Ty>,
}

impl<Ty: PrimInt> Iterator for Intersection<'_, Ty> {
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

impl<Ty: PrimInt> FusedIterator for Intersection<'_, Ty> {}
