use std::marker::PhantomData;
pub struct Difference<'il> {
    pub(crate) _pd: PhantomData<&'il ()>,
}
pub struct SymmetricDifference<'il> {
    pub(crate) _pd: PhantomData<&'il ()>,
}
pub struct Union<'il> {
    pub(crate) _pd: PhantomData<&'il ()>,
}
pub struct Intersection<'il> {
    pub(crate) _pd: PhantomData<&'il ()>,
}
