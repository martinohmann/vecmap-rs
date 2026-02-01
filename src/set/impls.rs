use core::ops::{BitAnd, BitOr, BitXor, Index, Sub};

use super::VecSet;
use alloc::vec::Vec;

impl<T> Default for VecSet<T> {
    fn default() -> Self {
        VecSet::new()
    }
}

impl<T> Index<usize> for VecSet<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get_index(index).expect("VecSet: index out of bounds")
    }
}

impl<T> Extend<T> for VecSet<T>
where
    T: Eq,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.base.extend(iterable);
    }
}

impl<'a, T> Extend<&'a T> for VecSet<T>
where
    T: 'a + Copy + Eq,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.base.extend(iterable.into_iter().copied());
    }
}

impl<T> FromIterator<T> for VecSet<T>
where
    T: Eq,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        VecSet {
            base: iter.into_iter().collect(),
        }
    }
}

impl<T> From<Vec<T>> for VecSet<T>
where
    T: Eq,
{
    /// Constructs set from a vector.
    ///
    /// **Note**: This conversion has a quadratic complexity because the
    /// conversion preserves order of elements while at the same time having to
    /// make sure no duplicate elements exist. To avoid it, sort and deduplicate
    /// the vector and use [`VecSet::from_vec_unchecked`] instead.
    fn from(vec: Vec<T>) -> Self {
        VecSet {
            base: vec.into(),
        }
    }
}

impl<T> From<&[T]> for VecSet<T>
where
    T: Clone + Eq,
{
    fn from(slice: &[T]) -> Self {
        VecSet {
            base: slice.into(),
        }
    }
}

impl<T> From<&mut [T]> for VecSet<T>
where
    T: Clone + Eq,
{
    fn from(slice: &mut [T]) -> Self {
        VecSet {
            base: slice.into(),
        }
    }
}

impl<T, const N: usize> From<[T; N]> for VecSet<T>
where
    T: Eq,
{
    fn from(arr: [T; N]) -> Self {
        VecSet { base: arr.into() }
    }
}

impl<T> PartialEq for VecSet<T>
where
    T: Eq,
{
    fn eq(&self, other: &VecSet<T>) -> bool {
        self.base == other.base
    }
}

impl<T> Eq for VecSet<T> where T: Eq {}

impl<T> BitAnd<&VecSet<T>> for &VecSet<T>
where
    T: Eq + Clone,
{
    type Output = VecSet<T>;

    /// Returns the set intersection, cloned into a new set.
    ///
    /// Values are collected in the same order that they appear in `self`.
    fn bitand(self, other: &VecSet<T>) -> Self::Output {
        self.intersection(other).cloned().collect()
    }
}

impl<T> BitOr<&VecSet<T>> for &VecSet<T>
where
    T: Eq + Clone,
{
    type Output = VecSet<T>;

    /// Returns the set union, cloned into a new set.
    ///
    /// Values from `self` are collected in their original order, followed by values that are
    /// unique to `other` in their original order.
    fn bitor(self, other: &VecSet<T>) -> Self::Output {
        self.union(other).cloned().collect()
    }
}

impl<T> BitXor<&VecSet<T>> for &VecSet<T>
where
    T: Eq + Clone,
{
    type Output = VecSet<T>;

    /// Returns the set symmetric-difference, cloned into a new set.
    ///
    /// Values from `self` are collected in their original order, followed by values from `other`
    /// in their original order.
    fn bitxor(self, other: &VecSet<T>) -> Self::Output {
        self.symmetric_difference(other).cloned().collect()
    }
}

impl<T> Sub<&VecSet<T>> for &VecSet<T>
where
    T: Eq + Clone,
{
    type Output = VecSet<T>;

    /// Returns the set difference, cloned into a new set.
    ///
    /// Values are collected in the same order that they appear in `self`.
    fn sub(self, other: &VecSet<T>) -> Self::Output {
        self.difference(other).cloned().collect()
    }
}
