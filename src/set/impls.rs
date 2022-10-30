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
        let iter = iterable.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            (iter.size_hint().0 + 1) / 2
        };
        self.reserve(reserve);
        iter.for_each(move |elem| {
            self.insert(elem);
        });
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
        self.extend(iterable.into_iter().copied());
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
        let iter = iter.into_iter();
        let lower = iter.size_hint().0;
        let mut map = VecSet::with_capacity(lower);
        map.extend(iter);
        map
    }
}

impl<T> From<Vec<T>> for VecSet<T>
where
    T: Eq,
{
    fn from(vec: Vec<T>) -> Self {
        VecSet::from_iter(vec)
    }
}

impl<T> From<&[T]> for VecSet<T>
where
    T: Clone + Eq,
{
    fn from(slice: &[T]) -> Self {
        VecSet::from_iter(slice.to_vec())
    }
}

impl<T> From<&mut [T]> for VecSet<T>
where
    T: Clone + Eq,
{
    fn from(slice: &mut [T]) -> Self {
        VecSet::from_iter(slice.to_vec())
    }
}

impl<T, const N: usize> From<[T; N]> for VecSet<T>
where
    T: Eq,
{
    fn from(arr: [T; N]) -> Self {
        VecSet::from_iter(arr)
    }
}

impl<T> PartialEq for VecSet<T>
where
    T: Eq,
{
    fn eq(&self, other: &VecSet<T>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter().all(|key| other.contains(key))
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
