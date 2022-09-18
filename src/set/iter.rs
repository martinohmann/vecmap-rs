use super::*;
use crate::map;
use alloc::vec;
use core::fmt;
use core::iter::{Chain, FusedIterator};
use core::slice;

macro_rules! impl_iterator {
    ($ty:ident<$($lt:lifetime,)*$($gen:ident),+>, $item:ty, $map:expr) => {
        impl<$($lt,)*$($gen),+> Iterator for $ty<$($lt,)*$($gen),+> {
            type Item = $item;

            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next().map($map)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.iter.size_hint()
            }
        }

        impl<$($lt,)*$($gen),+> DoubleEndedIterator for $ty<$($lt,)*$($gen),+> {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.iter.next_back().map($map)
            }
        }

        impl<$($lt,)*$($gen),+> ExactSizeIterator for $ty<$($lt,)*$($gen),+> {
            fn len(&self) -> usize {
                self.iter.len()
            }
        }

        impl<$($lt,)*$($gen),+> FusedIterator for $ty<$($lt,)*$($gen),+> {}

        impl<$($lt,)*$($gen),+> fmt::Debug for $ty<$($lt,)*$($gen),+>
        where
            T: fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let iter = self.iter.as_slice().iter().map(Slot::key_ref);
                f.debug_list().entries(iter).finish()
            }
        }
    };
}

impl<T> IntoIterator for VecSet<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self.into_entries())
    }
}

impl<'a, T> IntoIterator for &'a VecSet<T> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator over the elements of a `VecSet`.
///
/// This `struct` is created by the [`iter`] method on [`VecSet`]. See its documentation for more.
///
/// [`iter`]: VecSet::iter
pub struct Iter<'a, T> {
    iter: slice::Iter<'a, Slot<T, ()>>,
}

impl<'a, T> Iter<'a, T> {
    pub(super) fn new(entries: &'a [Slot<T, ()>]) -> Iter<'a, T> {
        Iter {
            iter: entries.iter(),
        }
    }
}

impl_iterator!(Iter<'a, T>, &'a T, Slot::key_ref);

impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter {
            iter: self.iter.clone(),
        }
    }
}

/// An owning iterator over the elements of a `VecSet`.
///
/// This `struct` is created by the [`into_iter`] method on [`VecSet`] (provided by the
/// [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<T> {
    iter: vec::IntoIter<Slot<T, ()>>,
}

impl<T> IntoIter<T> {
    pub(super) fn new(entries: Vec<Slot<T, ()>>) -> IntoIter<T> {
        IntoIter {
            iter: entries.into_iter(),
        }
    }
}

impl_iterator!(IntoIter<T>, T, Slot::key);

/// A lazy iterator producing elements in the difference of `VecSet`s.
///
/// This `struct` is created by the [`difference`] method on [`VecSet`]. See its documentation for
/// more.
///
/// [`VecSet`]: struct.VecSet.html
/// [`difference`]: struct.VecSet.html#method.difference
pub struct Difference<'a, T> {
    iter: Iter<'a, T>,
    other: &'a VecSet<T>,
}

impl<'a, T> Difference<'a, T> {
    pub(super) fn new(set: &'a VecSet<T>, other: &'a VecSet<T>) -> Difference<'a, T> {
        Difference {
            iter: set.iter(),
            other,
        }
    }
}

impl<'a, T> Iterator for Difference<'a, T>
where
    T: Eq,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let item = self.iter.next()?;

            if !self.other.contains(item) {
                return Some(item);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1)
    }
}

impl<T> DoubleEndedIterator for Difference<'_, T>
where
    T: Eq,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            let item = self.iter.next_back()?;

            if !self.other.contains(item) {
                return Some(item);
            }
        }
    }
}

impl<T> FusedIterator for Difference<'_, T> where T: Eq {}

impl<T> Clone for Difference<'_, T> {
    fn clone(&self) -> Self {
        Difference {
            iter: self.iter.clone(),
            ..*self
        }
    }
}

impl<T> fmt::Debug for Difference<'_, T>
where
    T: fmt::Debug + Eq,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A lazy iterator producing elements in the intersection of `VecSet`s.
///
/// This `struct` is created by the [`intersection`] method on [`VecSet`]. See its documentation
/// for more.
///
/// [`VecSet`]: struct.VecSet.html
/// [`intersection`]: struct.VecSet.html#method.intersection
pub struct Intersection<'a, T> {
    iter: Iter<'a, T>,
    other: &'a VecSet<T>,
}

impl<'a, T> Intersection<'a, T> {
    pub(super) fn new(set: &'a VecSet<T>, other: &'a VecSet<T>) -> Intersection<'a, T> {
        Intersection {
            iter: set.iter(),
            other,
        }
    }
}

impl<'a, T> Iterator for Intersection<'a, T>
where
    T: Eq,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let item = self.iter.next()?;

            if self.other.contains(item) {
                return Some(item);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.iter.size_hint().1)
    }
}

impl<T> DoubleEndedIterator for Intersection<'_, T>
where
    T: Eq,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            let item = self.iter.next_back()?;

            if self.other.contains(item) {
                return Some(item);
            }
        }
    }
}

impl<T> FusedIterator for Intersection<'_, T> where T: Eq {}

impl<T> Clone for Intersection<'_, T> {
    fn clone(&self) -> Self {
        Intersection {
            iter: self.iter.clone(),
            ..*self
        }
    }
}

impl<T> fmt::Debug for Intersection<'_, T>
where
    T: fmt::Debug + Eq,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A lazy iterator producing elements in the symmetric difference of `VecSet`s.
///
/// This `struct` is created by the [`symmetric_difference`] method on [`VecSet`]. See its
/// documentation for more.
///
/// [`VecSet`]: struct.VecSet.html
/// [`symmetric_difference`]: struct.VecSet.html#method.symmetric_difference
pub struct SymmetricDifference<'a, T> {
    iter: Chain<Difference<'a, T>, Difference<'a, T>>,
}

impl<'a, T> SymmetricDifference<'a, T>
where
    T: Eq,
{
    pub(super) fn new(set: &'a VecSet<T>, other: &'a VecSet<T>) -> SymmetricDifference<'a, T> {
        SymmetricDifference {
            iter: set.difference(other).chain(other.difference(set)),
        }
    }
}

impl<'a, T> Iterator for SymmetricDifference<'a, T>
where
    T: Eq,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> DoubleEndedIterator for SymmetricDifference<'_, T>
where
    T: Eq,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl<T> FusedIterator for SymmetricDifference<'_, T> where T: Eq {}

impl<T> Clone for SymmetricDifference<'_, T> {
    fn clone(&self) -> Self {
        SymmetricDifference {
            iter: self.iter.clone(),
        }
    }
}

impl<T> fmt::Debug for SymmetricDifference<'_, T>
where
    T: fmt::Debug + Eq,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A lazy iterator producing elements in the union of `VecSet`s.
///
/// This `struct` is created by the [`union`] method on [`VecSet`]. See its documentation for more.
///
/// [`VecSet`]: struct.VecSet.html
/// [`union`]: struct.VecSet.html#method.union
pub struct Union<'a, T> {
    iter: Chain<Iter<'a, T>, Difference<'a, T>>,
}

impl<'a, T> Union<'a, T>
where
    T: Eq,
{
    pub(super) fn new(set: &'a VecSet<T>, other: &'a VecSet<T>) -> Union<'a, T> {
        Union {
            iter: set.iter().chain(other.difference(set)),
        }
    }
}

impl<'a, T> Iterator for Union<'a, T>
where
    T: Eq,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> DoubleEndedIterator for Union<'_, T>
where
    T: Eq,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl<T> FusedIterator for Union<'_, T> where T: Eq {}

impl<T> Clone for Union<'_, T> {
    fn clone(&self) -> Self {
        Union {
            iter: self.iter.clone(),
        }
    }
}

impl<T> fmt::Debug for Union<'_, T>
where
    T: fmt::Debug + Eq,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A draining iterator for `VecSet`.
///
/// This `struct` is created by the [`drain`] method on [`VecSet`]. See its documentation for
/// more.
///
/// [`drain`]: VecSet::drain
pub struct Drain<'a, T> {
    iter: map::Drain<'a, T, ()>,
}

impl<'a, T> Drain<'a, T> {
    pub(super) fn new<R>(set: &'a mut VecSet<T>, range: R) -> Drain<'a, T>
    where
        R: RangeBounds<usize>,
    {
        Drain {
            iter: set.base.drain(range),
        }
    }
}

impl<'a, T> Iterator for Drain<'a, T>
where
    T: Eq,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> DoubleEndedIterator for Drain<'_, T>
where
    T: Eq,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, _)| k)
    }
}

impl<T> FusedIterator for Drain<'_, T> where T: Eq {}
