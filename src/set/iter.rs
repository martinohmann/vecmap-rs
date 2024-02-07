use super::VecSet;
use alloc::vec::{self, Vec};
use core::fmt;
use core::iter::{Chain, FusedIterator};
use core::slice;

impl<T> IntoIterator for VecSet<T> {
    type Item = T;

    type IntoIter = vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.base.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a VecSet<T> {
    type Item = &'a T;

    type IntoIter = <&'a Vec<T> as core::iter::IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        (&self.base).into_iter()
    }
}

/// A lazy iterator producing elements in the difference of `VecSet`s.
///
/// This `struct` is created by the [`difference`] method on [`VecSet`]. See its documentation for
/// more.
///
/// [`VecSet`]: struct.VecSet.html
/// [`difference`]: struct.VecSet.html#method.difference
pub struct Difference<'a, T> {
    iter: slice::Iter<'a, T>,
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
    T: Ord,
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
    T: Ord,
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

impl<T> FusedIterator for Difference<'_, T> where T: Ord {}

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
    T: fmt::Debug + Ord,
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
    iter: slice::Iter<'a, T>,
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
    T: Ord,
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
    T: Ord,
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

impl<T> FusedIterator for Intersection<'_, T> where T: Ord {}

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
    T: fmt::Debug + Ord,
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
    T: Ord,
{
    pub(super) fn new(set: &'a VecSet<T>, other: &'a VecSet<T>) -> SymmetricDifference<'a, T> {
        SymmetricDifference {
            iter: set.difference(other).chain(other.difference(set)),
        }
    }
}

impl<'a, T> Iterator for SymmetricDifference<'a, T>
where
    T: Ord,
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
    T: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl<T> FusedIterator for SymmetricDifference<'_, T> where T: Ord {}

impl<T> Clone for SymmetricDifference<'_, T> {
    fn clone(&self) -> Self {
        SymmetricDifference {
            iter: self.iter.clone(),
        }
    }
}

impl<T> fmt::Debug for SymmetricDifference<'_, T>
where
    T: fmt::Debug + Ord,
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
    iter: Chain<slice::Iter<'a, T>, Difference<'a, T>>,
}

impl<'a, T> Union<'a, T>
where
    T: Ord,
{
    pub(super) fn new(set: &'a VecSet<T>, other: &'a VecSet<T>) -> Union<'a, T> {
        Union {
            iter: set.iter().chain(other.difference(set)),
        }
    }
}

impl<'a, T> Iterator for Union<'a, T>
where
    T: Ord,
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
    T: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl<T> FusedIterator for Union<'_, T> where T: Ord {}

impl<T> Clone for Union<'_, T> {
    fn clone(&self) -> Self {
        Union {
            iter: self.iter.clone(),
        }
    }
}

impl<T> fmt::Debug for Union<'_, T>
where
    T: fmt::Debug + Ord,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}
