use super::{Entries, SortedVecSet};
use alloc::vec::{self, Vec};
use core::cmp::Ordering;
use core::fmt;
use core::iter::FusedIterator;
use core::iter::Peekable;
use core::ops::RangeBounds;
use core::slice;

macro_rules! impl_iterator {
    ($ty:ident<$($lt:lifetime,)*$($gen:ident),+>, $item:ty) => {
        impl<$($lt,)*$($gen),+> Iterator for $ty<$($lt,)*$($gen),+> {
            type Item = $item;

            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next()
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.iter.size_hint()
            }
        }

        impl<$($lt,)*$($gen),+> DoubleEndedIterator for $ty<$($lt,)*$($gen),+> {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.iter.next_back()
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
                let iter = self.iter.as_slice().iter();
                f.debug_list().entries(iter).finish()
            }
        }
    };
}

impl<T> IntoIterator for SortedVecSet<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self.into_entries())
    }
}

impl<'a, T> IntoIterator for &'a SortedVecSet<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator over the elements of a [`SortedVecSet`].
///
/// This `struct` is created by the [`iter`] method on [`SortedVecSet`].
///
/// [`iter`]: SortedVecSet::iter
pub struct Iter<'a, T> {
    iter: slice::Iter<'a, T>,
}

impl<'a, T> Iter<'a, T> {
    pub(super) fn new(entries: &'a [T]) -> Iter<'a, T> {
        Iter {
            iter: entries.iter(),
        }
    }
}

impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter {
            iter: self.iter.clone(),
        }
    }
}

impl_iterator!(Iter<'a, T>, &'a T);

/// An owning iterator over the elements of a [`SortedVecSet`].
///
/// This `struct` is created by the [`into_iter`] method on [`SortedVecSet`].
///
/// [`into_iter`]: IntoIterator::into_iter
pub struct IntoIter<T> {
    iter: vec::IntoIter<T>,
}

impl<T> IntoIter<T> {
    pub(super) fn new(entries: Vec<T>) -> IntoIter<T> {
        IntoIter {
            iter: entries.into_iter(),
        }
    }
}

impl<T> Clone for IntoIter<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        IntoIter {
            iter: self.iter.clone(),
        }
    }
}

impl_iterator!(IntoIter<T>, T);

/// An iterator over a sub-range of elements in a [`SortedVecSet`].
///
/// This `struct` is created by the [`range`] method on [`SortedVecSet`].
///
/// [`range`]: SortedVecSet::range
pub struct Range<'a, T> {
    iter: slice::Iter<'a, T>,
}

impl<'a, T> Range<'a, T> {
    pub(super) fn new(entries: &'a [T]) -> Range<'a, T> {
        Range {
            iter: entries.iter(),
        }
    }
}

impl<T> Clone for Range<'_, T> {
    fn clone(&self) -> Self {
        Range {
            iter: self.iter.clone(),
        }
    }
}

impl_iterator!(Range<'a, T>, &'a T);

/// A lazy iterator producing elements in the difference of [`SortedVecSet`]s.
///
/// Both sides are walked in parallel, so this runs in *O*(*n* + *m*).
///
/// This `struct` is created by the [`difference`] method on [`SortedVecSet`].
///
/// [`difference`]: SortedVecSet::difference
pub struct Difference<'a, T> {
    iter: Peekable<slice::Iter<'a, T>>,
    other: Peekable<slice::Iter<'a, T>>,
}

impl<'a, T> Difference<'a, T> {
    pub(super) fn new(set: &'a SortedVecSet<T>, other: &'a SortedVecSet<T>) -> Difference<'a, T> {
        Difference {
            iter: set.as_slice().iter().peekable(),
            other: other.as_slice().iter().peekable(),
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
            match (self.iter.peek(), self.other.peek()) {
                (Some(s), Some(o)) => match s.cmp(o) {
                    Ordering::Less => return self.iter.next(),
                    Ordering::Equal => {
                        self.iter.next();
                        self.other.next();
                    }
                    Ordering::Greater => {
                        self.other.next();
                    }
                },
                (Some(_), None) => return self.iter.next(),
                (None, _) => return None,
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let self_len = self.iter.len();
        let other_len = self.other.len();
        (self_len.saturating_sub(other_len), Some(self_len))
    }
}

impl<T> FusedIterator for Difference<'_, T> where T: Ord {}

impl<T> Clone for Difference<'_, T> {
    fn clone(&self) -> Self {
        Difference {
            iter: self.iter.clone(),
            other: self.other.clone(),
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

/// A lazy iterator producing elements in the intersection of [`SortedVecSet`]s.
///
/// Both sides are walked in parallel, so this runs in *O*(*n* + *m*).
///
/// [`intersection`]: SortedVecSet::intersection
pub struct Intersection<'a, T> {
    self_iter: Peekable<slice::Iter<'a, T>>,
    other_iter: Peekable<slice::Iter<'a, T>>,
}

impl<'a, T> Intersection<'a, T> {
    pub(super) fn new(set: &'a SortedVecSet<T>, other: &'a SortedVecSet<T>) -> Intersection<'a, T> {
        Intersection {
            self_iter: set.as_slice().iter().peekable(),
            other_iter: other.as_slice().iter().peekable(),
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
            match (self.self_iter.peek(), self.other_iter.peek()) {
                (Some(s), Some(o)) => match s.cmp(o) {
                    Ordering::Less => {
                        self.self_iter.next();
                    }
                    Ordering::Equal => {
                        self.other_iter.next();
                        return self.self_iter.next();
                    }
                    Ordering::Greater => {
                        self.other_iter.next();
                    }
                },
                _ => return None,
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.self_iter.len().min(self.other_iter.len())))
    }
}

impl<T> FusedIterator for Intersection<'_, T> where T: Ord {}

impl<T> Clone for Intersection<'_, T> {
    fn clone(&self) -> Self {
        Intersection {
            self_iter: self.self_iter.clone(),
            other_iter: self.other_iter.clone(),
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

/// A lazy iterator producing elements in the symmetric difference of [`SortedVecSet`]s.
///
/// Both sides are walked in parallel, so this runs in *O*(*n* + *m*).
///
/// [`symmetric_difference`]: SortedVecSet::symmetric_difference
pub struct SymmetricDifference<'a, T> {
    iter: Peekable<slice::Iter<'a, T>>,
    other: Peekable<slice::Iter<'a, T>>,
}

impl<'a, T> SymmetricDifference<'a, T> {
    pub(super) fn new(
        set: &'a SortedVecSet<T>,
        other: &'a SortedVecSet<T>,
    ) -> SymmetricDifference<'a, T> {
        SymmetricDifference {
            iter: set.as_slice().iter().peekable(),
            other: other.as_slice().iter().peekable(),
        }
    }
}

impl<'a, T> Iterator for SymmetricDifference<'a, T>
where
    T: Ord,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match (self.iter.peek(), self.other.peek()) {
                (Some(s), Some(o)) => match s.cmp(o) {
                    Ordering::Less => return self.iter.next(),
                    Ordering::Equal => {
                        self.iter.next();
                        self.other.next();
                    }
                    Ordering::Greater => return self.other.next(),
                },
                (Some(_), None) => return self.iter.next(),
                (None, Some(_)) => return self.other.next(),
                (None, None) => return None,
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.iter.len() + self.other.len()))
    }
}

impl<T> FusedIterator for SymmetricDifference<'_, T> where T: Ord {}

impl<T> Clone for SymmetricDifference<'_, T> {
    fn clone(&self) -> Self {
        SymmetricDifference {
            iter: self.iter.clone(),
            other: self.other.clone(),
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

/// A lazy iterator producing elements in the union of [`SortedVecSet`]s, in sort order and with no
/// duplicates.
///
/// Both sides are walked in parallel, so this runs in *O*(*n* + *m*).
///
/// [`union`]: SortedVecSet::union
pub struct Union<'a, T> {
    self_iter: Peekable<slice::Iter<'a, T>>,
    other_iter: Peekable<slice::Iter<'a, T>>,
}

impl<'a, T> Union<'a, T> {
    pub(super) fn new(set: &'a SortedVecSet<T>, other: &'a SortedVecSet<T>) -> Union<'a, T> {
        Union {
            self_iter: set.as_slice().iter().peekable(),
            other_iter: other.as_slice().iter().peekable(),
        }
    }
}

impl<'a, T> Iterator for Union<'a, T>
where
    T: Ord,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.self_iter.peek(), self.other_iter.peek()) {
            (Some(s), Some(o)) => match s.cmp(o) {
                Ordering::Less => self.self_iter.next(),
                Ordering::Equal => {
                    self.other_iter.next();
                    self.self_iter.next()
                }
                Ordering::Greater => self.other_iter.next(),
            },
            (Some(_), None) => self.self_iter.next(),
            (None, Some(_)) => self.other_iter.next(),
            (None, None) => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let self_len = self.self_iter.len();
        let other_len = self.other_iter.len();
        (self_len.max(other_len), Some(self_len + other_len))
    }
}

impl<T> FusedIterator for Union<'_, T> where T: Ord {}

impl<T> Clone for Union<'_, T> {
    fn clone(&self) -> Self {
        Union {
            self_iter: self.self_iter.clone(),
            other_iter: self.other_iter.clone(),
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

/// A draining iterator for [`SortedVecSet`].
///
/// [`drain`]: SortedVecSet::drain
pub struct Drain<'a, T> {
    iter: vec::Drain<'a, T>,
}

impl<'a, T> Drain<'a, T> {
    pub(super) fn new<R>(set: &'a mut SortedVecSet<T>, range: R) -> Drain<'a, T>
    where
        R: RangeBounds<usize>,
    {
        Drain {
            iter: set.base.drain(range),
        }
    }
}

impl_iterator!(Drain<'a, T>, T);
