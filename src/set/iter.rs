use super::*;
use alloc::vec;
use core::fmt;
use core::iter::FusedIterator;
use core::slice;

macro_rules! impl_iterator {
    ($ty:ident<$($lt:lifetime,)*$($gen:ident),+>, $item:ty, $map:expr) => {
        impl<$($lt,)*$($gen),+> Iterator for $ty<$($lt,)*$($gen),+> {
            type Item = $item;

            fn next(&mut self) -> Option<Self::Item> {
                self.entries.next().map($map)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.entries.size_hint()
            }
        }

        impl<$($lt,)*$($gen),+> DoubleEndedIterator for $ty<$($lt,)*$($gen),+> {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.entries.next_back().map($map)
            }
        }

        impl<$($lt,)*$($gen),+> ExactSizeIterator for $ty<$($lt,)*$($gen),+> {
            fn len(&self) -> usize {
                self.entries.len()
            }
        }

        impl<$($lt,)*$($gen),+> FusedIterator for $ty<$($lt,)*$($gen),+> {}

        impl<$($lt,)*$($gen),+> fmt::Debug for $ty<$($lt,)*$($gen),+>
        where
            T: fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let iter = self.entries.as_slice().iter().map(Slot::key_ref);
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
    entries: slice::Iter<'a, Slot<T, ()>>,
}

impl<'a, T> Iter<'a, T> {
    pub(super) fn new(entries: &'a [Slot<T, ()>]) -> Iter<'a, T> {
        Iter {
            entries: entries.iter(),
        }
    }
}

impl_iterator!(Iter<'a, T>, &'a T, Slot::key_ref);

/// An owning iterator over the elements of a `VecSet`.
///
/// This `struct` is created by the [`into_iter`] method on [`VecSet`] (provided by the
/// [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<T> {
    entries: vec::IntoIter<Slot<T, ()>>,
}

impl<T> IntoIter<T> {
    pub(super) fn new(entries: Vec<Slot<T, ()>>) -> IntoIter<T> {
        IntoIter {
            entries: entries.into_iter(),
        }
    }
}

impl_iterator!(IntoIter<T>, T, Slot::key);
