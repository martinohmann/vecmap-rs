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
            K: fmt::Debug,
            V: fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let iter = self.entries.as_slice().iter().map(Slot::refs);
                f.debug_list().entries(iter).finish()
            }
        }
    };
}

impl<K, V> IntoIterator for VecMap<K, V> {
    type Item = (K, V);

    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self.into_entries())
    }
}

impl<'a, K, V> IntoIterator for &'a VecMap<K, V> {
    type Item = (&'a K, &'a V);

    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut VecMap<K, V> {
    type Item = (&'a K, &'a mut V);

    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// An iterator over the entries of a `VecMap`.
///
/// This `struct` is created by the [`iter`] method on [`VecMap`]. See its documentation for more.
///
/// [`iter`]: VecMap::iter
pub struct Iter<'a, K, V> {
    entries: slice::Iter<'a, Slot<K, V>>,
}

impl<'a, K, V> Iter<'a, K, V> {
    pub(super) fn new(entries: &'a [Slot<K, V>]) -> Iter<'a, K, V> {
        Iter {
            entries: entries.iter(),
        }
    }
}

impl_iterator!(Iter<'a, K, V>, (&'a K, &'a V), Slot::refs);

/// A mutable iterator over the entries of a `VecMap`.
///
/// This `struct` is created by the [`iter_mut`] method on [`VecMap`]. See its documentation for
/// more.
///
/// [`iter_mut`]: VecMap::iter_mut
pub struct IterMut<'a, K, V> {
    entries: slice::IterMut<'a, Slot<K, V>>,
}

impl<'a, K, V> IterMut<'a, K, V> {
    pub(super) fn new(entries: &'a mut [Slot<K, V>]) -> IterMut<'a, K, V> {
        IterMut {
            entries: entries.iter_mut(),
        }
    }
}

impl_iterator!(IterMut<'a, K, V>, (&'a K, &'a mut V), Slot::ref_mut);

/// An owning iterator over the entries of a `VecMap`.
///
/// This `struct` is created by the [`into_iter`] method on [`VecMap`] (provided by the
/// [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<K, V> {
    entries: vec::IntoIter<Slot<K, V>>,
}

impl<K, V> IntoIter<K, V> {
    pub(super) fn new(entries: Vec<Slot<K, V>>) -> IntoIter<K, V> {
        IntoIter {
            entries: entries.into_iter(),
        }
    }
}

impl_iterator!(IntoIter<K, V>, (K, V), Slot::key_value);

/// An iterator over the keys of a `VecMap`.
///
/// This `struct` is created by the [`keys`] method on [`VecMap`]. See its documentation for more.
///
/// [`keys`]: VecMap::keys
pub struct Keys<'a, K, V> {
    entries: slice::Iter<'a, Slot<K, V>>,
}

impl<'a, K, V> Keys<'a, K, V> {
    pub(super) fn new(entries: &'a [Slot<K, V>]) -> Keys<'a, K, V> {
        Keys {
            entries: entries.iter(),
        }
    }
}

impl_iterator!(Keys<'a, K, V>, &'a K, Slot::key_ref);

/// An owning iterator over the keys of a `VecMap`.
///
/// This `struct` is created by the [`into_keys`] method on [`VecMap`]. See its documentation for
/// more.
///
/// [`into_keys`]: VecMap::into_keys
pub struct IntoKeys<K, V> {
    entries: vec::IntoIter<Slot<K, V>>,
}

impl<K, V> IntoKeys<K, V> {
    pub(super) fn new(entries: Vec<Slot<K, V>>) -> IntoKeys<K, V> {
        IntoKeys {
            entries: entries.into_iter(),
        }
    }
}

impl_iterator!(IntoKeys<K, V>, K, Slot::key);

/// An iterator over the values of a `VecMap`.
///
/// This `struct` is created by the [`values`] method on [`VecMap`]. See its documentation for
/// more.
///
/// [`values`]: VecMap::values
pub struct Values<'a, K, V> {
    entries: slice::Iter<'a, Slot<K, V>>,
}

impl<'a, K, V> Values<'a, K, V> {
    pub(super) fn new(entries: &'a [Slot<K, V>]) -> Values<'a, K, V> {
        Values {
            entries: entries.iter(),
        }
    }
}

impl_iterator!(Values<'a, K, V>, &'a V, Slot::value_ref);

/// A mutable iterator over the values of a `VecMap`.
///
/// This `struct` is created by the [`values_mut`] method on [`VecMap`]. See its documentation for
/// more.
///
/// [`values_mut`]: VecMap::values_mut
pub struct ValuesMut<'a, K, V> {
    entries: slice::IterMut<'a, Slot<K, V>>,
}

impl<'a, K, V> ValuesMut<'a, K, V> {
    pub(super) fn new(entries: &'a mut [Slot<K, V>]) -> ValuesMut<'a, K, V> {
        ValuesMut {
            entries: entries.iter_mut(),
        }
    }
}

impl_iterator!(ValuesMut<'a, K, V>, &'a mut V, Slot::value_mut);

/// An owning iterator over the values of a `VecMap`.
///
/// This `struct` is created by the [`into_values`] method on [`VecMap`]. See its documentation
/// for more.
///
/// [`into_values`]: VecMap::into_values
pub struct IntoValues<K, V> {
    entries: vec::IntoIter<Slot<K, V>>,
}

impl<K, V> IntoValues<K, V> {
    pub(super) fn new(entries: Vec<Slot<K, V>>) -> IntoValues<K, V> {
        IntoValues {
            entries: entries.into_iter(),
        }
    }
}

impl_iterator!(IntoValues<K, V>, V, Slot::value);

/// A draining iterator for `VecMap`.
///
/// This `struct` is created by the [`drain`] method on [`VecMap`]. See its documentation for
/// more.
///
/// [`drain`]: VecMap::drain
pub struct Drain<'a, K, V> {
    entries: vec::Drain<'a, Slot<K, V>>,
}

impl<'a, K, V> Drain<'a, K, V> {
    pub(super) fn new<R>(map: &'a mut VecMap<K, V>, range: R) -> Drain<'a, K, V>
    where
        R: RangeBounds<usize>,
    {
        Drain {
            entries: map.entries.drain(range),
        }
    }
}

impl_iterator!(Drain<'a, K, V>, (K, V), Slot::key_value);
