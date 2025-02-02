mod impls;

use super::{Iter, Slot};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::ptr;

/// A dynamically-sized slice of keys in a [`VecSet`][crate::VecSet].
///
/// This supports indexed operations much like a `[T]` slice.
#[repr(transparent)]
pub struct SetSlice<T> {
    entries: [Slot<T>],
}

impl<T> SetSlice<T> {
    pub(super) const fn from_slice(entries: &[Slot<T>]) -> &Self {
        // SAFETY: `&[Slot<T>]` and `&SetSlice<T>` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<T>]>(entries) as *const Self) }
    }

    pub(super) const fn from_mut_slice(entries: &mut [Slot<T>]) -> &mut SetSlice<T> {
        // SAFETY: `&mut [Slot<T>]` and `&mut SetSlice<T>` have the same memory layout.
        unsafe { &mut *(ptr::from_mut::<[Slot<T>]>(entries) as *mut SetSlice<T>) }
    }

    /// Extracts a slice containing the set slice elements.
    ///
    /// This method provides access to the backing [`&[T]`][core::slice] of the `SetSlice<T>`.
    pub const fn as_slice(&self) -> &[T] {
        // SAFETY: `&[Slot<T>]` and `&[T]` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<T>]>(&self.entries) as *const [T]) }
    }

    /// Returns an empty set slice.
    ///
    /// ```
    /// use vecmap::set::SetSlice;
    ///
    /// let slice: &SetSlice<u32> = SetSlice::new();
    /// assert!(slice.is_empty());
    /// ```
    pub const fn new<'a>() -> &'a Self {
        SetSlice::from_slice(&[])
    }

    /// Returns an empty mutable set slice.
    ///
    /// ```
    /// use vecmap::set::SetSlice;
    ///
    /// let slice: &mut SetSlice<u32> = SetSlice::new_mut();
    /// assert!(slice.is_empty());
    /// ```
    pub const fn new_mut<'a>() -> &'a mut Self {
        SetSlice::from_mut_slice(&mut [])
    }

    /// Returns the number of entries in the set slice, also referred to as its 'length'.
    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if the set slice contains no entries.
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Copies the set slice elements into a new `Vec<T>`.
    pub fn to_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.iter().cloned().collect()
    }
}

// Iterator adapters.
impl<T> SetSlice<T> {
    /// An iterator visiting all elements in insertion order. The iterator element type is
    /// `&'a T`.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(&self.entries)
    }
}

// Lookup operations.
impl<T> SetSlice<T> {
    /// Return `true` if an equivalent to `key` exists in the set.
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(value).is_some()
    }

    /// Get the first element.
    pub fn first(&self) -> Option<&T> {
        self.entries.first().map(Slot::key)
    }

    /// Get the last element.
    pub fn last(&self) -> Option<&T> {
        self.entries.last().map(Slot::key)
    }

    /// Returns a reference to the value in the set slice, if any, that is equal to the given
    /// value.
    ///
    /// The value may be any borrowed form of the set slice's value type, but [`Eq`] on the
    /// borrowed form *must* match those for the value type.
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        self.get_index_of(value)
            .map(|index| self.entries[index].key())
    }

    /// Return references to the element stored at `index`, if it is present, else `None`.
    pub fn get_index(&self, index: usize) -> Option<&T> {
        self.entries.get(index).map(Slot::key)
    }

    /// Returns the index and a reference to the value in the set slice, if any, that is equal to
    /// the given value.
    ///
    /// The value may be any borrowed form of the set's value type, but [`Eq`] on the borrowed form
    /// *must* match those for the value type.
    pub fn get_full<Q>(&self, value: &Q) -> Option<(usize, &T)>
    where
        T: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        self.get_index_of(value)
            .map(|index| (index, self.entries[index].key()))
    }

    /// Return item index, if it exists in the set slice.
    pub fn get_index_of<Q>(&self, value: &Q) -> Option<usize>
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        if self.entries.is_empty() {
            return None;
        }

        self.entries
            .iter()
            .position(|slot| slot.key().borrow() == value)
    }
}

// Mutation operations.
impl<T> SetSlice<T> {
    /// Reverses the order of entries in the set slice, in place.
    pub fn reverse(&mut self) {
        self.entries.reverse();
    }

    /// Swaps the position of two elements in the set slice.
    ///
    /// # Arguments
    ///
    /// * a - The index of the first element
    /// * b - The index of the second element
    ///
    /// # Panics
    ///
    /// Panics if `a` or `b` are out of bounds.
    pub fn swap_indices(&mut self, a: usize, b: usize) {
        self.entries.swap(a, b);
    }
}

// Sort operations.
impl<T> SetSlice<T> {
    /// Sorts the set slice.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*))
    /// worst-case.
    ///
    /// When applicable, unstable sorting is preferred because it is generally faster than stable
    /// sorting and it doesn't allocate auxiliary memory. See
    /// [`sort_unstable`](Self::sort_unstable).
    pub fn sort(&mut self)
    where
        T: Ord,
    {
        self.entries.sort();
    }

    /// Sorts the set slice.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place (i.e., does not
    /// allocate), and *O*(*n* \* log(*n*)) worst-case.
    pub fn sort_unstable(&mut self)
    where
        T: Ord,
    {
        self.entries.sort_unstable();
    }

    /// Sorts the set slice with a comparator function.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*))
    /// worst-case.
    pub fn sort_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&T, &T) -> Ordering,
    {
        self.entries.sort_by(|a, b| compare(a.key(), b.key()));
    }

    /// Sorts the set slice with a comparator function.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place (i.e., does not
    /// allocate), and *O*(*n* \* log(*n*)) worst-case.
    pub fn sort_unstable_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&T, &T) -> Ordering,
    {
        self.entries
            .sort_unstable_by(|a, b| compare(a.key(), b.key()));
    }

    /// Sort the set slice’s values in place using a key extraction function.
    ///
    /// During sorting, the function is called at most once per entry, by using temporary storage
    /// to remember the results of its evaluation. The order of calls to the function is
    /// unspecified and may change between versions of `vecmap-rs` or the standard library.
    ///
    /// See [`slice::sort_by_cached_key`] for more details.
    pub fn sort_by_cached_key<K, F>(&mut self, mut sort_key: F)
    where
        K: Ord,
        F: FnMut(&T) -> K,
    {
        self.entries.sort_by_cached_key(|slot| sort_key(slot.key()));
    }
}

// Binary search operations.
impl<T> SetSlice<T> {
    /// Search over a sorted set slice for a value.
    ///
    /// Returns the position where that key is present, or the position where it can be inserted to
    /// maintain the sort. See [`slice::binary_search`] for more details.
    pub fn binary_search(&self, value: &T) -> Result<usize, usize>
    where
        T: Ord,
    {
        self.binary_search_by(|v| v.cmp(value))
    }

    /// Search over a sorted set slice with a comparator function.
    ///
    /// Returns the position where that value is present, or the position where it can be inserted
    /// to maintain the sort. See [`slice::binary_search_by`] for more details.
    pub fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> Ordering,
    {
        self.entries.binary_search_by(|slot| f(slot.key()))
    }

    /// Search over a sorted set slice with an extraction function.
    ///
    /// Returns the position where that value is present, or the position where it can be inserted
    /// to maintain the sort. See [`slice::binary_search_by_key`] for more details.
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> B,
        B: Ord,
    {
        self.entries.binary_search_by_key(b, |slot| f(slot.key()))
    }

    /// Returns the index of the partition point of a sorted set slice according to the given
    /// predicate (the index of the first element of the second partition).
    ///
    /// See [`slice::partition_point`] for more details.
    pub fn partition_point<P>(&self, mut pred: P) -> usize
    where
        P: FnMut(&T) -> bool,
    {
        self.entries.partition_point(|slot| pred(slot.key()))
    }
}
