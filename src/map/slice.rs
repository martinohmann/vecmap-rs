mod impls;

use super::{Iter, IterMut, Keys, Slot, Values, ValuesMut};
use crate::try_simplify_range;
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::ops::RangeBounds;
use core::ptr;

/// A dynamically-sized slice of key-value pairs in a [`VecMap`][crate::VecMap].
///
/// This supports indexed operations much like a `[(K, V)]` slice.
pub struct MapSlice<K, V> {
    entries: [Slot<K, V>],
}

impl<K, V> MapSlice<K, V> {
    pub(super) const fn from_slice(entries: &[Slot<K, V>]) -> &Self {
        // SAFETY: `&[Slot<K, V>]` and `&MapSlice<K, V>` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<K, V>]>(entries) as *const Self) }
    }

    pub(super) const fn from_mut_slice(entries: &mut [Slot<K, V>]) -> &mut Self {
        // SAFETY: `&mut [Slot<K, V>]` and `&mut MapSlice<K, V>` have the same memory layout.
        unsafe { &mut *(ptr::from_mut::<[Slot<K, V>]>(entries) as *mut Self) }
    }

    /// Extracts a slice containing the map slice entries.
    ///
    /// This method provides access to the backing [`&[(K, V)]`][core::slice] of the `MapSlice<K, V>`.
    pub const fn as_slice(&self) -> &[(K, V)] {
        // SAFETY: `&[Slot<K, V>]` and `&[(K, V)]` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<K, V>]>(&self.entries) as *const [(K, V)]) }
    }

    /// Returns an empty slice.
    ///
    /// ```
    /// use vecmap::map::MapSlice;
    ///
    /// let slice: &MapSlice<u32, &str> = MapSlice::new();
    /// assert!(slice.is_empty());
    /// ```
    pub const fn new<'a>() -> &'a Self {
        MapSlice::from_slice(&[])
    }

    /// Returns an empty mutable slice.
    ///
    /// ```
    /// use vecmap::map::MapSlice;
    ///
    /// let slice: &mut MapSlice<u32, &str> = MapSlice::new_mut();
    /// assert!(slice.is_empty());
    /// ```
    pub const fn new_mut<'a>() -> &'a mut Self {
        MapSlice::from_mut_slice(&mut [])
    }

    /// Returns the number of entries in the map slice, also referred to as its 'length'.
    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if the map slice contains no entries.
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Copies the map slice entries into a new `Vec<(K, V)>`.
    pub fn to_vec(&self) -> Vec<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }
}

// Iterator adapters.
impl<K, V> MapSlice<K, V> {
    /// An iterator visiting all key-value pairs in insertion order. The iterator element type is
    /// `(&'a K, &'a V)`.
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::new(&self.entries)
    }

    /// An iterator visiting all key-value pairs in insertion order, with mutable references to the
    /// values. The iterator element type is `(&'a K, &'a mut V)`.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut::new(&mut self.entries)
    }

    /// An iterator visiting all keys in insertion order. The iterator element type is `&'a K`.
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys::new(&self.entries)
    }

    /// An iterator visiting all values in insertion order. The iterator element type is `&'a V`.
    pub fn values(&self) -> Values<'_, K, V> {
        Values::new(&self.entries)
    }

    /// An iterator visiting all values mutably in insertion order. The iterator element type is
    /// `&'a mut V`.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut::new(&mut self.entries)
    }
}

// Lookup operations.
impl<K, V> MapSlice<K, V> {
    /// Return `true` if an equivalent to `key` exists in the map slice.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key).is_some()
    }

    /// Get the first key-value pair.
    pub fn first(&self) -> Option<(&K, &V)> {
        self.entries.first().map(Slot::refs)
    }

    /// Get the first key-value pair, with mutable access to the value.
    pub fn first_mut(&mut self) -> Option<(&K, &mut V)> {
        self.entries.first_mut().map(Slot::ref_mut)
    }

    /// Get the last key-value pair.
    pub fn last(&self) -> Option<(&K, &V)> {
        self.entries.last().map(Slot::refs)
    }

    /// Get the last key-value pair, with mutable access to the value.
    pub fn last_mut(&mut self) -> Option<(&K, &mut V)> {
        self.entries.last_mut().map(Slot::ref_mut)
    }

    /// Return a reference to the value stored for `key`, if it is present, else `None`.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| self.entries[index].value())
    }

    /// Return a mutable reference to the value stored for `key`, if it is present, else `None`.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| self.entries[index].value_mut())
    }

    /// Return references to the key-value pair stored at `index`, if it is present, else `None`.
    pub fn get_index(&self, index: usize) -> Option<(&K, &V)> {
        self.entries.get(index).map(Slot::refs)
    }

    /// Return a reference to the key and a mutable reference to the value stored at `index`, if it
    /// is present, else `None`.
    pub fn get_index_mut(&mut self, index: usize) -> Option<(&K, &mut V)> {
        self.entries.get_mut(index).map(Slot::ref_mut)
    }

    /// Returns a map slice of values in the given range of indices.
    ///
    /// Valid indices are `0 <= index < self.len()`.
    ///
    /// Computes in **O(1)** time.
    pub fn get_range<R>(&self, range: R) -> Option<&Self>
    where
        R: RangeBounds<usize>,
    {
        let range = try_simplify_range(range, self.entries.len())?;
        self.entries.get(range).map(MapSlice::from_slice)
    }

    /// Returns a mutable map slice of key-value pairs in the given range of indices.
    ///
    /// Valid indices are `0 <= index < self.len()`.
    pub fn get_range_mut<R>(&mut self, range: R) -> Option<&mut Self>
    where
        R: RangeBounds<usize>,
    {
        let range = try_simplify_range(range, self.entries.len())?;
        self.entries.get_mut(range).map(MapSlice::from_mut_slice)
    }

    /// Return the index and references to the key-value pair stored for `key`, if it is present,
    /// else `None`.
    pub fn get_full<Q>(&self, key: &Q) -> Option<(usize, &K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key).map(|index| {
            let (key, value) = self.entries[index].refs();
            (index, key, value)
        })
    }

    /// Return the index, a reference to the key and a mutable reference to the value stored for
    /// `key`, if it is present, else `None`.
    pub fn get_full_mut<Q>(&mut self, key: &Q) -> Option<(usize, &K, &mut V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key).map(|index| {
            let (key, value) = self.entries[index].ref_mut();
            (index, key, value)
        })
    }

    /// Return references to the key-value pair stored for `key`, if it is present, else `None`.
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| self.entries[index].refs())
    }

    /// Return item index, if it exists in the map slice.
    pub fn get_index_of<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        if self.entries.is_empty() {
            return None;
        }

        self.entries
            .iter()
            .position(|slot| slot.key().borrow() == key)
    }
}

// Mutation operations.
impl<K, V> MapSlice<K, V> {
    /// Reverses the order of entries in the map slice, in place.
    pub fn reverse(&mut self) {
        self.entries.reverse();
    }

    /// Swaps the position of two key-value pairs in the map slice.
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
impl<K, V> MapSlice<K, V> {
    /// Sorts the map slice by key.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*))
    /// worst-case.
    ///
    /// When applicable, unstable sorting is preferred because it is generally faster than stable
    /// sorting and it doesn't allocate auxiliary memory. See
    /// [`sort_unstable_keys`](Self::sort_unstable_keys).
    pub fn sort_keys(&mut self)
    where
        K: Ord,
    {
        self.entries.sort_by(|a, b| a.key().cmp(b.key()));
    }

    /// Sorts the map slice by key.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place (i.e., does not
    /// allocate), and *O*(*n* \* log(*n*)) worst-case.
    pub fn sort_unstable_keys(&mut self)
    where
        K: Ord,
    {
        self.entries.sort_unstable_by(|a, b| a.key().cmp(b.key()));
    }

    /// Sorts the map slice with a comparator function.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*))
    /// worst-case.
    pub fn sort_by<F>(&mut self, mut compare: F)
    where
        F: FnMut((&K, &V), (&K, &V)) -> Ordering,
    {
        self.entries.sort_by(|a, b| compare(a.refs(), b.refs()));
    }

    /// Sorts the map slice with a comparator function.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place (i.e., does not
    /// allocate), and *O*(*n* \* log(*n*)) worst-case.
    pub fn sort_unstable_by<F>(&mut self, mut compare: F)
    where
        F: FnMut((&K, &V), (&K, &V)) -> Ordering,
    {
        self.entries
            .sort_unstable_by(|a, b| compare(a.refs(), b.refs()));
    }

    /// Sort the map slice’s key-value pairs in place using a sort-key extraction function.
    ///
    /// During sorting, the function is called at most once per entry, by using temporary storage
    /// to remember the results of its evaluation. The order of calls to the function is
    /// unspecified and may change between versions of `vecmap-rs` or the standard library.
    ///
    /// See [`slice::sort_by_cached_key`] for more details.
    pub fn sort_by_cached_key<T, F>(&mut self, mut sort_key: F)
    where
        T: Ord,
        F: FnMut(&K, &V) -> T,
    {
        self.entries
            .sort_by_cached_key(|a| sort_key(a.key(), a.value()));
    }
}

// Binary search operations.
impl<K, V> MapSlice<K, V> {
    /// Search over a sorted map slice for a key.
    ///
    /// Returns the position where that key is present, or the position where it can be inserted to
    /// maintain the sort. See [`slice::binary_search`] for more details.
    pub fn binary_search_keys(&self, key: &K) -> Result<usize, usize>
    where
        K: Ord,
    {
        self.binary_search_by(|k, _| k.cmp(key))
    }

    /// Search over a sorted map slice with a comparator function.
    ///
    /// Returns the position where that value is present, or the position where it can be inserted
    /// to maintain the sort. See [`slice::binary_search_by`] for more details.
    pub fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a K, &'a V) -> Ordering,
    {
        self.entries
            .binary_search_by(|slot| f(slot.key(), slot.value()))
    }

    /// Search over a sorted map slice with an extraction function.
    ///
    /// Returns the position where that value is present, or the position where it can be inserted
    /// to maintain the sort. See [`slice::binary_search_by_key`] for more details.
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a K, &'a V) -> B,
        B: Ord,
    {
        self.entries
            .binary_search_by_key(b, |slot| f(slot.key(), slot.value()))
    }

    /// Returns the index of the partition point of a sorted map slice according to the given
    /// predicate (the index of the first element of the second partition).
    ///
    /// See [`slice::partition_point`] for more details.
    pub fn partition_point<P>(&self, mut pred: P) -> usize
    where
        P: FnMut(&K, &V) -> bool,
    {
        self.entries
            .partition_point(|slot| pred(slot.key(), slot.value()))
    }
}
