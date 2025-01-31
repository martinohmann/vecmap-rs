mod impls;

use super::{Iter, IterMut, Keys, Slot, Values, ValuesMut};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::ptr;

/// A dynamically-sized slice of key-value pairs in a [`VecMap`][crate::VecMap].
///
/// This supports indexed operations much like a `[(K, V)]` slice.
#[repr(transparent)]
pub struct Slice<K, V> {
    entries: [Slot<K, V>],
}

impl<K, V> Slice<K, V> {
    pub(super) const fn from_slice(entries: &[Slot<K, V>]) -> &Slice<K, V> {
        // SAFETY: `&[Slot<K, V>]` and `&Slice<K, V>` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<K, V>]>(entries) as *const Slice<K, V>) }
    }

    pub(super) const fn from_mut_slice(entries: &mut [Slot<K, V>]) -> &mut Slice<K, V> {
        // SAFETY: `&mut [Slot<K, V>]` and `&mut Slice<K, V>` have the same memory layout.
        unsafe { &mut *(ptr::from_mut::<[Slot<K, V>]>(entries) as *mut Slice<K, V>) }
    }

    /// Extracts a slice containing the map entries.
    ///
    /// This method provides access to the raw backing [`&[(K, V)]`][core::slice] of the `Slice<K, V>`.
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// assert_eq!(map.as_std_slice(), [("b", 2), ("a", 1), ("c", 3)]);
    /// ```
    pub const fn as_std_slice(&self) -> &[(K, V)] {
        // SAFETY: `&[Slot<K, V>]` and `&[(K, V)]` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<K, V>]>(&self.entries) as *const [(K, V)]) }
    }

    /// Returns an empty slice.
    ///
    /// ```
    /// use vecmap::map::{Slice, VecMap};
    ///
    /// let map: VecMap<u32, &str> = VecMap::new();
    /// let slice: &Slice<u32, &str> = Slice::new();
    /// assert!(slice.is_empty());
    /// assert_eq!(slice, map.as_slice());
    /// ```
    pub const fn new<'a>() -> &'a Self {
        Slice::from_slice(&[])
    }

    /// Returns an empty mutable slice.
    ///
    /// ```
    /// use vecmap::map::{Slice, VecMap};
    ///
    /// let mut map: VecMap<u32, &str> = VecMap::new();
    /// let slice: &mut Slice<u32, &str> = Slice::new_mut();
    /// assert!(slice.is_empty());
    /// assert_eq!(slice, map.as_mut_slice());
    /// ```
    pub const fn new_mut<'a>() -> &'a mut Self {
        Slice::from_mut_slice(&mut [])
    }

    /// Returns the number of entries in the slice, also referred to as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// let slice = map.as_slice();
    /// assert_eq!(slice.len(), 1);
    /// ```
    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if the slice contains no entries.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// let slice = map.as_slice();
    /// assert!(slice.is_empty());
    ///
    /// map.insert(1, "a");
    ///
    /// let slice = map.as_slice();
    /// assert!(!slice.is_empty());
    /// ```
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Copies the map entries into a new `Vec<(K, V)>`.
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let vec = map.to_vec();
    /// assert_eq!(vec, [("b", 2), ("a", 1), ("c", 3)]);
    /// // Here, `map` and `vec` can be modified independently.
    /// ```
    pub fn to_vec(&self) -> Vec<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }
}

// Iterator adapters.
impl<K, V> Slice<K, V> {
    /// An iterator visiting all key-value pairs in insertion order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {key} val: {val}");
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::new(&self.entries)
    }

    /// An iterator visiting all key-value pairs in insertion order, with mutable references to the
    /// values. The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// // Update all values
    /// for (_, val) in map.iter_mut() {
    ///     *val *= 2;
    /// }
    ///
    /// for (key, val) in &map {
    ///     println!("key: {key} val: {val}");
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut::new(&mut self.entries)
    }

    /// An iterator visiting all keys in insertion order. The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for key in map.keys() {
    ///     println!("{key}");
    /// }
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys::new(&self.entries)
    }

    /// An iterator visiting all values in insertion order. The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for val in map.values() {
    ///     println!("{val}");
    /// }
    /// ```
    pub fn values(&self) -> Values<'_, K, V> {
        Values::new(&self.entries)
    }

    /// An iterator visiting all values mutably in insertion order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for val in map.values_mut() {
    ///     *val = *val + 10;
    /// }
    ///
    /// for val in map.values() {
    ///     println!("{val}");
    /// }
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut::new(&mut self.entries)
    }
}

// Lookup operations.
impl<K, V> Slice<K, V> {
    /// Return `true` if an equivalent to `key` exists in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key).is_some()
    }

    /// Get the first key-value pair.
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    /// assert_eq!(map.first(), Some((&"a", &1)));
    /// ```
    pub fn first(&self) -> Option<(&K, &V)> {
        self.entries.first().map(Slot::refs)
    }

    /// Get the first key-value pair, with mutable access to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    ///
    /// if let Some((_, v)) = map.first_mut() {
    ///     *v = *v + 10;
    /// }
    /// assert_eq!(map.first(), Some((&"a", &11)));
    /// ```
    pub fn first_mut(&mut self) -> Option<(&K, &mut V)> {
        self.entries.first_mut().map(Slot::ref_mut)
    }

    /// Get the last key-value pair.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    /// assert_eq!(map.last(), Some((&"b", &2)));
    /// map.pop();
    /// map.pop();
    /// assert_eq!(map.last(), None);
    /// ```
    pub fn last(&self) -> Option<(&K, &V)> {
        self.entries.last().map(Slot::refs)
    }

    /// Get the last key-value pair, with mutable access to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    ///
    /// if let Some((_, v)) = map.last_mut() {
    ///     *v = *v + 10;
    /// }
    /// assert_eq!(map.last(), Some((&"b", &12)));
    /// ```
    pub fn last_mut(&mut self) -> Option<(&K, &mut V)> {
        self.entries.last_mut().map(Slot::ref_mut)
    }

    /// Return a reference to the value stored for `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| self.entries[index].value())
    }

    /// Return a mutable reference to the value stored for `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| self.entries[index].value_mut())
    }

    /// Return references to the key-value pair stored at `index`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_index(0), Some((&1, &"a")));
    /// assert_eq!(map.get_index(1), None);
    /// ```
    pub fn get_index(&self, index: usize) -> Option<(&K, &V)> {
        self.entries.get(index).map(Slot::refs)
    }

    /// Return a reference to the key and a mutable reference to the value stored at `index`, if it
    /// is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// if let Some((_, v)) = map.get_index_mut(0) {
    ///     *v = "b";
    /// }
    /// assert_eq!(map[0], "b");
    /// ```
    pub fn get_index_mut(&mut self, index: usize) -> Option<(&K, &mut V)> {
        self.entries.get_mut(index).map(Slot::ref_mut)
    }

    /// Return the index and references to the key-value pair stored for `key`, if it is present,
    /// else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_full(&1), Some((0, &1, &"a")));
    /// assert_eq!(map.get_full(&2), None);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    ///
    /// if let Some((_, _, v)) = map.get_full_mut(&1) {
    ///     *v = "b";
    /// }
    /// assert_eq!(map.get(&1), Some(&"b"));
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| self.entries[index].refs())
    }

    /// Return item index, if it exists in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert("a", 10);
    /// map.insert("b", 20);
    /// assert_eq!(map.get_index_of("a"), Some(0));
    /// assert_eq!(map.get_index_of("b"), Some(1));
    /// assert_eq!(map.get_index_of("c"), None);
    /// ```
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
impl<K, V> Slice<K, V> {
    /// Reverses the order of entries in the map, in place.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate alloc;
    /// # use alloc::vec::Vec;
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2), ("c", 3)]);
    /// map.reverse();
    /// let reversed: Vec<(&str, u8)> = map.into_iter().collect();
    /// assert_eq!(reversed, Vec::from_iter([("c", 3), ("b", 2), ("a", 1)]));
    /// ```
    pub fn reverse(&mut self) {
        self.entries.reverse();
    }

    /// Swaps the position of two key-value pairs in the map.
    ///
    /// # Arguments
    ///
    /// * a - The index of the first element
    /// * b - The index of the second element
    ///
    /// # Panics
    ///
    /// Panics if `a` or `b` are out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([("a", 1), ("b", 2), ("c", 3), ("d", 4)]);
    /// map.swap_indices(1, 3);
    /// assert_eq!(map.to_vec(), [("a", 1), ("d", 4), ("c", 3), ("b", 2)]);
    /// ```
    pub fn swap_indices(&mut self, a: usize, b: usize) {
        self.entries.swap(a, b);
    }
}

// Sort operations.
impl<K, V> Slice<K, V> {
    /// Sorts the map by key.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*))
    /// worst-case.
    ///
    /// When applicable, unstable sorting is preferred because it is generally faster than stable
    /// sorting and it doesn't allocate auxiliary memory. See
    /// [`sort_unstable_keys`](Self::sort_unstable_keys).
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    ///
    /// map.sort_keys();
    /// let vec: Vec<_> = map.into_iter().collect();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    pub fn sort_keys(&mut self)
    where
        K: Ord,
    {
        self.entries.sort_by(|a, b| a.key().cmp(b.key()));
    }

    /// Sorts the map by key.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place (i.e., does not
    /// allocate), and *O*(*n* \* log(*n*)) worst-case.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    ///
    /// map.sort_unstable_keys();
    /// assert_eq!(map.as_slice(), [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    pub fn sort_unstable_keys(&mut self)
    where
        K: Ord,
    {
        self.entries.sort_unstable_by(|a, b| a.key().cmp(b.key()));
    }

    /// Sorts the map with a comparator function.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*))
    /// worst-case.
    ///
    /// # Examples
    ///
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    ///
    /// map.sort_by(|(k1, _), (k2, _)| k2.cmp(&k1));
    /// let vec: Vec<_> = map.into_iter().collect();
    /// assert_eq!(vec, [("c", 3), ("b", 2), ("a", 1)]);
    /// ```
    pub fn sort_by<F>(&mut self, mut compare: F)
    where
        F: FnMut((&K, &V), (&K, &V)) -> Ordering,
    {
        self.entries.sort_by(|a, b| compare(a.refs(), b.refs()));
    }

    /// Sorts the map with a comparator function.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place (i.e., does not
    /// allocate), and *O*(*n* \* log(*n*)) worst-case.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    ///
    /// map.sort_unstable_by(|(k1, _), (k2, _)| k2.cmp(&k1));
    /// let vec: Vec<_> = map.into_iter().collect();
    /// assert_eq!(vec, [("c", 3), ("b", 2), ("a", 1)]);
    /// ```
    pub fn sort_unstable_by<F>(&mut self, mut compare: F)
    where
        F: FnMut((&K, &V), (&K, &V)) -> Ordering,
    {
        self.entries
            .sort_unstable_by(|a, b| compare(a.refs(), b.refs()));
    }

    /// Sort the map’s key-value pairs in place using a sort-key extraction function.
    ///
    /// During sorting, the function is called at most once per entry, by using temporary storage
    /// to remember the results of its evaluation. The order of calls to the function is
    /// unspecified and may change between versions of `vecmap-rs` or the standard library.
    ///
    /// See [`slice::sort_by_cached_key`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    ///
    /// map.sort_by_cached_key(|_, v| v.to_string());
    /// let vec: Vec<_> = map.into_iter().collect();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
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
impl<K, V> Slice<K, V> {
    /// Search over a sorted map for a key.
    ///
    /// Returns the position where that key is present, or the position where it can be inserted to
    /// maintain the sort. See [`slice::binary_search`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([("a", 1), ("b", 2), ("d", 4)]);
    /// assert_eq!(map.binary_search_keys(&"b"), Ok(1));
    /// assert_eq!(map.binary_search_keys(&"c"), Err(2));
    /// assert_eq!(map.binary_search_keys(&"z"), Err(3));
    /// ```
    pub fn binary_search_keys(&self, key: &K) -> Result<usize, usize>
    where
        K: Ord,
    {
        self.binary_search_by(|k, _| k.cmp(key))
    }

    /// Search over a sorted map with a comparator function.
    ///
    /// Returns the position where that value is present, or the position where it can be inserted
    /// to maintain the sort. See [`slice::binary_search_by`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([("a", 1), ("b", 2), ("d", 4)]);
    /// assert_eq!(map.binary_search_by(|k, _| k.cmp(&"b")), Ok(1));
    /// assert_eq!(map.binary_search_by(|k, _| k.cmp(&"c")), Err(2));
    /// assert_eq!(map.binary_search_by(|k, _| k.cmp(&"z")), Err(3));
    /// assert_eq!(map.binary_search_by(|_, v| v.cmp(&4)), Ok(2));
    /// ```
    pub fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a K, &'a V) -> Ordering,
    {
        self.entries
            .binary_search_by(|slot| f(slot.key(), slot.value()))
    }

    /// Search over a sorted map with an extraction function.
    ///
    /// Returns the position where that value is present, or the position where it can be inserted
    /// to maintain the sort. See [`slice::binary_search_by_key`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([("a", 1), ("b", 2), ("d", 4)]);
    /// assert_eq!(map.binary_search_by_key(&"b", |&k, _| k), Ok(1));
    /// assert_eq!(map.binary_search_by_key(&"c", |&k, _| k), Err(2));
    /// assert_eq!(map.binary_search_by_key(&"z", |&k, _| k), Err(3));
    /// assert_eq!(map.binary_search_by_key(&4, |_, &v| v), Ok(2));
    /// ```
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a K, &'a V) -> B,
        B: Ord,
    {
        self.entries
            .binary_search_by_key(b, |slot| f(slot.key(), slot.value()))
    }

    /// Returns the index of the partition point of a sorted map according to the given predicate
    /// (the index of the first element of the second partition).
    ///
    /// See [`slice::partition_point`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([("a", 1), ("b", 2), ("d", 4)]);
    /// assert_eq!(map.partition_point(|&k, _| k < "d"), 2);
    /// assert_eq!(map.partition_point(|_, &v| v < 2), 1);
    /// assert_eq!(map.partition_point(|_, &v| v > 100), 0);
    /// assert_eq!(map.partition_point(|_, &v| v < 100), 3);
    /// ```
    pub fn partition_point<P>(&self, mut pred: P) -> usize
    where
        P: FnMut(&K, &V) -> bool,
    {
        self.entries
            .partition_point(|slot| pred(slot.key(), slot.value()))
    }
}
