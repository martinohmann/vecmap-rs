use super::{Iter, IterMut, Keys, Slot, Values, ValuesMut};
use alloc::boxed::Box;
use core::cmp::Ordering;
use core::ops::Deref;
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

    pub(super) fn from_boxed(entries: Box<[Slot<K, V>]>) -> Box<Slice<K, V>> {
        // SAFETY: `A [Slot<K, V>]` and a `Slice<K, V>` are essentially the same thing.
        unsafe { Box::from_raw(Box::into_raw(entries) as *mut Slice<K, V>) }
    }

    pub(super) fn as_raw_slice(&self) -> &[(K, V)] {
        // SAFETY: `&[Slot<K, V>]` and `&[(K, V)]` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<K, V>]>(&self.entries) as *const [(K, V)]) }
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
    /// assert_eq!(map.as_raw_slice(), [("a", 1), ("b", 2), ("c", 3)]);
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

impl<K, V> Deref for Slice<K, V> {
    type Target = [(K, V)];

    fn deref(&self) -> &Self::Target {
        self.as_raw_slice()
    }
}

impl<'a, K, V> IntoIterator for &'a Slice<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut Slice<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
