//! `VecMap` is a vector-based map implementation which retains the order of inserted entries.

mod entry;
mod impls;
mod iter;
mod mutable_keys;
#[cfg(feature = "serde")]
mod serde;

use super::{Entries, Slot};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::mem;
use core::ops::RangeBounds;

pub use self::entry::{Entry, OccupiedEntry, VacantEntry};
pub use self::iter::*;
pub use self::mutable_keys::MutableKeys;

/// A vector-based map implementation which retains the order of inserted entries.
///
/// Internally it is represented as a `Vec<(K, V)>` to support keys that are neither `Hash` nor
/// `Ord`.
#[derive(Clone, Debug)]
pub struct VecMap<K, V> {
    pub(crate) base: Vec<Slot<K, V>>,
}

impl<K, V> VecMap<K, V> {
    /// Create a new map. (Does not allocate.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<i32, &str> = VecMap::new();
    /// ```
    pub const fn new() -> Self {
        VecMap { base: Vec::new() }
    }

    /// Create a new map with capacity for `capacity` key-value pairs. (Does not allocate if
    /// `capacity` is zero.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<i32, &str> = VecMap::with_capacity(10);
    /// assert_eq!(map.len(), 0);
    /// assert!(map.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        VecMap {
            base: Vec::with_capacity(capacity),
        }
    }

    /// Returns the number of entries the map can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<i32, &str> = VecMap::with_capacity(10);
    /// assert_eq!(map.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.base.capacity()
    }

    /// Returns the number of entries in the map, also referred to as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut a = VecMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.base.len()
    }

    /// Returns `true` if the map contains no entries.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut a = VecMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Clears the map, removing all entries.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut a = VecMap::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.base.clear();
    }

    /// Shortens the map, keeping the first `len` key-value pairs and dropping the rest.
    ///
    /// If `len` is greater than the map's current length, this has no effect.
    ///
    /// # Examples
    ///
    /// Truncating a four element map to two elements:
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([("a", 1), ("b", 2), ("c", 3), ("d", 4)]);
    /// map.truncate(2);
    /// assert_eq!(map, VecMap::from([("a", 1), ("b", 2)]));
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the map's current length:
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([("a", 1), ("b", 2), ("c", 3), ("d", 4)]);
    /// map.truncate(8);
    /// assert_eq!(map, VecMap::from([("a", 1), ("b", 2), ("c", 3), ("d", 4)]));
    /// ```
    pub fn truncate(&mut self, len: usize) {
        self.base.truncate(len);
    }

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
        self.base.reverse();
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the given
    /// `VecMap<K, V>`. The collection may reserve more space to speculatively avoid frequent
    /// reallocations. After calling `reserve`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1)]);
    /// map.reserve(10);
    /// assert!(map.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.base.reserve(additional);
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)` returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<i32, i32> = (0..8).map(|x| (x, x*10)).collect();
    /// map.retain(|&k, _| k % 2 == 0);
    /// assert_eq!(map.len(), 4);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        self.base.retain_mut(|slot| {
            let (key, value) = slot.ref_mut();
            f(key, value)
        });
    }

    /// Shrinks the capacity of the map as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with
    /// the resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<i32, i32> = VecMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.base.shrink_to_fit();
    }

    /// Shrinks the capacity of the map with a lower limit. It will drop down no lower than the
    /// supplied limit while maintaining the internal rules and possibly leaving some space in
    /// accordance with the resize policy.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<i32, i32> = VecMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10);
    /// map.shrink_to(0);
    /// assert!(map.capacity() >= 2);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.base.shrink_to(min_capacity);
    }

    /// Splits the map into two at the given index.
    ///
    /// Returns a newly allocated map containing the key-value pairs in the range `[at, len)`.
    /// After the call, the original map will be left containing the key-value pairs `[0, at)`
    /// with its previous capacity unchanged.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([("a", 1), ("b", 2), ("c", 3)]);
    /// let map2 = map.split_off(1);
    /// assert_eq!(map, VecMap::from([("a", 1)]));
    /// assert_eq!(map2, VecMap::from([("b", 2), ("c", 3)]));
    /// ```
    pub fn split_off(&mut self, at: usize) -> VecMap<K, V> {
        VecMap {
            base: self.base.split_off(at),
        }
    }

    /// Removes the specified range from the vector in bulk, returning all removed elements as an
    /// iterator. If the iterator is dropped before being fully consumed, it drops the remaining
    /// removed elements.
    ///
    /// The returned iterator keeps a mutable borrow on the vector to optimize its implementation.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if the end point is greater
    /// than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::{vecmap, VecMap};
    ///
    /// let mut v = vecmap!["a" => 1, "b" => 2, "c" => 3];
    /// let u: VecMap<_, _> = v.drain(1..).collect();
    /// assert_eq!(v, vecmap!["a" => 1]);
    /// assert_eq!(u, vecmap!["b" => 2, "c" => 3]);
    ///
    /// // A full range clears the vector, like `clear()` does
    /// v.drain(..);
    /// assert_eq!(v, vecmap![]);
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, K, V>
    where
        R: RangeBounds<usize>,
    {
        Drain::new(self, range)
    }

    // Push a key-value pair at the end of the `VecMap` without checking whether the key already
    // exists.
    fn push(&mut self, key: K, value: V) -> usize {
        let index = self.base.len();
        self.base.push(Slot::new(key, value));
        index
    }

    /// Sorts the map by key.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*))
    /// worst-case.
    ///
    /// When applicable, unstable sorting is preferred because it is generally faster than stable
    /// sorting and it doesn't allocate auxiliary memory. See
    /// [`sort_unstable_keys`](VecMap::sort_unstable_keys).
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
        self.base.sort_by(|a, b| a.key().cmp(b.key()));
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
        self.base.sort_unstable_by(|a, b| a.key().cmp(b.key()));
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
        self.base.sort_by(|a, b| compare(a.refs(), b.refs()));
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
        self.base
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
        self.base
            .sort_by_cached_key(|a| sort_key(a.key(), a.value()));
    }

    /// Extracts a slice containing the map entries.
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let slice = map.as_slice();
    /// assert_eq!(slice, [("b", 2), ("a", 1), ("c", 3)]);
    /// ```
    pub fn as_slice(&self) -> &[(K, V)] {
        // SAFETY: `&[Slot<K, V>]` and `&[(K, V)]` have the same memory layout.
        unsafe { &*(self.base.as_slice() as *const [Slot<K, V>] as *const [(K, V)]) }
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

    /// Takes ownership of the map and returns its entries as a `Vec<(K, V)>`.
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let vec = map.into_vec();
    /// assert_eq!(vec, [("b", 2), ("a", 1), ("c", 3)]);
    /// ```
    pub fn into_vec(self) -> Vec<(K, V)> {
        // SAFETY: `Vec<Slot<K, V>>` and `Vec<(K, V)>` have the same memory layout.
        unsafe { super::transmute_vec(self.base) }
    }

    /// Takes ownership of provided vector and converts it into `VecMap`.
    ///
    /// # Safety
    ///
    /// The vector must have no duplicate keys. One way to guarantee it is to
    /// sort the vector (e.g. by using [`[T]::sort_by_key`][slice-sort-by-key]) and then drop
    /// duplicate keys (e.g. by using [`Vec::dedup_by_key`]).
    ///
    /// # Example
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut vec = vec![("b", 2), ("a", 1), ("c", 3), ("b", 4)];
    /// vec.sort_by_key(|slot| slot.0);
    /// vec.dedup_by_key(|slot| slot.0);
    /// // SAFETY: We've just deduplicated the vector.
    /// let map = unsafe { VecMap::from_vec_unchecked(vec) };
    ///
    /// assert_eq!(map, VecMap::from([("b", 2), ("a", 1), ("c", 3)]));
    /// ```
    ///
    /// [slice-sort-by-key]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_key
    pub unsafe fn from_vec_unchecked(vec: Vec<(K, V)>) -> Self {
        // SAFETY: `Vec<(K, V)>` and `Vec<Slot<K, V>>` have the same memory layout.
        let base = unsafe { super::transmute_vec(vec) };
        VecMap { base }
    }
}

// Lookup operations.
impl<K, V> VecMap<K, V> {
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
        self.base.first().map(Slot::refs)
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
        self.base.first_mut().map(Slot::ref_mut)
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
        self.base.last().map(Slot::refs)
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
        self.base.last_mut().map(Slot::ref_mut)
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
        self.get_index_of(key).map(|index| self.base[index].value())
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
            .map(|index| self.base[index].value_mut())
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
        self.base.get(index).map(Slot::refs)
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
        self.base.get_mut(index).map(Slot::ref_mut)
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
            let (key, value) = self.base[index].refs();
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
            let (key, value) = self.base[index].ref_mut();
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
        self.get_index_of(key).map(|index| self.base[index].refs())
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
        if self.base.is_empty() {
            return None;
        }

        self.base.iter().position(|slot| slot.key().borrow() == key)
    }
}

// Removal operations.
impl<K, V> VecMap<K, V> {
    /// Removes the last element from the map and returns it, or [`None`] if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    /// assert_eq!(map.pop(), Some(("b", 2)));
    /// assert_eq!(map.pop(), Some(("a", 1)));
    /// assert!(map.is_empty());
    /// assert_eq!(map.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<(K, V)> {
        self.base.pop().map(Slot::into_key_value)
    }

    /// Remove the key-value pair equivalent to `key` and return its value.
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([(1, "a"), (2, "b"), (3, "c"), (4, "d")]);
    /// assert_eq!(map.remove(&2), Some("b"));
    /// assert_eq!(map.remove(&2), None);
    /// assert_eq!(map, VecMap::from_iter([(1, "a"), (3, "c"), (4, "d")]));
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| self.remove_index(index).1)
    }

    /// Remove and return the key-value pair equivalent to `key`.
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([(1, "a"), (2, "b"), (3, "c"), (4, "d")]);
    /// assert_eq!(map.remove_entry(&2), Some((2, "b")));
    /// assert_eq!(map.remove_entry(&2), None);
    /// assert_eq!(map, VecMap::from_iter([(1, "a"), (3, "c"), (4, "d")]));
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key).map(|index| self.remove_index(index))
    }

    /// Removes and returns the key-value pair at position `index` within the map, shifting all
    /// elements after it to the left.
    ///
    /// If you don't need the order of elements to be preserved, use [`swap_remove`] instead.
    ///
    /// [`swap_remove`]: VecMap::swap_remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut v = VecMap::from([("a", 1), ("b", 2), ("c", 3)]);
    /// assert_eq!(v.remove_index(1), ("b", 2));
    /// assert_eq!(v, VecMap::from([("a", 1), ("c", 3)]));
    /// ```
    pub fn remove_index(&mut self, index: usize) -> (K, V) {
        self.base.remove(index).into_key_value()
    }

    /// Remove the key-value pair equivalent to `key` and return its value.
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the last element of the
    /// map and popping it off. **This perturbs the position of what used to be the last element!**
    ///
    /// Return `None` if `key` is not in map.
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([(1, "a"), (2, "b"), (3, "c"), (4, "d")]);
    /// assert_eq!(map.swap_remove(&2), Some("b"));
    /// assert_eq!(map.swap_remove(&2), None);
    /// assert_eq!(map, VecMap::from_iter([(1, "a"), (4, "d"), (3, "c")]));
    /// ```
    pub fn swap_remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| self.swap_remove_index(index).1)
    }

    /// Remove and return the key-value pair equivalent to `key`.
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the last element of the
    /// map and popping it off. **This perturbs the position of what used to be the last element!**
    ///
    /// Return `None` if `key` is not in map.
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([(1, "a"), (2, "b"), (3, "c"), (4, "d")]);
    /// assert_eq!(map.swap_remove_entry(&2), Some((2, "b")));
    /// assert_eq!(map.swap_remove_entry(&2), None);
    /// assert_eq!(map, VecMap::from_iter([(1, "a"), (4, "d"), (3, "c")]));
    /// ```
    pub fn swap_remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| self.swap_remove_index(index))
    }

    /// Removes a key-value pair from the map and returns it.
    ///
    /// The removed key-value pair is replaced by the last key-value pair of the map.
    ///
    /// If you need to preserve the element order, use [`remove`] instead.
    ///
    /// [`remove`]: VecMap::remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut v = VecMap::from([("foo", 1), ("bar", 2), ("baz", 3), ("qux", 4)]);
    ///
    /// assert_eq!(v.swap_remove_index(0), ("foo", 1));
    /// assert_eq!(v, VecMap::from([("qux", 4), ("bar", 2), ("baz", 3)]));
    ///
    /// assert_eq!(v.swap_remove_index(0), ("qux", 4));
    /// assert_eq!(v, VecMap::from([("baz", 3), ("bar", 2)]));
    /// ```
    pub fn swap_remove_index(&mut self, index: usize) -> (K, V) {
        self.base.swap_remove(index).into_key_value()
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
        self.base.swap(a, b);
    }
}

// Insertion operations.
impl<K, V> VecMap<K, V>
where
    K: Eq,
{
    /// Insert a key-value pair in the map.
    ///
    /// If an equivalent key already exists in the map: the key remains and retains in its place
    /// in the order, its corresponding value is updated with `value` and the older value is
    /// returned inside `Some(_)`.
    ///
    /// If no equivalent key existed in the map: the new key-value pair is inserted, last in
    /// order, and `None` is returned.
    ///
    /// See also [`entry`](#method.entry) if you you want to insert *or* modify or if you need to
    /// get the index of the corresponding key-value pair.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert_full(key, value).1
    }

    /// Insert a key-value pair in the map, and get their index.
    ///
    /// If an equivalent key already exists in the map: the key remains and
    /// retains in its place in the order, its corresponding value is updated
    /// with `value` and the older value is returned inside `(index, Some(_))`.
    ///
    /// If no equivalent key existed in the map: the new key-value pair is
    /// inserted, last in order, and `(index, None)` is returned.
    ///
    /// See also [`entry`](#method.entry) if you you want to insert *or* modify
    /// or if you need to get the index of the corresponding key-value pair.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// assert_eq!(map.insert_full("a", 1), (0, None));
    /// assert_eq!(map.insert_full("b", 2), (1, None));
    /// assert_eq!(map.insert_full("b", 3), (1, Some(2)));
    /// assert_eq!(map["b"], 3);
    /// ```
    pub fn insert_full(&mut self, key: K, value: V) -> (usize, Option<V>) {
        match self.get_index_of(&key) {
            Some(index) => {
                let old_slot = mem::replace(&mut self.base[index], Slot::new(key, value));
                (index, Some(old_slot.into_value()))
            }
            None => (self.push(key, value), None),
        }
    }

    /// Insert a key-value pair at position `index` within the map, shifting all
    /// elements after it to the right.
    ///
    /// If an equivalent key already exists in the map: the key is removed from the map and the new
    /// key-value pair is inserted at `index`. The old index and its value are returned inside
    /// `Some((usize, _))`.
    ///
    /// If no equivalent key existed in the map: the new key-value pair is
    /// inserted at position `index` and `None` is returned.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// assert_eq!(map.insert_at(0, "a", 1), None);
    /// assert_eq!(map.insert_at(1, "b", 2), None);
    /// assert_eq!(map.insert_at(0, "b", 3), Some((1, 2)));
    /// assert_eq!(map.to_vec(), [("b", 3), ("a", 1)]);
    /// ```
    pub fn insert_at(&mut self, index: usize, key: K, value: V) -> Option<(usize, V)> {
        if let Some(old_index) = self.get_index_of(&key) {
            let old_slot = if old_index == index {
                mem::replace(&mut self.base[index], Slot::new(key, value))
            } else {
                let old_slot = self.base.remove(old_index);
                self.base.insert(index, Slot::new(key, value));
                old_slot
            };

            Some((old_index, old_slot.into_value()))
        } else {
            self.base.insert(index, Slot::new(key, value));
            None
        }
    }

    /// Get the given key's corresponding entry in the map for insertion and/or in-place
    /// manipulation.
    ///
    /// ## Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut letters = VecMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     letters.entry(ch).and_modify(|counter| *counter += 1).or_insert(1);
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        match self.get_index_of(&key) {
            Some(index) => Entry::Occupied(OccupiedEntry::new(self, key, index)),
            None => Entry::Vacant(VacantEntry::new(self, key)),
        }
    }
}

// Iterator adapters.
impl<K, V> VecMap<K, V> {
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
        Iter::new(self.as_entries())
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
        IterMut::new(self.as_entries_mut())
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
        Keys::new(self.as_entries())
    }

    /// Creates a consuming iterator visiting all the keys in insertion order. The object cannot be
    /// used after calling this. The iterator element type is `K`.
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
    /// let mut vec: Vec<&str> = map.into_keys().collect();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// ```
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys::new(self.into_entries())
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
        Values::new(self.as_entries())
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
        ValuesMut::new(self.as_entries_mut())
    }

    /// Creates a consuming iterator visiting all the values in insertion order. The object cannot
    /// be used after calling this. The iterator element type is `V`.
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
    /// let mut vec: Vec<i32> = map.into_values().collect();
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues::new(self.into_entries())
    }
}

impl<K, V> Entries for VecMap<K, V> {
    type Entry = Slot<K, V>;

    fn as_entries(&self) -> &[Self::Entry] {
        &self.base
    }

    fn as_entries_mut(&mut self) -> &mut [Self::Entry] {
        &mut self.base
    }

    fn into_entries(self) -> Vec<Self::Entry> {
        self.base
    }
}
