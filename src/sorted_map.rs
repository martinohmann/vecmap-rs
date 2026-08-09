//! `SortedVecMap` is a vector-based map implementation which keeps its entries sorted by key.

mod entry;
mod impls;
mod iter;
#[cfg(feature = "serde")]
mod serde;

use super::{Entries, Slot, TryReserveError, sorted_keyed::SortedKeyedVecSet};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::ops::RangeBounds;
use core::ptr;

pub use self::entry::{Entry, OccupiedEntry, VacantEntry};
pub use self::iter::*;

/// A vector-based map implementation which keeps its entries sorted by key.
///
/// Internally it is represented as a `Vec<(K, V)>` whose entries are always kept sorted by the
/// key. Iteration order matches the sort order of the keys.
///
/// # Complexity
///
/// | operation                                  | cost              |
/// |--------------------------------------------|-------------------|
/// | `get` / `contains_key` / `binary_search_*` | *O*(log *n*)      |
/// | `insert` / `remove` / `pop_first`          | *O*(*n*) (shift)  |
/// | `pop_last`                                 | *O*(1)            |
/// | `append`                                   | *O*(*n* + *m*)    |
/// | `iter` / `range`                           | *O*(*k*)          |
///
/// Lookups are faster than [`VecMap`](crate::VecMap)'s linear scan, but writes pay a shift cost
/// that [`BTreeMap`](alloc::collections::BTreeMap) avoids. Prefer `SortedVecMap` for read-heavy
/// workloads with small-to-moderate *n* or when the contiguous memory layout matters.
///
/// Unlike [`VecMap`](crate::VecMap), `SortedVecMap` requires keys to implement [`Ord`], and
/// operations that would disturb the sort order (such as `insert_at`, `reverse`, `sort_keys`,
/// etc.) are intentionally not provided.
#[derive(Clone, Debug)]
pub struct SortedVecMap<K, V> {
    base: SortedKeyedVecSet<K, Slot<K, V>>,
}

impl<K, V> SortedVecMap<K, V> {
    /// Create a new map. (Does not allocate.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map: SortedVecMap<i32, &str> = SortedVecMap::new();
    /// ```
    pub const fn new() -> Self {
        SortedVecMap {
            base: SortedKeyedVecSet::new(),
        }
    }

    /// Create a new map with capacity for `capacity` key-value pairs. (Does not allocate if
    /// `capacity` is zero.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map: SortedVecMap<i32, &str> = SortedVecMap::with_capacity(10);
    /// assert_eq!(map.len(), 0);
    /// assert!(map.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        SortedVecMap {
            base: SortedKeyedVecSet::with_capacity(capacity),
        }
    }

    /// Returns the number of entries the map can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map: SortedVecMap<i32, &str> = SortedVecMap::with_capacity(10);
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
    /// use vecmap::SortedVecMap;
    ///
    /// let mut a = SortedVecMap::new();
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
    /// use vecmap::SortedVecMap;
    ///
    /// let mut a = SortedVecMap::new();
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
    /// use vecmap::SortedVecMap;
    ///
    /// let mut a = SortedVecMap::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.base.clear();
    }

    /// Shortens the map, keeping the first `len` key-value pairs (in sort order) and dropping the
    /// rest.
    ///
    /// If `len` is greater than the map's current length, this has no effect.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::from([("a", 1), ("b", 2), ("c", 3), ("d", 4)]);
    /// map.truncate(2);
    /// assert_eq!(map, SortedVecMap::from([("a", 1), ("b", 2)]));
    /// ```
    pub fn truncate(&mut self, len: usize) {
        self.base.truncate(len);
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the given
    /// `SortedVecMap<K, V>`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::from_iter([("a", 1)]);
    /// map.reserve(10);
    /// assert!(map.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.base.reserve(additional);
    }

    /// Reserves the minimum capacity for at least `additional` more elements to be inserted in
    /// the given `SortedVecMap<K, V>`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::from_iter([("a", 1)]);
    /// map.reserve_exact(10);
    /// assert!(map.capacity() >= 11);
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        self.base.reserve_exact(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::{SortedVecMap, TryReserveError};
    ///
    /// fn process(data: &[(u32, u32)]) -> Result<SortedVecMap<u32, u32>, TryReserveError> {
    ///     let mut output = SortedVecMap::new();
    ///     output.try_reserve(data.len())?;
    ///     output.extend(data.iter().copied());
    ///     Ok(output)
    /// }
    /// # process(&[(1, 1), (2, 2)]).expect("should reserve");
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional` more elements to be
    /// inserted.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::{SortedVecMap, TryReserveError};
    ///
    /// fn process(data: &[(u32, u32)]) -> Result<SortedVecMap<u32, u32>, TryReserveError> {
    ///     let mut output = SortedVecMap::new();
    ///     output.try_reserve_exact(data.len())?;
    ///     output.extend(data.iter().copied());
    ///     Ok(output)
    /// }
    /// # process(&[(1, 1), (2, 2)]).expect("should reserve");
    /// ```
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve_exact(additional)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)` returns `false`. The
    /// sort order is preserved.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map: SortedVecMap<i32, i32> = (0..8).map(|x| (x, x * 10)).collect();
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

    /// Shrinks the capacity of the map as much as possible.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map: SortedVecMap<i32, i32> = SortedVecMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.base.shrink_to_fit();
    }

    /// Shrinks the capacity of the map with a lower limit.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map: SortedVecMap<i32, i32> = SortedVecMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.base.shrink_to(min_capacity);
    }

    /// Splits the map into two at the given index.
    ///
    /// Returns a newly allocated map containing the key-value pairs in the range `[at, len)`.
    /// After the call, the original map will be left containing the key-value pairs `[0, at)`
    /// with its previous capacity unchanged. Both halves remain sorted.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::from([("a", 1), ("b", 2), ("c", 3)]);
    /// let map2 = map.split_off(1);
    /// assert_eq!(map, SortedVecMap::from([("a", 1)]));
    /// assert_eq!(map2, SortedVecMap::from([("b", 2), ("c", 3)]));
    /// ```
    pub fn split_off(&mut self, at: usize) -> SortedVecMap<K, V> {
        SortedVecMap {
            base: self.base.split_off(at),
        }
    }

    /// Search over the map for a key.
    ///
    /// Returns the position where that key is present, or the position where it can be inserted
    /// to maintain the sort. See [`slice::binary_search`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let map = SortedVecMap::from([("a", 1), ("b", 2), ("d", 4)]);
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

    /// Search over the map with a comparator function.
    ///
    /// Returns the position where that value is present, or the position where it can be
    /// inserted to maintain the sort. See [`slice::binary_search_by`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let map = SortedVecMap::from([("a", 1), ("b", 2), ("d", 4)]);
    /// assert_eq!(map.binary_search_by(|k, _| k.cmp(&"b")), Ok(1));
    /// assert_eq!(map.binary_search_by(|k, _| k.cmp(&"c")), Err(2));
    /// ```
    pub fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a K, &'a V) -> Ordering,
    {
        self.as_slice().binary_search_by(|(k, v)| f(k, v))
    }

    /// Search over the map with an extraction function.
    ///
    /// Returns the position where that value is present, or the position where it can be
    /// inserted to maintain the sort. See [`slice::binary_search_by_key`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let map = SortedVecMap::from([("a", 1), ("b", 2), ("d", 4)]);
    /// assert_eq!(map.binary_search_by_key(&"b", |&k, _| k), Ok(1));
    /// assert_eq!(map.binary_search_by_key(&"c", |&k, _| k), Err(2));
    /// assert_eq!(map.binary_search_by_key(&4, |_, &v| v), Ok(2));
    /// ```
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a K, &'a V) -> B,
        B: Ord,
    {
        self.as_slice().binary_search_by_key(b, |(k, v)| f(k, v))
    }

    /// Returns the index of the partition point according to the given predicate (the index of
    /// the first element of the second partition).
    ///
    /// See [`slice::partition_point`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let map = SortedVecMap::from([("a", 1), ("b", 2), ("d", 4)]);
    /// assert_eq!(map.partition_point(|&k, _| k < "d"), 2);
    /// assert_eq!(map.partition_point(|_, &v| v < 2), 1);
    /// ```
    pub fn partition_point<P>(&self, mut pred: P) -> usize
    where
        P: FnMut(&K, &V) -> bool,
    {
        self.as_slice().partition_point(|(k, v)| pred(k, v))
    }

    /// Removes the specified range from the vector in bulk, returning all removed elements as an
    /// iterator.
    ///
    /// The returned iterator keeps a mutable borrow on the vector to optimize its implementation.
    /// The range is interpreted in index space, not key space.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if the end point is greater
    /// than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut v = SortedVecMap::from([("a", 1), ("b", 2), ("c", 3)]);
    /// let u: SortedVecMap<_, _> = v.drain(1..).collect();
    /// assert_eq!(v, SortedVecMap::from([("a", 1)]));
    /// assert_eq!(u, SortedVecMap::from([("b", 2), ("c", 3)]));
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, K, V>
    where
        R: RangeBounds<usize>,
    {
        Drain::new(self, range)
    }

    /// Extracts a slice containing the map entries in sort order.
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let map = SortedVecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let slice = map.as_slice();
    /// assert_eq!(slice, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    pub fn as_slice(&self) -> &[(K, V)] {
        // SAFETY: `&[Slot<K, V>]` and `&[(K, V)]` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<K, V>]>(self.base.as_slice()) as *const [(K, V)]) }
    }

    /// Copies the map entries into a new `Vec<(K, V)>` in sort order.
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let map = SortedVecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let vec = map.to_vec();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    pub fn to_vec(&self) -> Vec<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }

    /// Takes ownership of the map and returns its entries as a `Vec<(K, V)>` in sort order.
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let map = SortedVecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let vec = map.into_vec();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    pub fn into_vec(self) -> Vec<(K, V)> {
        // SAFETY: `Vec<Slot<K, V>>` and `Vec<(K, V)>` have the same memory layout.
        unsafe { super::transmute_vec(self.base.into_vec()) }
    }

    /// Takes ownership of the provided vector and converts it into `SortedVecMap`.
    ///
    /// # Safety
    ///
    /// The vector must be sorted strictly by key (no duplicate keys). One way to guarantee this
    /// is to sort the vector (e.g. by using [`[T]::sort_by_key`][slice-sort-by-key]) and then
    /// drop duplicate keys (e.g. by using [`Vec::dedup_by_key`]).
    ///
    /// [slice-sort-by-key]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_key
    ///
    /// # Example
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut vec = vec![("b", 2), ("a", 1), ("c", 3), ("b", 4)];
    /// vec.sort_by_key(|slot| slot.0);
    /// vec.dedup_by_key(|slot| slot.0);
    /// // SAFETY: we've just sorted and deduplicated the vector.
    /// let map = unsafe { SortedVecMap::from_vec_unchecked(vec) };
    ///
    /// assert_eq!(map, SortedVecMap::from([("a", 1), ("b", 2), ("c", 3)]));
    /// ```
    pub unsafe fn from_vec_unchecked(vec: Vec<(K, V)>) -> Self {
        // SAFETY: `Vec<(K, V)>` and `Vec<Slot<K, V>>` have the same memory layout.
        let base_vec = unsafe { super::transmute_vec(vec) };
        SortedVecMap {
            base: unsafe { SortedKeyedVecSet::from_vec_unchecked(base_vec) },
        }
    }
}

// Lookup operations.
impl<K, V> SortedVecMap<K, V> {
    /// Return `true` if an equivalent to `key` exists in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.contains_key(key)
    }

    /// Get the first (least-keyed) key-value pair.
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let map = SortedVecMap::from_iter([("b", 2), ("a", 1)]);
    /// assert_eq!(map.first_key_value(), Some((&"a", &1)));
    /// ```
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        self.base.first().map(Slot::refs)
    }

    /// Get the last (greatest-keyed) key-value pair.
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let map = SortedVecMap::from_iter([("b", 2), ("a", 1)]);
    /// assert_eq!(map.last_key_value(), Some((&"b", &2)));
    /// ```
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        self.base.last().map(Slot::refs)
    }

    /// Get the first (least-keyed) key-value pair, with a mutable reference to the value.
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::from_iter([("b", 2), ("a", 1)]);
    /// if let Some((_, v)) = map.first_key_value_mut() {
    ///     *v = 10;
    /// }
    /// assert_eq!(map[&"a"], 10);
    /// ```
    pub fn first_key_value_mut(&mut self) -> Option<(&K, &mut V)> {
        self.base.first_mut().map(Slot::ref_mut)
    }

    /// Get the last (greatest-keyed) key-value pair, with a mutable reference to the value.
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::from_iter([("b", 2), ("a", 1)]);
    /// if let Some((_, v)) = map.last_key_value_mut() {
    ///     *v = 20;
    /// }
    /// assert_eq!(map[&"b"], 20);
    /// ```
    pub fn last_key_value_mut(&mut self) -> Option<(&K, &mut V)> {
        self.base.last_mut().map(Slot::ref_mut)
    }

    /// Return a reference to the value stored for `key`, if it is present.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.get(key).map(Slot::value)
    }

    /// Return a mutable reference to the value stored for `key`, if it is present.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.get_mut(key).map(Slot::value_mut)
    }

    /// Return references to the key-value pair stored at `index`, if it is present.
    ///
    /// The index is an index into the sort-ordered sequence of entries.
    pub fn get_index(&self, index: usize) -> Option<(&K, &V)> {
        self.base.get_index(index).map(Slot::refs)
    }

    /// Return a reference to the key and a mutable reference to the value stored at `index`, if
    /// it is present.
    pub fn get_index_mut(&mut self, index: usize) -> Option<(&K, &mut V)> {
        self.base.get_index_mut(index).map(Slot::ref_mut)
    }

    /// Return the index and references to the key-value pair stored for `key`, if it is present.
    pub fn get_full<Q>(&self, key: &Q) -> Option<(usize, &K, &V)>
    where
        K: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base
            .get_full(key)
            .map(|(index, slot)| (index, slot.key(), slot.value()))
    }

    /// Return the index, a reference to the key and a mutable reference to the value stored for
    /// `key`, if it is present.
    pub fn get_full_mut<Q>(&mut self, key: &Q) -> Option<(usize, &K, &mut V)>
    where
        K: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.get_index_of(key).map(|index| {
            let (key, value) = self.base[index].ref_mut();
            (index, key, value)
        })
    }

    /// Return references to the key-value pair stored for `key`, if it is present.
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.get(key).map(Slot::refs)
    }

    /// Return the item index, if it exists in the map.
    pub fn get_index_of<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.get_index_of(key)
    }
}

// Removal operations.
impl<K, V> SortedVecMap<K, V> {
    /// Removes the first (least-keyed) element from the map and returns it, or [`None`] if the
    /// map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::from_iter([("b", 2), ("a", 1)]);
    /// assert_eq!(map.pop_first(), Some(("a", 1)));
    /// assert_eq!(map.pop_first(), Some(("b", 2)));
    /// assert_eq!(map.pop_first(), None);
    /// ```
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        self.base.pop_first().map(Slot::into_key_value)
    }

    /// Removes the last (greatest-keyed) element from the map and returns it, or [`None`] if the
    /// map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::from_iter([("b", 2), ("a", 1)]);
    /// assert_eq!(map.pop_last(), Some(("b", 2)));
    /// assert_eq!(map.pop_last(), Some(("a", 1)));
    /// assert_eq!(map.pop_last(), None);
    /// ```
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        self.base.pop_last().map(Slot::into_key_value)
    }

    /// Remove the key-value pair equivalent to `key` and return its value.
    ///
    /// The pair is removed by shifting all of the elements that follow it, preserving their
    /// relative order (and therefore the sort invariant).
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::from_iter([(1, "a"), (2, "b"), (3, "c"), (4, "d")]);
    /// assert_eq!(map.remove(&2), Some("b"));
    /// assert_eq!(map.remove(&2), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.remove(key).map(Slot::into_value)
    }

    /// Remove and return the key-value pair equivalent to `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::from_iter([(1, "a"), (2, "b"), (3, "c")]);
    /// assert_eq!(map.remove_entry(&2), Some((2, "b")));
    /// assert_eq!(map.remove_entry(&2), None);
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.remove(key).map(Slot::into_key_value)
    }

    /// Removes and returns the key-value pair at position `index` within the map, shifting all
    /// elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut v = SortedVecMap::from([("a", 1), ("b", 2), ("c", 3)]);
    /// assert_eq!(v.remove_index(1), ("b", 2));
    /// assert_eq!(v, SortedVecMap::from([("a", 1), ("c", 3)]));
    /// ```
    pub fn remove_index(&mut self, index: usize) -> (K, V) {
        self.base.remove_index(index).into_key_value()
    }
}

// Insertion operations.
impl<K, V> SortedVecMap<K, V>
where
    K: Ord,
{
    /// Insert a key-value pair in the map.
    ///
    /// If an equivalent key already exists in the map: the key remains at its sorted position,
    /// its corresponding value is updated with `value`, and the old value is returned inside
    /// `Some(_)`.
    ///
    /// If no equivalent key existed: the new key-value pair is inserted at the correct sorted
    /// position, and `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::new();
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

    /// Insert a key-value pair in the map, and get its (sorted) index.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map = SortedVecMap::new();
    /// assert_eq!(map.insert_full("b", 2), (0, None));
    /// assert_eq!(map.insert_full("a", 1), (0, None));
    /// // "a" sorts before "b", so inserting "b" again reports index 1.
    /// assert_eq!(map.insert_full("b", 3), (1, Some(2)));
    /// ```
    pub fn insert_full(&mut self, key: K, value: V) -> (usize, Option<V>) {
        let (index, old_slot) = self.base.insert_full(Slot::new(key, value));
        (index, old_slot.map(Slot::into_value))
    }

    /// Get the given key's corresponding entry in the map for insertion and/or in-place
    /// manipulation.
    ///
    /// ## Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut letters = SortedVecMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     letters.entry(ch).and_modify(|c| *c += 1).or_insert(1);
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        match self.base.binary_search_key(&key) {
            Ok(index) => Entry::Occupied(OccupiedEntry::new(self, key, index)),
            Err(index) => Entry::Vacant(VacantEntry::new(self, key, index)),
        }
    }

    /// Moves all key-value pairs from `other` into `self`, leaving `other` empty.
    ///
    /// When a key exists in both maps, the value from `other` overwrites the one in `self`,
    /// matching [`BTreeMap::append`](alloc::collections::BTreeMap::append) semantics.
    ///
    /// Runs in *O*(*n* + *m*) by walking both sorted sides in parallel.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut a = SortedVecMap::from([(3, "c"), (2, "b"), (1, "a")]);
    /// let mut b = SortedVecMap::from([(3, "d"), (4, "e"), (5, "f")]);
    ///
    /// a.append(&mut b);
    ///
    /// assert_eq!(a.len(), 5);
    /// assert_eq!(b.len(), 0);
    ///
    /// assert_eq!(a[&3], "d"); // "c" was overwritten by "d" from `b`.
    /// ```
    pub fn append(&mut self, other: &mut SortedVecMap<K, V>) {
        self.base.append(&mut other.base);
    }
}

// Range iterators.
impl<K, V> SortedVecMap<K, V>
where
    K: Ord,
{
    /// Constructs an iterator over a sub-range of entries in the map.
    ///
    /// The simplest way is to use the range syntax `min..max`, thus `range(min..max)` will yield
    /// elements from `min` (inclusive) to `max` (exclusive). The range may also be specified as
    /// `(Bound<&K>, Bound<&K>)`, so for example `range((Excluded(&4), Included(&10)))` will yield
    /// a left-exclusive, right-inclusive range from 4 to 10.
    ///
    /// # Panics
    ///
    /// Panics if the range's start is greater than its end.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let map: SortedVecMap<_, _> = [(3, "a"), (5, "b"), (8, "c")].into_iter().collect();
    /// let collected: Vec<_> = map.range(4..9).map(|(k, v)| (*k, *v)).collect();
    /// assert_eq!(collected, vec![(5, "b"), (8, "c")]);
    /// ```
    pub fn range<Q, R>(&self, range: R) -> Range<'_, K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        let (start, end) = self.base.key_range_to_indices(range);
        Range::new(&self.base.as_slice()[start..end])
    }

    /// Constructs a mutable iterator over a sub-range of entries in the map.
    ///
    /// See [`range`](SortedVecMap::range) for range-specification details.
    ///
    /// # Panics
    ///
    /// Panics if the range's start is greater than its end.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map: SortedVecMap<_, _> = [(3, 1), (5, 1), (8, 1)].into_iter().collect();
    /// for (_, v) in map.range_mut(4..9) {
    ///     *v += 10;
    /// }
    /// assert_eq!(map[&3], 1);
    /// assert_eq!(map[&5], 11);
    /// assert_eq!(map[&8], 11);
    /// ```
    pub fn range_mut<Q, R>(&mut self, range: R) -> RangeMut<'_, K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        let (start, end) = self.base.key_range_to_indices(range);
        RangeMut::new(&mut self.base.as_mut_slice()[start..end])
    }
}

// Iterator adapters.
impl<K, V> SortedVecMap<K, V> {
    /// An iterator visiting all key-value pairs in sort order. The iterator element type is
    /// `(&'a K, &'a V)`.
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::new(self.as_entries())
    }

    /// An iterator visiting all key-value pairs in sort order, with mutable references to the
    /// values. The iterator element type is `(&'a K, &'a mut V)`.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut::new(self.as_entries_mut())
    }

    /// An iterator visiting all keys in sort order. The iterator element type is `&'a K`.
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys::new(self.as_entries())
    }

    /// Creates a consuming iterator visiting all the keys in sort order. The object cannot be
    /// used after calling this. The iterator element type is `K`.
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys::new(self.into_entries())
    }

    /// An iterator visiting all values in sort order. The iterator element type is `&'a V`.
    pub fn values(&self) -> Values<'_, K, V> {
        Values::new(self.as_entries())
    }

    /// An iterator visiting all values mutably in sort order. The iterator element type is
    /// `&'a mut V`.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut::new(self.as_entries_mut())
    }

    /// Creates a consuming iterator visiting all the values in sort order. The object cannot be
    /// used after calling this. The iterator element type is `V`.
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues::new(self.into_entries())
    }
}

impl<K, V> Entries for SortedVecMap<K, V> {
    type Entry = Slot<K, V>;

    fn as_entries(&self) -> &[Self::Entry] {
        self.base.as_slice()
    }

    fn as_entries_mut(&mut self) -> &mut [Self::Entry] {
        self.base.as_mut_slice()
    }

    fn into_entries(self) -> Vec<Self::Entry> {
        self.base.into_vec()
    }
}
