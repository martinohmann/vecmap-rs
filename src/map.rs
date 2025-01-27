//! `VecMap` is a vector-based map implementation which retains the order of inserted entries.

mod entry;
mod impls;
mod iter;
mod mutable_keys;
#[cfg(feature = "serde")]
mod serde;
mod slice;

use super::{Entries, Slot, TryReserveError};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::mem;
use core::ops::RangeBounds;

pub use self::entry::{Entry, OccupiedEntry, VacantEntry};
pub use self::iter::*;
pub use self::mutable_keys::MutableKeys;
pub use self::slice::Slice;

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

    /// Reserves the minimum capacity for at least `additional` more elements to be inserted in the
    /// given `VecMap<K, V>`. Unlike [`reserve`], this will not deliberately over-allocate to
    /// speculatively avoid frequent allocations. After calling `reserve_exact`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if the capacity is already
    /// sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests. Therefore,
    /// capacity can not be relied upon to be precisely minimal. Prefer [`reserve`] if future
    /// insertions are expected.
    ///
    /// [`reserve`]: VecMap::reserve
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
    pub fn reserve_exact(&mut self, additional: usize) {
        self.base.reserve_exact(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted in the
    /// given `VecMap<K, V>`. The collection may reserve more space to speculatively avoid frequent
    /// reallocations. After calling `try_reserve`, capacity will be greater than or equal to
    /// `self.len() + additional` if it returns `Ok(())`. Does nothing if capacity is already
    /// sufficient. This method preserves the contents even if an error occurs.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::{TryReserveError, VecMap};
    ///
    /// fn process_data(data: &[(u32, u32)]) -> Result<VecMap<u32, u32>, TryReserveError> {
    ///     let mut output = VecMap::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|(k, v)| {
    ///         (k * 2 + 5, v * 2 + 5) // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[(1, 1), (2, 2), (3, 3)]).expect("why is the test harness OOMing?");
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional` elements to be inserted in
    /// the given `VecMap<K, V>`. Unlike [`try_reserve`], this will not deliberately over-allocate
    /// to speculatively avoid frequent allocations. After calling `try_reserve_exact`, capacity
    /// will be greater than or equal to `self.len() + additional` if it returns `Ok(())`. Does
    /// nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests. Therefore,
    /// capacity can not be relied upon to be precisely minimal. Prefer [`try_reserve`] if future
    /// insertions are expected.
    ///
    /// [`try_reserve`]: VecMap::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::{TryReserveError, VecMap};
    ///
    /// fn process_data(data: &[(u32, u32)]) -> Result<VecMap<u32, u32>, TryReserveError> {
    ///     let mut output = VecMap::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve_exact(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|(k, v)| {
    ///         (k * 2 + 5, v * 2 + 5) // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[(1, 1), (2, 2), (3, 3)]).expect("why is the test harness OOMing?");
    /// ```
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve_exact(additional)
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

    /// Returns a slice of all the key-value pairs in the map.
    ///
    /// This method is automatically called via `VecMap<K, V>`'s `Deref` implementation.
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let slice = map.as_slice();
    /// assert!(slice.contains_key(&"a"));
    /// assert!(!slice.contains_key(&"z"));
    /// ```
    pub fn as_slice(&self) -> &Slice<K, V> {
        Slice::from_slice(self.as_entries())
    }

    /// Returns a mutable slice of all the key-value pairs in the map.
    ///
    /// This method is automatically called via `VecMap<K, V>`'s `DerefMut` implementation.
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let slice = map.as_mut_slice();
    /// slice.swap_indices(0, 1);
    /// assert_eq!(map.as_std_slice(), [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut Slice<K, V> {
        Slice::from_mut_slice(self.as_entries_mut())
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

    /// Moves all key-value pairs from `other` into `self`, leaving `other` empty.
    ///
    /// This is equivalent to calling [`insert`][Self::insert] for each key-value pair from `other`
    /// in order, which means that for keys that already exist in `self`, their value is updated in
    /// the current position.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// // Note: Key (3) is present in both maps.
    /// let mut a = VecMap::from([(3, "c"), (2, "b"), (1, "a")]);
    /// let mut b = VecMap::from([(3, "d"), (4, "e"), (5, "f")]);
    /// let old_capacity = b.capacity();
    ///
    /// a.append(&mut b);
    ///
    /// assert_eq!(a.len(), 5);
    /// assert_eq!(b.len(), 0);
    /// assert_eq!(b.capacity(), old_capacity);
    ///
    /// assert!(a.keys().eq(&[3, 2, 1, 4, 5]));
    /// assert_eq!(a[&3], "d"); // "c" was overwritten.
    /// ```
    pub fn append(&mut self, other: &mut VecMap<K, V>) {
        self.extend(other.drain(..));
    }
}

// Iterator adapters.
impl<K, V> VecMap<K, V> {
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
