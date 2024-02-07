//! `VecMap` is a vector-based map implementation which retains the order of inserted entries.

mod entry;
mod impls;
mod iter;
#[cfg(feature = "serde")]
mod serde;

use super::KeyedVecSet;
use alloc::vec::{self, Vec};
use core::borrow::Borrow;
use core::ops::RangeBounds;

pub use self::entry::{Entry, OccupiedEntry, VacantEntry};
pub use self::iter::*;

// The type used to store entries in a `VecMap`.
//
// It is just a alias type of`(K, V)`
type Slot<K, V> = (K, V);

/// A vector-based map implementation which retains the order of inserted entries.
///
/// Internally it is represented as a `Vec<(K, V)>` to support keys that are neither `Hash` nor
/// `Ord`.
#[derive(Clone, Debug)]
pub struct VecMap<K, V> {
    pub(crate) base: KeyedVecSet<K, Slot<K, V>>,
}

impl<K, V> VecMap<K, V> {
    fn refs(slot: &Slot<K, V>) -> (&K, &V) {
        (&slot.0, &slot.1)
    }

    fn ref_mut(slot: &mut Slot<K, V>) -> (&K, &mut V) {
        (&slot.0, &mut slot.1)
    }

    /// Create a new map. (Does not allocate.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map: VecMap<i32, &str> = VecMap::new();
    /// ```
    pub const fn new() -> Self {
        VecMap {
            base: KeyedVecSet::new(),
        }
    }

    /// Create a new map with capacity for `capacity` key-value pairs. (Does not allocate if
    /// `capacity` is zero.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map: VecMap<i32, &str> = VecMap::with_capacity(10);
    /// assert_eq!(map.len(), 0);
    /// assert!(map.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        VecMap {
            base: KeyedVecSet::with_capacity(capacity),
        }
    }

    /// Returns the number of entries the map can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
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
    /// use vecset::VecMap;
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
    /// use vecset::VecMap;
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
    /// use vecset::VecMap;
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
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::from([("a", 1), ("b", 2), ("c", 3), ("d", 4)]);
    /// map.truncate(2);
    /// assert_eq!(map, VecMap::from([("a", 1), ("b", 2)]));
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the map's current length:
    ///
    /// ```
    /// use vecset::VecMap;
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
    /// use vecset::VecMap;
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
    /// use vecset::VecMap;
    ///
    /// let mut map: VecMap<i32, i32> = (0..8).map(|x| (x, x*10)).collect();
    /// map.retain(|&k, _| k % 2 == 0);
    /// assert_eq!(map.len(), 4);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &V) -> bool,
    {
        self.base.retain(|slot| {
            let (key, value) = (&slot.0, &slot.1);
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
    /// use vecset::VecMap;
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
    /// use vecset::VecMap;
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
    /// use vecset::VecMap;
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
    /// use vecset::{vecmap, VecMap};
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
    pub fn drain<R>(&mut self, range: R) -> vec::Drain<'_, (K, V)>
    where
        R: RangeBounds<usize>,
    {
        self.base.drain(range)
    }

    /// Extracts a slice containing the map entries.
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let slice = map.as_slice();
    /// assert_eq!(slice, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    pub fn as_slice(&self) -> &[(K, V)] {
        // SAFETY: `&[Slot<K, V>]` and `&[(K, V)]` have the same memory layout.
        unsafe { &*(self.base.as_slice() as *const [Slot<K, V>] as *const [(K, V)]) }
    }

    /// Copies the map entries into a new `Vec<(K, V)>`.
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let vec = map.to_vec();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
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
    /// use vecset::VecMap;
    ///
    /// let map = VecMap::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let vec = map.into_vec();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    pub fn into_vec(self) -> Vec<(K, V)> {
        self.base.into_vec()
    }

    /// Takes ownership of provided vector and converts it into `VecMap`.
    ///
    /// # Safety
    ///
    /// The vector must be sorted and have no duplicate keys. One way to guarantee it is to
    /// sort the vector (e.g. by using [`[T]::sort_by_key`][slice-sort-by-key]) and then drop
    /// duplicate keys (e.g. by using [`Vec::dedup_by_key`]).
    ///
    /// # Example
    ///
    /// ```
    /// use vecset::VecMap;
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
        let base = KeyedVecSet::from_vec_unchecked(vec);
        VecMap { base }
    }
}

// Lookup operations
impl<K, V> VecMap<K, V> {
    /// Return `true` if an equivalent to `key` exists in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.base.contains_key(key)
    }

    /// Get the first key-value pair.
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    /// assert_eq!(map.first(), Some((&"a", &1)));
    /// ```
    pub fn first(&self) -> Option<(&K, &V)> {
        self.base.first().map(Self::refs)
    }

    /// Get the first key-value pair, with mutable access to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    ///
    /// if let Some((_, v)) = map.first_mut() {
    ///     *v = *v + 10;
    /// }
    /// assert_eq!(map.first(), Some((&"a", &11)));
    /// ```
    pub fn first_mut(&mut self) -> Option<(&K, &mut V)> {
        unsafe { self.base.first_mut().map(Self::ref_mut) }
    }

    /// Get the last key-value pair.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    /// assert_eq!(map.last(), Some((&"b", &2)));
    /// map.pop();
    /// map.pop();
    /// assert_eq!(map.last(), None);
    /// ```
    pub fn last(&self) -> Option<(&K, &V)> {
        self.base.last().map(Self::refs)
    }

    /// Get the last key-value pair, with mutable access to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    ///
    /// if let Some((_, v)) = map.last_mut() {
    ///     *v = *v + 10;
    /// }
    /// assert_eq!(map.last(), Some((&"b", &12)));
    /// ```
    pub fn last_mut(&mut self) -> Option<(&K, &mut V)> {
        unsafe { self.base.last_mut().map(Self::ref_mut) }
    }

    /// Return a reference to the value stored for `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let slot = self.base.get(key)?;
        Some(&slot.1)
    }

    /// Return a mutable reference to the value stored for `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
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
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let slot = self.base.get_mut(key)?;
        Some(&mut slot.1)
    }

    /// Return references to the key-value pair stored at `index`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_index(0), Some((&1, &"a")));
    /// assert_eq!(map.get_index(1), None);
    /// ```
    pub fn get_index(&self, index: usize) -> Option<(&K, &V)> {
        self.base.get_index(index).map(Self::refs)
    }

    /// Return a reference to the key and a mutable reference to the value stored at `index`, if it
    /// is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// if let Some((_, v)) = map.get_index_mut(0) {
    ///     *v = "b";
    /// }
    /// assert_eq!(map[0], "b");
    /// ```
    pub fn get_index_mut(&mut self, index: usize) -> Option<(&K, &mut V)> {
        unsafe { self.base.get_index_mut(index).map(Self::ref_mut) }
    }

    /// Return the index and references to the key-value pair stored for `key`, if it is present,
    /// else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_full(&1), Ok((0, &1, &"a")));
    /// assert_eq!(map.get_full(&2), Err(1));
    /// ```
    pub fn get_full<Q>(&self, key: &Q) -> Result<(usize, &K, &V), usize>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let (idx, slot) = self.base.get_full(key)?;
        Ok((idx, &slot.0, &slot.1))
    }

    /// Return the index, a reference to the key and a mutable reference to the value stored for
    /// `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    ///
    /// if let Ok((_, _, v)) = map.get_full_mut(&1) {
    ///     *v = "b";
    /// }
    /// assert_eq!(map.get(&1), Some(&"b"));
    /// ```
    pub fn get_full_mut<Q>(&mut self, key: &Q) -> Result<(usize, &K, &mut V), usize>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let (idx, slot) = unsafe { self.base.get_full_mut(key) }?;
        Ok((idx, &slot.0, &mut slot.1))
    }

    /// Return references to the key-value pair stored for `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.base.get(key).map(Self::refs)
    }

    /// Return item index, if it exists in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert("a", 10);
    /// map.insert("b", 20);
    /// assert_eq!(map.binary_search("a"), Ok(0));
    /// assert_eq!(map.binary_search("b"), Ok(1));
    /// assert_eq!(map.binary_search("c"), Err(2));
    /// ```
    pub fn binary_search<Q>(&self, key: &Q) -> Result<usize, usize>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.base.binary_search(key)
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
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    /// assert_eq!(map.pop(), Some(("b", 2)));
    /// assert_eq!(map.pop(), Some(("a", 1)));
    /// assert!(map.is_empty());
    /// assert_eq!(map.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<(K, V)> {
        self.base.pop()
    }

    /// Remove the key-value pair equivalent to `key` and return its value.
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::from_iter([(1, "a"), (2, "b"), (3, "c"), (4, "d")]);
    /// assert_eq!(map.remove(&2), Some("b"));
    /// assert_eq!(map.remove(&2), None);
    /// assert_eq!(map, VecMap::from_iter([(1, "a"), (3, "c"), (4, "d")]));
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.base.remove(key).map(|slot| slot.1)
    }

    /// Remove and return the key-value pair equivalent to `key`.
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::from_iter([(1, "a"), (2, "b"), (3, "c"), (4, "d")]);
    /// assert_eq!(map.remove_entry(&2), Some((2, "b")));
    /// assert_eq!(map.remove_entry(&2), None);
    /// assert_eq!(map, VecMap::from_iter([(1, "a"), (3, "c"), (4, "d")]));
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.base.remove(key)
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
    /// use vecset::VecMap;
    ///
    /// let mut v = VecMap::from([("a", 1), ("b", 2), ("c", 3)]);
    /// assert_eq!(v.remove_index(1), ("b", 2));
    /// assert_eq!(v, VecMap::from([("a", 1), ("c", 3)]));
    /// ```
    pub fn remove_index(&mut self, index: usize) -> (K, V) {
        self.base.remove_index(index)
    }
}

// Insertion operations.
impl<K, V> VecMap<K, V>
where
    K: Ord,
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
    /// use vecset::VecMap;
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
    /// use vecset::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// assert_eq!(map.insert_full("a", 1), (0, None));
    /// assert_eq!(map.insert_full("b", 2), (1, None));
    /// assert_eq!(map.insert_full("b", 3), (1, Some(2)));
    /// assert_eq!(map["b"], 3);
    /// ```
    pub fn insert_full(&mut self, key: K, value: V) -> (usize, Option<V>) {
        let (index, removed) = self.base.insert_full((key, value));
        (index, removed.map(|slot| slot.1))
    }

    /// Get the given key's corresponding entry in the map for insertion and/or in-place
    /// manipulation.
    ///
    /// ## Examples
    ///
    /// ```
    /// use vecset::VecMap;
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
        match self.binary_search(&key) {
            Ok(index) => Entry::Occupied(OccupiedEntry::new(self, key, index)),
            Err(index) => Entry::Vacant(VacantEntry::new(self, key, index)),
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
    /// use vecset::VecMap;
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
        Iter::new(self.as_slice())
    }

    /// An iterator visiting all key-value pairs in insertion order, with mutable references to the
    /// values. The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
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
        IterMut::new(unsafe { self.base.as_mut_slice() })
    }

    /// An iterator visiting all keys in insertion order. The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
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
        Keys::new(self.as_slice())
    }

    /// Creates a consuming iterator visiting all the keys in insertion order. The object cannot be
    /// used after calling this. The iterator element type is `K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
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
        IntoKeys::new(self.base.into_vec())
    }

    /// An iterator visiting all values in insertion order. The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
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
        Values::new(self.as_slice())
    }

    /// An iterator visiting all values mutably in insertion order. The iterator element type is
    /// `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
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
        ValuesMut::new(unsafe { self.base.as_mut_slice() })
    }

    /// Creates a consuming iterator visiting all the values in insertion order. The object cannot
    /// be used after calling this. The iterator element type is `V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::VecMap;
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
        IntoValues::new(self.base.into_vec())
    }
}

// https://github.com/martinohmann/vecmap-rs/issues/18
//
// If `Slot<K, V>` does not have the same memory layout as `(K, V)`, e.g. due to possible field
// reordering, this test will:
//
// - Segfault with "SIGSEGV: invalid memory reference" in the `unsafe` block in `VecMap::as_slice`
//   when run via `cargo test`.
// - Trigger a miri error when run via `cargo +nightly miri test`.
#[test]
fn issue_18() {
    use alloc::string::String;
    use core::{fmt, mem};

    fn test<K, V>(slice: &[(K, V)])
    where
        K: Clone + Ord + fmt::Debug,
        V: Clone + PartialEq + fmt::Debug,
    {
        assert_eq!(mem::size_of::<Slot<K, V>>(), mem::size_of::<(K, V)>());
        assert_eq!(mem::align_of::<Slot<K, V>>(), mem::align_of::<(K, V)>());

        let map = VecMap::from(slice);
        assert_eq!(map.as_slice(), slice);
    }

    test(&[(1i64, String::from("foo")), (2, String::from("bar"))]);
    test(&[(String::from("bar"), 2), (String::from("foo"), 1i64)]);
    test(&[(false, 2), (true, 1i64)]);
    test(&[(1i64, true), (2, false)]);
}
