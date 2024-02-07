//! `KeyedVecSet` is a vector-based map implementation which retains the order of inserted entries.

mod entry;
mod impls;
mod iter;
#[cfg(feature = "serde")]
mod serde;

use alloc::vec::{self, Vec};
use core::borrow::Borrow;
use core::mem;
use core::ops::RangeBounds;
use core::slice;

pub use self::entry::{Entry, OccupiedEntry, VacantEntry};

/// Key accessor for elements which have their own keys, used for `KeyedVecSet`.
pub trait Keyed<K>
where
    K: ?Sized,
{
    /// key accessor for the element.
    fn key(&self) -> &K;
}

// KeyMap
impl<K, V> Keyed<K> for (K, V) {
    fn key(&self) -> &K {
        &self.0
    }
}

// KeySet
impl<K> Keyed<K> for K {
    fn key(&self) -> &K {
        &self
    }
}

impl Keyed<str> for alloc::string::String {
    fn key(&self) -> &str {
        self.as_str()
    }
}

/// A vector-based map implementation which retains the order of inserted entries.
///
/// Internally it is represented as a `Vec<(K, V)>` to support keys that are neither `Hash` nor
/// `Ord`.
#[derive(Clone, Debug)]
pub struct KeyedVecSet<K, V> {
    pub(crate) base: Vec<V>,
    _marker: core::marker::PhantomData<K>,
}

impl<K, V> KeyedVecSet<K, V> {
    /// Create a new map. (Does not allocate.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<i32, &str> = KeyedVecSet::new();
    /// ```
    pub const fn new() -> Self {
        KeyedVecSet {
            base: Vec::new(),
            _marker: core::marker::PhantomData,
        }
    }

    /// Create a new map with capacity for `capacity` key-value pairs. (Does not allocate if
    /// `capacity` is zero.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<i32, &str> = KeyedVecSet::with_capacity(10);
    /// assert_eq!(map.len(), 0);
    /// assert!(map.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        KeyedVecSet {
            base: Vec::with_capacity(capacity),
            _marker: core::marker::PhantomData,
        }
    }

    /// Returns the number of entries the map can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<i32, (i32, &str)> = KeyedVecSet::with_capacity(10);
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut a = KeyedVecSet::<u32, (u32, &str)>::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert((1, "a"));
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut a = KeyedVecSet::<i32, (i32, &str)>::new();
    /// assert!(a.is_empty());
    /// a.insert((1, "a"));
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut a = KeyedVecSet::<i32, (i32, &str)>::new();
    /// a.insert((1, "a"));
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("b", 2), ("c", 3), ("d", 4)]);
    /// map.truncate(2);
    /// assert_eq!(map, KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("b", 2)]));
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the map's current length:
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("b", 2), ("c", 3), ("d", 4)]);
    /// map.truncate(8);
    /// assert_eq!(map, KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("b", 2), ("c", 3), ("d", 4)]));
    /// ```
    pub fn truncate(&mut self, len: usize) {
        self.base.truncate(len);
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the given
    /// `KeyedVecSet<K, V>`. The collection may reserve more space to speculatively avoid frequent
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1)]);
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<i32, (i32, i32)> = (0..8).map(|x| (x, x*10)).collect();
    /// map.retain(|&v| v.0 % 2 == 0);
    /// assert_eq!(map.len(), 4);
    /// ```
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&V) -> bool,
    {
        self.base.retain(f);
    }

    /// Shrinks the capacity of the map as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with
    /// the resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<i32, (i32, i32)> = KeyedVecSet::with_capacity(100);
    /// map.insert((1, 2));
    /// map.insert((3, 4));
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map: KeyedVecSet<i32, (i32, i32)> = KeyedVecSet::with_capacity(100);
    /// map.insert((1, 2));
    /// map.insert((3, 4));
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("b", 2), ("c", 3)]);
    /// let map2 = map.split_off(1);
    /// assert_eq!(map, KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1)]));
    /// assert_eq!(map2, KeyedVecSet::<&str, (&str, u32)>::from_iter([("b", 2), ("c", 3)]));
    /// ```
    pub fn split_off(&mut self, at: usize) -> KeyedVecSet<K, V> {
        KeyedVecSet {
            base: self.base.split_off(at),
            _marker: core::marker::PhantomData,
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut v = KeyedVecSet::<&str, (&str, i32)>::from_iter([("a", 1), ("b", 2), ("c", 3)]);
    /// let u: KeyedVecSet<_, _> = v.drain(1..).collect();
    /// assert_eq!(v, KeyedVecSet::<&str, (&str, i32)>::from([("a", 1)]));
    /// assert_eq!(u, KeyedVecSet::<&str, (&str, i32)>::from([("b", 2), ("c", 3)]));
    ///
    /// // A full range clears the vector, like `clear()` does
    /// v.drain(..);
    /// assert_eq!(v, KeyedVecSet::new());
    /// ```
    pub fn drain<R>(&mut self, range: R) -> vec::Drain<'_, V>
    where
        R: RangeBounds<usize>,
    {
        self.base.drain(range)
    }

    /// Extracts a slice containing the map entries.
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("b", 2), ("a", 1), ("c", 3)]);
    /// let slice = map.as_slice();
    /// assert_eq!(slice, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    pub fn as_slice(&self) -> &[V] {
        self.base.as_slice()
    }

    /// Extracts a slice containing the map entries.
    ///
    /// # Safety
    /// Changing key may cause the map to be unsorted or have duplicate keys.
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("b", 2), ("a", 1), ("c", 3)]);
    /// let slice = map.as_mut_slice();
    /// slice[0].1 = 10;
    /// assert_eq!(slice, [("a", 10), ("b", 2), ("c", 3)]);
    /// ```
    pub unsafe fn as_mut_slice(&mut self) -> &mut [V] {
        self.base.as_mut_slice()
    }

    /// Copies the map entries into a new `Vec<(K, V)>`.
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("b", 2), ("a", 1), ("c", 3)]);
    /// let vec = map.to_vec();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    /// // Here, `map` and `vec` can be modified independently.
    /// ```
    pub fn to_vec(&self) -> Vec<V>
    where
        V: Clone,
    {
        self.base.to_vec()
    }

    /// Takes ownership of the map and returns its entries as a `Vec<(K, V)>`.
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let map = KeyedVecSet::<&str, (&str, i32)>::from([("b", 2), ("a", 1), ("c", 3)]);
    /// let vec = map.into_vec();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    pub fn into_vec(self) -> Vec<V> {
        self.base
    }

    /// Takes ownership of provided vector and converts it into `KeyedVecSet`.
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut vec = vec![("b", 2), ("a", 1), ("c", 3), ("b", 4)];
    /// vec.sort_by_key(|slot| slot.0);
    /// vec.dedup_by_key(|slot| slot.0);
    /// // SAFETY: We've just deduplicated the vector.
    /// let map = unsafe { KeyedVecSet::from_vec_unchecked(vec) };
    ///
    /// assert_eq!(map, KeyedVecSet::<&str, (&str, i32)>::from([("b", 2), ("a", 1), ("c", 3)]));
    /// ```
    ///
    /// [slice-sort-by-key]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_key
    pub unsafe fn from_vec_unchecked(base: Vec<V>) -> Self {
        KeyedVecSet {
            base,
            _marker: core::marker::PhantomData,
        }
    }
}

// Lookup operations.
impl<K, V> KeyedVecSet<K, V> {
    /// Return `true` if an equivalent to `key` exists in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<i32, (i32, &str)>::new();
    /// map.insert((1, "a"));
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
        V: Keyed<K>,
    {
        self.binary_search(key).is_ok()
    }

    /// Get the first key-value pair.
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("b", 2)]);
    /// assert_eq!(map.first(), Some(&("a", 1)));
    /// ```
    pub fn first(&self) -> Option<&V> {
        self.base.first()
    }

    /// Get the first key-value pair, with mutable access to the value.
    ///
    /// # Safety
    /// Changing key may cause the map to be unsorted or have duplicate keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("b", 2)]);
    ///
    /// if let Some(v) = map.first_mut() {
    ///     v.1 = v.1 + 10;
    /// }
    /// assert_eq!(map.first(), Some(&("a", 11)));
    /// ```
    pub unsafe fn first_mut(&mut self) -> Option<&mut V> {
        self.base.first_mut()
    }

    /// Get the last key-value pair.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("b", 2)]);
    /// assert_eq!(map.last(), Some(&("b", 2)));
    /// map.pop();
    /// map.pop();
    /// assert_eq!(map.last(), None);
    /// ```
    pub fn last(&self) -> Option<&V> {
        self.base.last()
    }

    /// Get the last key-value pair, with mutable access to the value.
    ///
    /// # Safety
    /// Changing key may cause the map to be unsorted or have duplicate keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("b", 2)]);
    ///
    /// if let Some(v) = map.last_mut() {
    ///     v.1 += 10;
    /// }
    /// assert_eq!(map.last(), Some(&("b", 12)));
    /// ```
    pub unsafe fn last_mut(&mut self) -> Option<&mut V> {
        self.base.last_mut()
    }

    /// Return a reference to the value stored for `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<i32, (i32, &str)>::new();
    /// map.insert((1, "a"));
    /// assert_eq!(map.get(&1), Some(&(1, "a")));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
        V: Keyed<K>,
    {
        let index = self.binary_search(key).ok()?;
        Some(&self.base[index])
    }

    /// Return a mutable reference to the value stored for `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<i32, (i32, &str)>::new();
    /// map.insert((1, "a"));
    /// if let Some(x) = map.get_mut(&1) {
    ///     x.1 = "b";
    /// }
    /// assert_eq!(map[&1], (1, "b"));
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
        V: Keyed<K>,
    {
        let index = self.binary_search(key).ok()?;
        Some(&mut self.base[index])
    }

    /// Return references to the key-value pair stored at `index`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<i32, (i32, &str)>::new();
    /// map.insert((1, "a"));
    /// assert_eq!(map.get_index(0), Some(&(1, "a")));
    /// assert_eq!(map.get_index(1), None);
    /// ```
    pub fn get_index(&self, index: usize) -> Option<&V> {
        self.base.get(index)
    }

    /// Return a reference to the key and a mutable reference to the value stored at `index`, if it
    /// is present, else `None`.
    ///
    /// # Safety
    /// Changing key may cause the map to be unsorted or have duplicate keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<i32, (i32, &str)>::new();
    /// map.insert((1, "a"));
    /// if let Some((_, v)) = map.get_index_mut(0) {
    ///     *v = "b";
    /// }
    /// assert_eq!(map[0].1, "b");
    /// ```
    pub unsafe fn get_index_mut(&mut self, index: usize) -> Option<&mut V> {
        self.base.get_mut(index)
    }

    /// Return the index and references to the key-value pair stored for `key`, if it is present,
    /// else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<i32, (i32, &str)>::new();
    /// map.insert((1, "a"));
    /// assert_eq!(map.get_full(&1), Ok((0, &(1, "a"))));
    /// assert_eq!(map.get_full(&2), Err(1));
    /// ```
    pub fn get_full<Q>(&self, key: &Q) -> Result<(usize, &V), usize>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
        V: Keyed<K>,
    {
        let index = self.binary_search(key)?;
        Ok((index, &self.base[index]))
    }

    /// Return the index, a reference to the key and a mutable reference to the value stored for
    /// `key`, if it is present, else `None`.
    ///
    /// # Safety
    /// Changing key may cause the map to be unsorted or have duplicate keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<i32, (i32, &str)>::new();
    /// map.insert((1, "a"));
    ///
    /// if let Ok((_, v)) = map.get_full_mut(&1) {
    ///     v.1 = "b";
    /// }
    /// assert_eq!(map.get(&1), Some(&(1, "b")));
    /// ```
    pub unsafe fn get_full_mut<Q>(&mut self, key: &Q) -> Result<(usize, &mut V), usize>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
        V: Keyed<K>,
    {
        let index = self.binary_search(key)?;
        Ok((index, &mut self.base[index]))
    }

    /// Return item index, if it exists in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, i32)>::new();
    /// map.insert(("a", 10));
    /// map.insert(("b", 20));
    /// assert_eq!(map.binary_search("a"), Ok(0));
    /// assert_eq!(map.binary_search("b"), Ok(1));
    /// assert_eq!(map.binary_search("c"), Err(2));
    /// ```
    pub fn binary_search<Q>(&self, key: &Q) -> Result<usize, usize>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
        V: Keyed<K>,
    {
        self.base
            .binary_search_by(|slot| slot.key().borrow().cmp(key))
    }
}

// Removal operations.
impl<K, V> KeyedVecSet<K, V> {
    /// Removes the last element from the map and returns it, or [`None`] if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("b", 2)]);
    /// assert_eq!(map.pop(), Some(("b", 2)));
    /// assert_eq!(map.pop(), Some(("a", 1)));
    /// assert!(map.is_empty());
    /// assert_eq!(map.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<V> {
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<u32, (u32, &str)>::from_iter([(1, "a"), (2, "b"), (3, "c"), (4, "d")]);
    /// assert_eq!(map.remove(&2), Some((2, "b")));
    /// assert_eq!(map.remove(&2), None);
    /// assert_eq!(map, KeyedVecSet::<u32, (u32, &str)>::from([(1, "a"), (3, "c"), (4, "d")]));
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
        V: Keyed<K>,
    {
        let key = key.borrow();
        self.binary_search(key)
            .ok()
            .map(|index| self.remove_index(index))
    }

    /// Removes and returns the key-value pair at position `index` within the map, shifting all
    /// elements after it to the left.
    ///
    /// If you don't need the order of elements to be preserved, use [`swap_remove`] instead.
    ///
    /// [`swap_remove`]: KeyedVecSet::swap_remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut v = KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("b", 2), ("c", 3)]);
    /// assert_eq!(v.remove_index(1), ("b", 2));
    /// assert_eq!(v, KeyedVecSet::<&str, (&str, u32)>::from_iter([("a", 1), ("c", 3)]));
    /// ```
    pub fn remove_index(&mut self, index: usize) -> V {
        self.base.remove(index)
    }
}

// Insertion operations.
impl<K, V> KeyedVecSet<K, V>
where
    K: Ord,
    V: Keyed<K>,
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<i32, (i32, &str)>::new();
    /// assert_eq!(map.insert((37, "a")), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert((37, "b"));
    /// assert_eq!(map.insert((37, "c")), Some((37, "b")));
    /// assert_eq!(map[&37].1, "c");
    /// ```
    pub fn insert(&mut self, value: V) -> Option<V> {
        self.insert_full(value).1
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
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, i32)>::new();
    /// assert_eq!(map.insert_full(("a", 1)), (0, None));
    /// assert_eq!(map.insert_full(("b", 2)), (1, None));
    /// assert_eq!(map.insert_full(("b", 3)), (1, Some(("b", 2))));
    /// assert_eq!(map["b"].1, 3);
    /// ```
    pub fn insert_full(&mut self, value: V) -> (usize, Option<V>) {
        let key = value.key();
        match self.binary_search(&key) {
            Ok(index) => {
                let old_slot = mem::replace(&mut self.base[index], value);
                (index, Some(old_slot))
            }
            Err(index) => {
                self.base.insert(index, value);
                (index, None)
            }
        }
    }

    /// Get the given key's corresponding entry in the map for insertion and/or in-place
    /// manipulation.
    ///
    /// ## Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut letters = KeyedVecSet::<char, (char, usize)>::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     letters.entry(ch).and_modify(|pair| pair.1 += 1).or_insert((ch, 1));
    /// }
    ///
    /// assert_eq!(letters[&'s'].1, 2);
    /// assert_eq!(letters[&'t'].1, 3);
    /// assert_eq!(letters[&'u'].1, 1);
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
impl<K, V: Keyed<K>> KeyedVecSet<K, V> {
    /// An iterator visiting all key-value pairs in insertion order. The iterator element type is
    /// `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let map = KeyedVecSet::<&str, (&str, i32)>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {key} val: {val}");
    /// }
    /// ```
    pub fn iter(&self) -> slice::Iter<'_, V> {
        self.base.iter()
    }

    /// An iterator visiting all key-value pairs in insertion order, with mutable references to the
    /// values. The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Safety
    /// Changing key may cause the map to be unsorted or have duplicate keys.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let mut map = KeyedVecSet::<&str, (&str, i32)>::from([
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
    pub unsafe fn iter_mut(&mut self) -> impl core::iter::Iterator<Item = &mut V> {
        self.base.iter_mut()
    }

    /// Creates a consuming iterator visiting all the values in insertion order. The object cannot
    /// be used after calling this. The iterator element type is `V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let map = KeyedVecSet::<&str, (&str, i32)>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// let mut vec: Vec<(&str, i32)> = map.into_iter().collect();
    /// assert_eq!(vec, [("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    pub fn into_iter(self) -> vec::IntoIter<V> {
        self.base.into_iter()
    }

    /// An iterator visiting all keys in insertion order. The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecset::KeyedVecSet;
    ///
    /// let map = KeyedVecSet::<&str, (&str, i32)>::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for key in map.keys() {
    ///     println!("{key}");
    /// }
    /// ```
    pub fn keys(&self) -> impl core::iter::Iterator<Item = &K> + '_ {
        self.iter().map(|slot| slot.key())
    }
}
