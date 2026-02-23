//! Internal backing type for `VecMap` and `VecSet`.
//!
//! This module provides `KeyedVecSet<K, V>`, a generic ordered collection that maintains insertion
//! order and uses linear search for lookups.

// TODO: replace ```ignore to ``` when making this module public

mod impls;

use super::TryReserveError;
use alloc::vec::{self, Vec};
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::mem;
use core::ops::RangeBounds;
use core::slice;

/// Key accessor for elements which have their own keys, used for `KeyedVecSet`.
///
/// This trait allows `KeyedVecSet` to extract keys from its elements, enabling a single
/// implementation to work for both map-like structures (where keys and values are separate)
/// and set-like structures (where the element is its own key).
pub(crate) trait Keyed<K>
where
    K: ?Sized,
{
    /// Key accessor for the element.
    fn key(&self) -> &K;
}

// For VecSet: T serves as its own key
impl<K> Keyed<K> for K {
    fn key(&self) -> &K {
        self
    }
}

/// A vector-based collection which retains the order of inserted entries.
///
/// Internally it is represented as a `Vec<V>`. `V` has to implement `Keyed<K>` to retrieve the key
/// from its value.
/// This design allows any data type to be used as an element of `KeyedVecSet`, as long as it
/// contains data that can be considered as a key.
///
/// When `V = T` (where `T: Keyed<T>`), `KeyedVecSet<T, T>` is equivalent to `VecSet<T>`.
/// When `V = Slot<K, MV>`, `KeyedVecSet<K, Slot<K, MV>>` is equivalent to `VecMap<K, MV>`.
///
/// # Type Parameters
///
/// - `K`: The key type used for lookups. Must implement `Eq` for key-based operations.
/// - `V`: The value type, which must implement `Keyed<K>` to provide access to keys.
#[derive(Clone, Debug)]
pub(crate) struct KeyedVecSet<K, V> {
    base: Vec<V>,
    _marker: core::marker::PhantomData<K>,
}

impl<K, V> KeyedVecSet<K, V> {
    /// Create a new set. (Does not allocate.)
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::KeyedVecSet;
    ///
    /// let set: KeyedVecSet<i32, (i32, &str)> = KeyedVecSet::new();
    /// ```
    pub const fn new() -> Self {
        KeyedVecSet {
            base: Vec::new(),
            _marker: core::marker::PhantomData,
        }
    }

    /// Create a new set with capacity for `capacity` elements. (Does not allocate if
    /// `capacity` is zero.)
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::KeyedVecSet;
    ///
    /// let set: KeyedVecSet<i32, (i32, &str)> = KeyedVecSet::with_capacity(10);
    /// assert_eq!(set.len(), 0);
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        KeyedVecSet {
            base: Vec::with_capacity(capacity),
            _marker: core::marker::PhantomData,
        }
    }

    /// Returns the number of elements the set can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::KeyedVecSet;
    ///
    /// let set: KeyedVecSet<i32, (i32, &str)> = KeyedVecSet::with_capacity(10);
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.base.capacity()
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut a = KeyedVecSet::<i32, Entry>::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(Entry(1, "a"));
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.base.len()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut a = KeyedVecSet::<i32, Entry>::new();
    /// assert!(a.is_empty());
    /// a.insert(Entry(1, "a"));
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Clears the set, removing all elements.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut a = KeyedVecSet::<i32, Entry>::new();
    /// a.insert(Entry(1, "a"));
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.base.clear();
    }

    /// Shortens the set, keeping the first `len` elements and dropping the rest.
    ///
    /// If `len` is greater than the set's current length, this has no effect.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(&'static str, i32);
    ///
    /// impl Keyed<&'static str> for Entry {
    ///     fn key(&self) -> &&'static str { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<&str, Entry>::new();
    /// map.insert(Entry("a", 1));
    /// map.insert(Entry("b", 2));
    /// map.insert(Entry("c", 3));
    /// map.insert(Entry("d", 4));
    /// map.truncate(2);
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        self.base.truncate(len);
    }

    /// Reverses the order of elements in the set, in place.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.insert(Entry(3, "c"));
    /// map.reverse();
    /// assert_eq!(map.get_index(0), Some(&Entry(3, "c")));
    /// assert_eq!(map.get_index(1), Some(&Entry(2, "b")));
    /// assert_eq!(map.get_index(2), Some(&Entry(1, "a")));
    /// ```
    pub fn reverse(&mut self) {
        self.base.reverse();
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
    /// ```ignore
    /// use vecmap::keyed::KeyedVecSet;
    ///
    /// let mut set: KeyedVecSet<i32, (i32, &str)> = KeyedVecSet::new();
    /// set.reserve(10);
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.base.reserve(additional);
    }

    /// Reserves the minimum capacity for at least `additional` more elements to be inserted in
    /// the given `KeyedVecSet<K, V>`. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests. Therefore,
    /// capacity can not be relied upon to be precisely minimal. Prefer [`Self::reserve`] if future
    /// insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::KeyedVecSet;
    ///
    /// let mut set: KeyedVecSet<i32, (i32, &str)> = KeyedVecSet::new();
    /// set.reserve_exact(10);
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        self.base.reserve_exact(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted in the
    /// given `KeyedVecSet<K, V>`. The collection may reserve more space to speculatively avoid
    /// frequent reallocations. After calling `try_reserve`, capacity will be greater than or equal
    /// to `self.len() + additional` if it returns `Ok(())`. Does nothing if capacity is already
    /// sufficient. This method preserves the contents even if an error occurs.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::KeyedVecSet;
    ///
    /// let mut set: KeyedVecSet<i32, (i32, &str)> = KeyedVecSet::new();
    /// set.try_reserve(10).expect("should reserve");
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional` more elements to be
    /// inserted in the given `KeyedVecSet<K, V>`. Unlike [`Self::try_reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations. After calling
    /// `try_reserve_exact`, capacity will be greater than or equal to `self.len() + additional`
    /// if it returns `Ok(())`. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests. Therefore,
    /// capacity can not be relied upon to be precisely minimal. Prefer [`Self::try_reserve`] if
    /// future insertions are expected.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::KeyedVecSet;
    ///
    /// let mut set: KeyedVecSet<i32, (i32, &str)> = KeyedVecSet::new();
    /// set.try_reserve_exact(10).expect("should reserve");
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of the set as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with
    /// the resize policy.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::with_capacity(10);
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.base.shrink_to_fit();
    }

    /// Shrinks the capacity of the set with a lower limit. It will drop down no lower than the
    /// supplied limit while maintaining the internal rules and possibly leaving some space in
    /// accordance with the resize policy.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::with_capacity(10);
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.shrink_to(4);
    /// assert!(map.capacity() >= 4);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.base.shrink_to(min_capacity);
    }

    /// Splits the set into two at the given index.
    ///
    /// Returns a newly allocated set containing the elements in the range `[at, len)`. After the
    /// call, the original set will be left containing the elements `[0, at)` with its previous
    /// capacity unchanged.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.insert(Entry(3, "c"));
    /// let map2 = map.split_off(1);
    /// assert_eq!(map.len(), 1);
    /// assert_eq!(map2.len(), 2);
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
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.insert(Entry(3, "c"));
    /// let drained: Vec<_> = map.drain(1..).collect();
    /// assert_eq!(drained, vec![Entry(2, "b"), Entry(3, "c")]);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn drain<R>(&mut self, range: R) -> vec::Drain<'_, V>
    where
        R: RangeBounds<usize>,
    {
        self.base.drain(range)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.insert(Entry(3, "c"));
    /// map.retain(|entry| entry.0 % 2 == 1);
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&V) -> bool,
    {
        self.base.retain(f);
    }

    /// Retains only the elements specified by the predicate (with mutable access).
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.insert(Entry(3, "c"));
    /// map.retain_mut(|entry| {
    ///     entry.0 += 10;
    ///     entry.0 % 2 == 1
    /// });
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn retain_mut<F>(&mut self, f: F)
    where
        F: FnMut(&mut V) -> bool,
    {
        self.base.retain_mut(f);
    }

    /// Sorts the set with a comparator function.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(3, "c"));
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.sort_by(|a, b| a.0.cmp(&b.0));
    /// assert_eq!(map.get_index(0), Some(&Entry(1, "a")));
    /// ```
    pub fn sort_by<F>(&mut self, compare: F)
    where
        F: FnMut(&V, &V) -> Ordering,
    {
        self.base.sort_by(compare);
    }

    /// Sorts the set with a comparator function (unstable).
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(3, "c"));
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    /// assert_eq!(map.get_index(0), Some(&Entry(1, "a")));
    /// ```
    pub fn sort_unstable_by<F>(&mut self, compare: F)
    where
        F: FnMut(&V, &V) -> Ordering,
    {
        self.base.sort_unstable_by(compare);
    }

    /// Sort the set's values in place using a key extraction function.
    ///
    /// During sorting, the function is called at most once per entry, by using temporary storage
    /// to remember the results of its evaluation. The order of calls to the function is
    /// unspecified and may change between versions of `vecmap-rs` or the standard library.
    ///
    /// See [`slice::sort_by_cached_key`] for more details.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(3, "c"));
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.sort_by_cached_key(|entry| entry.0);
    /// assert_eq!(map.get_index(0), Some(&Entry(1, "a")));
    /// ```
    pub fn sort_by_cached_key<T, F>(&mut self, sort_key: F)
    where
        T: Ord,
        F: FnMut(&V) -> T,
    {
        self.base.sort_by_cached_key(sort_key);
    }

    /// Swaps the position of two elements in the set.
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
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.swap_indices(0, 1);
    /// assert_eq!(map.get_index(0), Some(&Entry(2, "b")));
    /// assert_eq!(map.get_index(1), Some(&Entry(1, "a")));
    /// ```
    pub fn swap_indices(&mut self, a: usize, b: usize) {
        self.base.swap(a, b);
    }

    /// Extracts a slice containing the set elements.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// let slice = map.as_slice();
    /// assert_eq!(slice.len(), 2);
    /// ```
    pub fn as_slice(&self) -> &[V] {
        self.base.as_slice()
    }

    /// Extracts a mutable slice containing the set elements.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// let slice = map.as_mut_slice();
    /// slice[0] = Entry(3, "c");
    /// assert_eq!(map.get_index(0), Some(&Entry(3, "c")));
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [V] {
        self.base.as_mut_slice()
    }

    /// Copies the set elements into a new `Vec<V>`.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq, Clone)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// let vec = map.to_vec();
    /// assert_eq!(vec, vec![Entry(1, "a"), Entry(2, "b")]);
    /// ```
    pub fn to_vec(&self) -> Vec<V>
    where
        V: Clone,
    {
        self.base.clone()
    }

    /// Takes ownership of the set and returns its elements as a `Vec<V>`.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// let vec = map.into_vec();
    /// assert_eq!(vec, vec![Entry(1, "a"), Entry(2, "b")]);
    /// ```
    pub fn into_vec(self) -> Vec<V> {
        self.base
    }

    /// Takes ownership of provided vector and converts it into `KeyedVecSet`.
    ///
    /// # Safety
    ///
    /// The vector must have no duplicate keys. One way to guarantee it is to sort the vector
    /// (e.g. by using [`[T]::sort_by_key`][slice-sort-by-key]) and then drop duplicate keys
    /// (e.g. by using [`Vec::dedup_by_key`]).
    ///
    /// [slice-sort-by-key]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_key
    pub unsafe fn from_vec_unchecked(base: Vec<V>) -> Self {
        KeyedVecSet {
            base,
            _marker: core::marker::PhantomData,
        }
    }
}

// Lookup operations
impl<K, V> KeyedVecSet<K, V>
where
    V: Keyed<K>,
{
    /// Return item index, if it exists in the set.
    ///
    /// Performs a linear search O(n) over all elements to find the matching key.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(&'static str, i32);
    ///
    /// impl Keyed<&'static str> for Entry {
    ///     fn key(&self) -> &&'static str { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<&str, Entry>::new();
    /// map.insert(Entry("a", 10));
    /// map.insert(Entry("b", 20));
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
        self.base.iter().position(|elem| elem.key().borrow() == key)
    }

    /// Returns `true` if the set contains an element with the given key.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
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

    /// Return a reference to the value stored for `key`, if it is present.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// assert_eq!(map.get(&1), Some(&Entry(1, "a")));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key).map(|index| &self.base[index])
    }

    /// Return item index and a reference to the value stored for `key`, if it is present.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// assert_eq!(map.get_full(&1), Some((0, &Entry(1, "a"))));
    /// assert_eq!(map.get_full(&2), None);
    /// ```
    pub fn get_full<Q>(&self, key: &Q) -> Option<(usize, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| (index, &self.base[index]))
    }

    /// Return a mutable reference to the value stored for `key`, if it is present.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// if let Some(entry) = map.get_mut(&1) {
    ///     *entry = Entry(1, "b");
    /// }
    /// assert_eq!(map.get(&1), Some(&Entry(1, "b")));
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key).map(|index| &mut self.base[index])
    }

    /// Return a reference to the value stored at `index`, if it is present.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// assert_eq!(map.get_index(0), Some(&Entry(1, "a")));
    /// assert_eq!(map.get_index(1), None);
    /// ```
    pub fn get_index(&self, index: usize) -> Option<&V> {
        self.base.get(index)
    }

    /// Return a mutable reference to the value stored at `index`, if it is present.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// if let Some(entry) = map.get_index_mut(0) {
    ///     *entry = Entry(2, "b");
    /// }
    /// assert_eq!(map.get_index(0), Some(&Entry(2, "b")));
    /// ```
    pub fn get_index_mut(&mut self, index: usize) -> Option<&mut V> {
        self.base.get_mut(index)
    }

    /// Get the first element.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// assert_eq!(map.first(), Some(&Entry(1, "a")));
    /// ```
    pub fn first(&self) -> Option<&V> {
        self.base.first()
    }

    /// Get the first element with mutable access.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// if let Some(entry) = map.first_mut() {
    ///     *entry = Entry(3, "c");
    /// }
    /// assert_eq!(map.first(), Some(&Entry(3, "c")));
    /// ```
    pub fn first_mut(&mut self) -> Option<&mut V> {
        self.base.first_mut()
    }

    /// Get the last element.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// assert_eq!(map.last(), Some(&Entry(2, "b")));
    /// ```
    pub fn last(&self) -> Option<&V> {
        self.base.last()
    }

    /// Get the last element with mutable access.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// if let Some(entry) = map.last_mut() {
    ///     *entry = Entry(3, "c");
    /// }
    /// assert_eq!(map.last(), Some(&Entry(3, "c")));
    /// ```
    pub fn last_mut(&mut self) -> Option<&mut V> {
        self.base.last_mut()
    }
}

// Removal operations
impl<K, V> KeyedVecSet<K, V> {
    /// Removes the last element from the set and returns it, or [`None`] if it is empty.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(&'static str, i32);
    ///
    /// impl Keyed<&'static str> for Entry {
    ///     fn key(&self) -> &&'static str { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<&str, Entry>::new();
    /// map.insert(Entry("a", 1));
    /// map.insert(Entry("b", 2));
    /// assert_eq!(map.pop(), Some(Entry("b", 2)));
    /// assert_eq!(map.pop(), Some(Entry("a", 1)));
    /// assert!(map.is_empty());
    /// assert_eq!(map.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<V> {
        self.base.pop()
    }

    /// Removes and returns the element at position `index`, shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.insert(Entry(3, "c"));
    /// assert_eq!(map.remove_index(1), Entry(2, "b"));
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn remove_index(&mut self, index: usize) -> V {
        self.base.remove(index)
    }

    /// Removes an element from the set and returns it.
    ///
    /// The removed element is replaced by the last element of the set.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.insert(Entry(3, "c"));
    /// assert_eq!(map.swap_remove_index(1), Entry(2, "b"));
    /// assert_eq!(map.len(), 2);
    /// // Note: Entry(3, "c") moved to index 1
    /// ```
    pub fn swap_remove_index(&mut self, index: usize) -> V {
        self.base.swap_remove(index)
    }
}

impl<K, V> KeyedVecSet<K, V>
where
    V: Keyed<K>,
{
    /// Remove the element equivalent to `key` and return its value.
    ///
    /// Like `Vec::remove`, the element is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.insert(Entry(3, "c"));
    /// assert_eq!(map.remove(&2), Some(Entry(2, "b")));
    /// assert_eq!(map.remove(&2), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key).map(|index| self.remove_index(index))
    }

    /// Remove the element equivalent to `key` using `swap_remove`.
    ///
    /// Like `Vec::swap_remove`, the element is removed by swapping it with the last element of the
    /// set and popping it off. **This perturbs the position of what used to be the last element!**
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// map.insert(Entry(3, "c"));
    /// map.insert(Entry(4, "d"));
    /// assert_eq!(map.swap_remove(&2), Some(Entry(2, "b")));
    /// assert_eq!(map.swap_remove(&2), None);
    /// // Note: element order changed - Entry(4, "d") moved to index 1
    /// ```
    pub fn swap_remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| self.swap_remove_index(index))
    }
}

// Insertion operations (unconstrained version for VecMap::push)
impl<K, V> KeyedVecSet<K, V> {
    /// Push a value at the end of the set.
    pub(crate) fn push(&mut self, value: V) {
        self.base.push(value);
    }
}

// Insertion operations
impl<K, V> KeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Eq,
{
    /// Insert or replace an element (always appends new elements at the end).
    ///
    /// If an equivalent key already exists in the set: the key remains and retains in its place
    /// in the order, its corresponding value is updated with `value` and the older value is
    /// returned inside `Some(_)`.
    ///
    /// If no equivalent key existed in the set: the new key-value pair is inserted, last in
    /// order, and `None` is returned.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// assert_eq!(map.insert(Entry(37, "a")), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(Entry(37, "b"));
    /// assert_eq!(map.insert(Entry(37, "c")), Some(Entry(37, "b")));
    /// ```
    pub fn insert(&mut self, value: V) -> Option<V> {
        self.insert_full(value).1
    }

    /// Insert or replace an element (always appends new elements at the end).
    ///
    /// If an equivalent key already exists in the set: the key remains and retains in its place
    /// in the order, its corresponding value is updated with `value` and the older value is
    /// returned inside `(index, Some(_))`.
    ///
    /// If no equivalent key existed in the set: the new key-value pair is inserted, last in
    /// order, and `(index, None)` is returned.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(&'static str, i32);
    ///
    /// impl Keyed<&'static str> for Entry {
    ///     fn key(&self) -> &&'static str { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<&str, Entry>::new();
    /// assert_eq!(map.insert_full(Entry("a", 1)), (0, None));
    /// assert_eq!(map.insert_full(Entry("b", 2)), (1, None));
    /// assert_eq!(map.insert_full(Entry("b", 3)), (1, Some(Entry("b", 2))));
    /// ```
    pub fn insert_full(&mut self, value: V) -> (usize, Option<V>) {
        let key = value.key();
        if let Some(index) = self.get_index_of(key) {
            // Replace existing value
            let old = mem::replace(&mut self.base[index], value);
            (index, Some(old))
        } else {
            // Append new value (maintain insertion order)
            let index = self.base.len();
            self.base.push(value);
            (index, None)
        }
    }

    /// Insert a value at position `index` within the set, shifting all elements after it to the right.
    ///
    /// If an equivalent key already exists in the set: the key is removed from the old position and the new
    /// value is inserted at `index`. The old index and its value are returned inside `Some((usize, V))`.
    ///
    /// If no equivalent key existed in the set: the new value is inserted at position `index` and `None` is returned.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(&'static str, i32);
    ///
    /// impl Keyed<&'static str> for Entry {
    ///     fn key(&self) -> &&'static str { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<&str, Entry>::new();
    /// assert_eq!(map.insert_at(0, Entry("a", 1)), None);
    /// assert_eq!(map.insert_at(1, Entry("b", 2)), None);
    /// assert_eq!(map.insert_at(0, Entry("b", 3)), Some((1, Entry("b", 2))));
    /// ```
    pub fn insert_at(&mut self, index: usize, value: V) -> Option<(usize, V)> {
        let key = value.key();
        if let Some(old_index) = self.get_index_of(key) {
            let old_value = if old_index == index {
                mem::replace(&mut self.base[index], value)
            } else {
                let old_value = self.remove_index(old_index);
                self.base.insert(index, value);
                old_value
            };
            Some((old_index, old_value))
        } else {
            self.base.insert(index, value);
            None
        }
    }

    /// Moves all elements from `other` into `self`, leaving `other` empty.
    ///
    /// Elements from `other` that already exist in `self` are unchanged in their current position.
    /// All other elements are appended to `self` in the order they appear in `other`.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut a = KeyedVecSet::<i32, Entry>::new();
    /// a.insert(Entry(3, "c"));
    /// a.insert(Entry(2, "b"));
    /// a.insert(Entry(1, "a"));
    ///
    /// let mut b = KeyedVecSet::<i32, Entry>::new();
    /// b.insert(Entry(3, "d"));
    /// b.insert(Entry(4, "e"));
    /// b.insert(Entry(5, "f"));
    ///
    /// let old_capacity = b.capacity();
    ///
    /// a.append(&mut b);
    ///
    /// assert_eq!(a.len(), 5);
    /// assert_eq!(b.len(), 0);
    /// assert_eq!(b.capacity(), old_capacity);
    /// ```
    pub fn append(&mut self, other: &mut KeyedVecSet<K, V>) {
        self.reserve(other.len());
        for value in other.drain(..) {
            self.insert(value);
        }
    }
}

// Iterator adapters
impl<K, V> KeyedVecSet<K, V> {
    /// An iterator visiting all elements in insertion order. The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use vecmap::keyed::{KeyedVecSet, Keyed};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Entry(i32, &'static str);
    ///
    /// impl Keyed<i32> for Entry {
    ///     fn key(&self) -> &i32 { &self.0 }
    /// }
    ///
    /// let mut map = KeyedVecSet::<i32, Entry>::new();
    /// map.insert(Entry(1, "a"));
    /// map.insert(Entry(2, "b"));
    /// let mut iter = map.iter();
    /// assert_eq!(iter.next(), Some(&Entry(1, "a")));
    /// assert_eq!(iter.next(), Some(&Entry(2, "b")));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> slice::Iter<'_, V> {
        self.base.iter()
    }
}
