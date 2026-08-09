//! Internal backing type for `SortedVecMap` and `SortedVecSet`.
//!
//! This module provides `SortedKeyedVecSet<K, V>`, a generic ordered collection that keeps its
//! elements sorted by key and uses binary search for lookups. It reuses the [`Keyed`] trait from
//! [`crate::keyed`].

mod impls;

use crate::TryReserveError;
use crate::keyed::Keyed;
use alloc::vec::{self, Vec};
use core::borrow::Borrow;
use core::mem;
use core::ops::{Bound, RangeBounds};

/// A vector-based collection which keeps its elements sorted by key.
///
/// Internally it is represented as a `Vec<V>` whose elements are always kept sorted by the key
/// extracted via [`Keyed::key`]. This design allows any data type to be used as an element of
/// `SortedKeyedVecSet`, as long as it contains data that can be considered as a key and that key
/// is [`Ord`].
///
/// When `V = T` (where `T: Keyed<T>`), `SortedKeyedVecSet<T, T>` is equivalent to
/// [`SortedVecSet<T>`](crate::SortedVecSet).
/// When `V = Slot<K, MV>`, `SortedKeyedVecSet<K, Slot<K, MV>>` is equivalent to
/// [`SortedVecMap<K, MV>`](crate::SortedVecMap).
#[derive(Clone, Debug)]
pub(crate) struct SortedKeyedVecSet<K, V> {
    base: Vec<V>,
    _marker: core::marker::PhantomData<K>,
}

impl<K, V> SortedKeyedVecSet<K, V> {
    /// Create a new set. (Does not allocate.)
    pub const fn new() -> Self {
        SortedKeyedVecSet {
            base: Vec::new(),
            _marker: core::marker::PhantomData,
        }
    }

    /// Create a new set with capacity for `capacity` elements. (Does not allocate if `capacity`
    /// is zero.)
    pub fn with_capacity(capacity: usize) -> Self {
        SortedKeyedVecSet {
            base: Vec::with_capacity(capacity),
            _marker: core::marker::PhantomData,
        }
    }

    /// Returns the number of elements the set can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.base.capacity()
    }

    /// Returns the number of elements in the set.
    pub fn len(&self) -> usize {
        self.base.len()
    }

    /// Returns `true` if the set contains no elements.
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Clears the set, removing all elements.
    pub fn clear(&mut self) {
        self.base.clear();
    }

    /// Shortens the set, keeping the first `len` elements and dropping the rest.
    ///
    /// If `len` is greater than the set's current length, this has no effect.
    pub fn truncate(&mut self, len: usize) {
        self.base.truncate(len);
    }

    /// Reserves capacity for at least `additional` more elements to be inserted.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    pub fn reserve(&mut self, additional: usize) {
        self.base.reserve(additional);
    }

    /// Reserves the minimum capacity for at least `additional` more elements to be inserted.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.base.reserve_exact(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional` more elements to be
    /// inserted.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of the set as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.base.shrink_to_fit();
    }

    /// Shrinks the capacity of the set with a lower limit.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
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
    pub fn split_off(&mut self, at: usize) -> SortedKeyedVecSet<K, V> {
        SortedKeyedVecSet {
            base: self.base.split_off(at),
            _marker: core::marker::PhantomData,
        }
    }

    /// Removes the specified range from the vector in bulk, returning all removed elements as an
    /// iterator.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if the end point is greater
    /// than the length of the vector.
    pub fn drain<R>(&mut self, range: R) -> vec::Drain<'_, V>
    where
        R: RangeBounds<usize>,
    {
        self.base.drain(range)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// Because the predicate cannot observe keys separately from values it cannot invalidate the
    /// sort invariant.
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&V) -> bool,
    {
        self.base.retain(f);
    }

    /// Retains only the elements specified by the predicate, with mutable access.
    ///
    /// # Safety considerations
    ///
    /// The caller must not mutate the key portion of the element in a way that would invalidate
    /// the sort order. In practice this method is only exposed to callers that hand out
    /// `&mut value` (not `&mut key`).
    pub fn retain_mut<F>(&mut self, f: F)
    where
        F: FnMut(&mut V) -> bool,
    {
        self.base.retain_mut(f);
    }

    /// Extracts a slice containing the set elements.
    pub fn as_slice(&self) -> &[V] {
        self.base.as_slice()
    }

    /// Extracts a mutable slice containing the set elements.
    ///
    /// The caller must not mutate the key portion of any element in a way that would invalidate
    /// the sort order.
    pub fn as_mut_slice(&mut self) -> &mut [V] {
        self.base.as_mut_slice()
    }

    /// Copies the set elements into a new `Vec<V>`.
    pub fn to_vec(&self) -> Vec<V>
    where
        V: Clone,
    {
        self.base.clone()
    }

    /// Takes ownership of the set and returns its elements as a `Vec<V>`.
    pub fn into_vec(self) -> Vec<V> {
        self.base
    }

    /// Takes ownership of the provided vector and converts it into `SortedKeyedVecSet`.
    ///
    /// # Safety
    ///
    /// The vector must be sorted strictly by key (no duplicate keys). One way to guarantee this
    /// is to sort the vector (e.g. by using [`[T]::sort_by`][slice-sort-by]) and then drop
    /// duplicate keys (e.g. by using [`Vec::dedup_by`]).
    ///
    /// [slice-sort-by]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by
    pub unsafe fn from_vec_unchecked(base: Vec<V>) -> Self {
        SortedKeyedVecSet {
            base,
            _marker: core::marker::PhantomData,
        }
    }
}

// Lookup operations
impl<K, V> SortedKeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Ord,
{
    /// Returns the position of the element with the given key, or the position where it could be
    /// inserted while maintaining the sort order.
    pub fn binary_search_key<Q>(&self, key: &Q) -> Result<usize, usize>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base
            .binary_search_by(|elem| elem.key().borrow().cmp(key))
    }

    /// Return item index, if it exists in the set.
    ///
    /// Performs a binary search O(log n) over the elements to find the matching key.
    pub fn get_index_of<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.binary_search_key(key).ok()
    }

    /// Returns `true` if the set contains an element with the given key.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.binary_search_key(key).is_ok()
    }

    /// Return a reference to the value stored for `key`, if it is present.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.get_index_of(key).map(|index| &self.base[index])
    }

    /// Return item index and a reference to the value stored for `key`, if it is present.
    pub fn get_full<Q>(&self, key: &Q) -> Option<(usize, &V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.get_index_of(key)
            .map(|index| (index, &self.base[index]))
    }

    /// Return a mutable reference to the value stored for `key`, if it is present.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.get_index_of(key).map(|index| &mut self.base[index])
    }
}

impl<K, V> SortedKeyedVecSet<K, V> {
    /// Return a reference to the value stored at `index`, if it is present.
    pub fn get_index(&self, index: usize) -> Option<&V> {
        self.base.get(index)
    }

    /// Return a mutable reference to the value stored at `index`, if it is present.
    pub fn get_index_mut(&mut self, index: usize) -> Option<&mut V> {
        self.base.get_mut(index)
    }

    /// Get the first element.
    pub fn first(&self) -> Option<&V> {
        self.base.first()
    }

    /// Get a mutable reference to the first element.
    ///
    /// The caller must not mutate the key portion of the element in a way that would invalidate
    /// the sort order.
    pub fn first_mut(&mut self) -> Option<&mut V> {
        self.base.first_mut()
    }

    /// Get the last element.
    pub fn last(&self) -> Option<&V> {
        self.base.last()
    }

    /// Get a mutable reference to the last element.
    ///
    /// The caller must not mutate the key portion of the element in a way that would invalidate
    /// the sort order.
    pub fn last_mut(&mut self) -> Option<&mut V> {
        self.base.last_mut()
    }
}

// Unchecked insertion (used by VacantEntry).
impl<K, V> SortedKeyedVecSet<K, V> {
    /// Insert `value` at `index`, shifting subsequent elements to the right.
    ///
    /// # Safety
    ///
    /// The caller must ensure that inserting at `index` preserves the sort invariant:
    /// `index <= len`, no existing element has the same key, and the inserted key sorts between
    /// its neighbours.
    pub unsafe fn insert_at_unchecked(&mut self, index: usize, value: V) {
        self.base.insert(index, value);
    }
}

// Removal operations
impl<K, V> SortedKeyedVecSet<K, V> {
    /// Removes the last (greatest-keyed) element from the set and returns it, or [`None`] if it
    /// is empty.
    pub fn pop_last(&mut self) -> Option<V> {
        self.base.pop()
    }

    /// Removes the first (least-keyed) element from the set and returns it, or [`None`] if it is
    /// empty.
    pub fn pop_first(&mut self) -> Option<V> {
        if self.base.is_empty() {
            None
        } else {
            Some(self.base.remove(0))
        }
    }

    /// Removes and returns the element at position `index`, shifting all elements after it to
    /// the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    pub fn remove_index(&mut self, index: usize) -> V {
        self.base.remove(index)
    }
}

impl<K, V> SortedKeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Ord,
{
    /// Remove the element equivalent to `key` and return its value.
    ///
    /// The pair is removed by shifting all of the elements that follow it, preserving their
    /// relative order (and therefore the sort invariant).
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.get_index_of(key).map(|index| self.remove_index(index))
    }
}

// Insertion operations
impl<K, V> SortedKeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Ord,
{
    /// Insert or replace an element, keeping the set sorted.
    ///
    /// If an equivalent key already exists: the key retains its position, its value is replaced
    /// with `value`, and the old value is returned inside `Some(_)`.
    ///
    /// If no equivalent key existed: the value is inserted in its sorted position, and `None` is
    /// returned.
    pub fn insert(&mut self, value: V) -> Option<V> {
        self.insert_full(value).1
    }

    /// Insert or replace an element, returning its index.
    ///
    /// See [`Self::insert`] for semantics.
    pub fn insert_full(&mut self, value: V) -> (usize, Option<V>) {
        match self.binary_search_key(value.key()) {
            Ok(index) => {
                let old = mem::replace(&mut self.base[index], value);
                (index, Some(old))
            }
            Err(index) => {
                self.base.insert(index, value);
                (index, None)
            }
        }
    }

    /// Moves all elements from `other` into `self`, leaving `other` empty.
    ///
    /// If both sets contain an equivalent key, the value from `other` replaces the one in `self`
    /// (matching `BTreeMap::append` semantics).
    ///
    /// Runs in *O*(*n* + *m*) by walking both sorted sides in parallel and building a fresh vector
    /// with the merged contents.
    pub fn append(&mut self, other: &mut SortedKeyedVecSet<K, V>) {
        if other.is_empty() {
            return;
        }
        if self.is_empty() {
            mem::swap(&mut self.base, &mut other.base);
            return;
        }

        let mut self_iter = mem::take(&mut self.base).into_iter();
        let mut other_iter = mem::take(&mut other.base).into_iter();
        let total = self_iter.len() + other_iter.len();
        let mut merged = Vec::with_capacity(total);

        let mut left = self_iter.next();
        let mut right = other_iter.next();
        loop {
            match (left.take(), right.take()) {
                (Some(l), Some(r)) => match l.key().cmp(r.key()) {
                    core::cmp::Ordering::Less => {
                        merged.push(l);
                        left = self_iter.next();
                        right = Some(r);
                    }
                    core::cmp::Ordering::Greater => {
                        merged.push(r);
                        left = Some(l);
                        right = other_iter.next();
                    }
                    core::cmp::Ordering::Equal => {
                        // Equal keys: `other` wins.
                        merged.push(r);
                        left = self_iter.next();
                        right = other_iter.next();
                    }
                },
                (Some(l), None) => {
                    merged.push(l);
                    merged.extend(self_iter);
                    break;
                }
                (None, Some(r)) => {
                    merged.push(r);
                    merged.extend(other_iter);
                    break;
                }
                (None, None) => break,
            }
        }

        self.base = merged;
    }
}

// Range helpers
impl<K, V> SortedKeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Ord,
{
    /// Translate a key-bounded range into an index range over the backing slice.
    pub(crate) fn key_range_to_indices<Q, R>(&self, range: R) -> (usize, usize)
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        let slice = self.base.as_slice();
        let start = match range.start_bound() {
            Bound::Unbounded => 0,
            Bound::Included(key) => slice.partition_point(|elem| elem.key().borrow() < key),
            Bound::Excluded(key) => slice.partition_point(|elem| elem.key().borrow() <= key),
        };
        let end = match range.end_bound() {
            Bound::Unbounded => slice.len(),
            Bound::Included(key) => slice.partition_point(|elem| elem.key().borrow() <= key),
            Bound::Excluded(key) => slice.partition_point(|elem| elem.key().borrow() < key),
        };
        assert!(start <= end, "range start is greater than range end");
        (start, end)
    }
}
