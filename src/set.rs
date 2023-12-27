//! `VecSet` is a vector-based set implementation which retains the order of inserted elements.

mod impls;
mod iter;
#[cfg(feature = "serde")]
mod serde;

use super::{Entries, Slot, VecMap};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::ops::RangeBounds;

pub use self::iter::*;

/// A vector-based set implementation which retains the order of inserted elements.
///
/// Internally it is represented as a `Vec<T>` to support keys that are neither `Hash` nor `Ord`.
#[derive(Clone, Debug)]
pub struct VecSet<T> {
    base: VecMap<T, ()>,
}

impl<T> VecSet<T> {
    /// Create a new set. (Does not allocate.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set: VecSet<&str> = VecSet::new();
    /// ```
    pub const fn new() -> Self {
        VecSet {
            base: VecMap::new(),
        }
    }

    /// Create a new set with capacity for `capacity` key-value pairs. (Does not allocate if
    /// `capacity` is zero.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set: VecSet<&str> = VecSet::with_capacity(10);
    /// assert_eq!(set.len(), 0);
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        VecSet {
            base: VecMap::with_capacity(capacity),
        }
    }

    /// Returns the number of elements the set can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set: VecSet<&str> = VecSet::with_capacity(10);
    /// assert_eq!(set.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.base.capacity()
    }

    /// Returns the number of elements in the set, also referred to as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut a = VecSet::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1);
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.base.len()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut a = VecSet::new();
    /// assert!(a.is_empty());
    /// a.insert(1);
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Clears the set, removing all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut a = VecSet::new();
    /// a.insert(1);
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
    /// Truncating a four element set to two elements:
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from(["a", "b", "c", "d"]);
    /// set.truncate(2);
    /// assert_eq!(set, VecSet::from(["a", "b"]));
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the set's current length:
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from(["a", "b", "c", "d"]);
    /// set.truncate(8);
    /// assert_eq!(set, VecSet::from(["a", "b", "c", "d"]));
    /// ```
    pub fn truncate(&mut self, len: usize) {
        self.base.truncate(len);
    }

    /// Reverses the order of entries in the set, in place.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from_iter(["a", "b", "c"]);
    /// set.reverse();
    /// assert_eq!(set, VecSet::from_iter(["c", "b", "a"]));
    /// ```
    pub fn reverse(&mut self) {
        self.base.reverse();
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the given
    /// `VecSet<T>`. The collection may reserve more space to speculatively avoid frequent
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
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from_iter(["a"]);
    /// set.reserve(10);
    /// assert!(set.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.base.reserve(additional);
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set: VecSet<i32> = VecSet::from([0, 1, 2, 3, 4, 5, 6, 7]);
    /// set.retain(|&e| e % 2 == 0);
    /// assert_eq!(set.len(), 4);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.base.retain(|k, _| f(k));
    }

    /// Shrinks the capacity of the set as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with the
    /// resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set: VecSet<i32> = VecSet::with_capacity(100);
    /// set.insert(1);
    /// set.insert(2);
    /// assert!(set.capacity() >= 100);
    /// set.shrink_to_fit();
    /// assert!(set.capacity() >= 2);
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
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set: VecSet<i32> = VecSet::with_capacity(100);
    /// set.insert(1);
    /// set.insert(2);
    /// assert!(set.capacity() >= 100);
    /// set.shrink_to(10);
    /// assert!(set.capacity() >= 10);
    /// set.shrink_to(0);
    /// assert!(set.capacity() >= 2);
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
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from(["a", "b", "c"]);
    /// let set2 = set.split_off(1);
    /// assert_eq!(set, VecSet::from(["a"]));
    /// assert_eq!(set2, VecSet::from(["b", "c"]));
    /// ```
    pub fn split_off(&mut self, at: usize) -> VecSet<T> {
        VecSet {
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
    /// use vecmap::VecSet;
    ///
    /// let mut v = VecSet::from([1, 2, 3]);
    /// let u: VecSet<_> = v.drain(1..).collect();
    /// assert_eq!(v, VecSet::from([1]));
    /// assert_eq!(u, VecSet::from([2, 3]));
    ///
    /// // A full range clears the vector, like `clear()` does
    /// v.drain(..);
    /// assert_eq!(v, VecSet::new());
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T>
    where
        R: RangeBounds<usize>,
    {
        Drain::new(self, range)
    }

    /// An iterator visiting all elements in insertion order. The iterator element type is
    /// `&'a T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let set = VecSet::from(["a", "b", "c"]);
    ///
    /// for elem in set.iter() {
    ///     println!("elem: {elem}");
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self.as_entries())
    }

    /// Sorts the set.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*))
    /// worst-case.
    ///
    /// When applicable, unstable sorting is preferred because it is generally faster than stable
    /// sorting and it doesn't allocate auxiliary memory. See
    /// [`sort_unstable`](VecSet::sort_unstable).
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from(["b", "a", "c"]);
    ///
    /// set.sort();
    /// let vec: Vec<_> = set.into_iter().collect();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// ```
    pub fn sort(&mut self)
    where
        T: Ord,
    {
        self.base.sort_keys();
    }

    /// Sorts the set.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place (i.e., does not
    /// allocate), and *O*(*n* \* log(*n*)) worst-case.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from(["b", "a", "c"]);
    ///
    /// set.sort_unstable();
    /// let vec: Vec<_> = set.into_iter().collect();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// ```
    pub fn sort_unstable(&mut self)
    where
        T: Ord,
    {
        self.base.sort_unstable_keys();
    }

    /// Sorts the set with a comparator function.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*))
    /// worst-case.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from(["b", "a", "c"]);
    ///
    /// set.sort_by(|a, b| b.cmp(&a));
    /// let vec: Vec<_> = set.into_iter().collect();
    /// assert_eq!(vec, ["c", "b", "a"]);
    /// ```
    pub fn sort_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&T, &T) -> Ordering,
    {
        self.base.sort_by(|a, b| compare(a.0, b.0));
    }

    /// Sorts the set with a comparator function.
    ///
    /// This sort is unstable (i.e., may reorder equal elements), in-place (i.e., does not
    /// allocate), and *O*(*n* \* log(*n*)) worst-case.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from(["b", "a", "c"]);
    ///
    /// set.sort_unstable_by(|a, b| b.cmp(&a));
    /// let vec: Vec<_> = set.into_iter().collect();
    /// assert_eq!(vec, ["c", "b", "a"]);
    /// ```
    pub fn sort_unstable_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&T, &T) -> Ordering,
    {
        self.base.sort_unstable_by(|a, b| compare(a.0, b.0));
    }

    /// Extracts a slice containing the set elements.
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let set = VecSet::from(["b", "a", "c"]);
    /// let slice = set.as_slice();
    /// assert_eq!(slice, ["b", "a", "c"]);
    /// ```
    pub fn as_slice(&self) -> &[T] {
        // SAFETY: `&[(T, ())]` and `&[T]` have the same memory layout.
        unsafe { &*(self.base.as_slice() as *const [(T, ())] as *const [T]) }
    }

    /// Copies the set elements into a new `Vec<T>`.
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let set = VecSet::from(["b", "a", "c"]);
    /// let vec = set.to_vec();
    /// assert_eq!(vec, ["b", "a", "c"]);
    /// // Here, `set` and `vec` can be modified independently.
    /// ```
    pub fn to_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.iter().cloned().collect()
    }

    /// Takes ownership of the set and returns its elements as a `Vec<T>`.
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let set = VecSet::from(["b", "a", "c"]);
    /// let vec = set.into_vec();
    /// assert_eq!(vec, ["b", "a", "c"]);
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        // SAFETY: `Vec<Slot<T, ()>>` and `Vec<T>` have the same memory layout.
        unsafe { super::transmute_vec(self.base.base) }
    }

    /// Takes ownership of provided vector and converts it into `VecSet`.
    ///
    /// # Safety
    ///
    /// The vector must have no duplicate elements. One way to guarantee it is to sort the vector
    /// (e.g. by using [`[T]::sort`][slice-sort]) and then drop duplicate elements (e.g. by using
    /// [`Vec::dedup`]).
    ///
    /// # Example
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut vec = vec!["b", "a", "c", "b"];
    /// vec.sort();
    /// vec.dedup();
    /// // SAFETY: We've just deduplicated the vector.
    /// let set = unsafe { VecSet::from_vec_unchecked(vec) };
    ///
    /// assert_eq!(set, VecSet::from(["b", "a", "c"]));
    /// ```
    ///
    /// [slice-sort]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort
    pub unsafe fn from_vec_unchecked(vec: Vec<T>) -> Self {
        // SAFETY: `Vec<T>` and `Vec<Slot<T, ()>>` have the same memory layout.
        let base = unsafe { super::transmute_vec(vec) };
        VecSet {
            base: VecMap { base },
        }
    }
}

// Lookup operations.
impl<T> VecSet<T> {
    /// Return `true` if an equivalent to `key` exists in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// set.insert(1);
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&2), false);
    /// ```
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.base.contains_key(value)
    }

    /// Get the first element.
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from_iter(["a", "b"]);
    /// assert_eq!(set.first(), Some(&"a"));
    /// ```
    pub fn first(&self) -> Option<&T> {
        self.base.first().map(|(k, _)| k)
    }

    /// Get the last element.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from_iter(["a", "b"]);
    /// assert_eq!(set.last(), Some(&"b"));
    /// set.pop();
    /// set.pop();
    /// assert_eq!(set.last(), None);
    /// ```
    pub fn last(&self) -> Option<&T> {
        self.base.last().map(|(k, _)| k)
    }

    /// Returns a reference to the value in the set, if any, that is equal to the given value.
    ///
    /// The value may be any borrowed form of the set's value type, but [`Eq`] on the borrowed form
    /// *must* match those for the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let set = VecSet::from([1, 2, 3]);
    /// assert_eq!(set.get(&2), Some(&2));
    /// assert_eq!(set.get(&4), None);
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        self.base.get_key_value(value).map(|(k, _)| k)
    }

    /// Return references to the element stored at `index`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// set.insert(1);
    /// assert_eq!(set.get_index(0), Some(&1));
    /// assert_eq!(set.get_index(1), None);
    /// ```
    pub fn get_index(&self, index: usize) -> Option<&T> {
        self.base.get_index(index).map(|(k, _)| k)
    }

    /// Returns the index and a reference to the value in the set, if any, that is equal to the
    /// given value.
    ///
    /// The value may be any borrowed form of the set's value type, but [`Eq`] on the borrowed form
    /// *must* match those for the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let set = VecSet::from([1, 2, 3]);
    /// assert_eq!(set.get_full(&2), Some((1, &2)));
    /// assert_eq!(set.get_full(&4), None);
    /// ```
    pub fn get_full<Q>(&self, value: &Q) -> Option<(usize, &T)>
    where
        T: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        self.base.get_full(value).map(|(index, k, _)| (index, k))
    }

    /// Return item index, if it exists in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// set.insert("a");
    /// set.insert("b");
    /// assert_eq!(set.get_index_of("a"), Some(0));
    /// assert_eq!(set.get_index_of("b"), Some(1));
    /// assert_eq!(set.get_index_of("c"), None);
    /// ```
    pub fn get_index_of<Q>(&self, value: &Q) -> Option<usize>
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.base.get_index_of(value)
    }
}

// Removal operations.
impl<T> VecSet<T> {
    /// Removes the last element from the set and returns it, or [`None`] if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from_iter(["a", "b"]);
    /// assert_eq!(set.pop(), Some("b"));
    /// assert_eq!(set.pop(), Some("a"));
    /// assert!(set.is_empty());
    /// assert_eq!(set.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.base.pop().map(|(k, ())| k)
    }

    /// Remove the element equivalent to `value`.
    ///
    /// Like `Vec::remove`, the element is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// Returns `true` if `value` was found in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from_iter([1, 2, 3, 4]);
    /// assert_eq!(set.remove(&2), true);
    /// assert_eq!(set.remove(&2), false);
    /// assert_eq!(set, VecSet::from_iter([1, 3, 4]));
    /// ```
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.base.remove(value).is_some()
    }

    /// Removes and returns the element at position `index` within the set, shifting all elements
    /// after it to the left.
    ///
    /// If you don't need the order of elements to be preserved, use [`swap_remove`] instead.
    ///
    /// [`swap_remove`]: VecSet::swap_remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut v = VecSet::from(["a", "b", "c"]);
    /// assert_eq!(v.remove_index(1), "b");
    /// assert_eq!(v, VecSet::from(["a", "c"]));
    /// ```
    pub fn remove_index(&mut self, index: usize) -> T {
        self.base.remove_index(index).0
    }

    /// Remove the element equivalent to `value`.
    ///
    /// Like `Vec::swap_remove`, the element is removed by swapping it with the last element of the
    /// map and popping it off. **This perturbs the position of what used to be the last element!**
    ///
    /// Returns `true` if `value` was found in the set.
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from_iter([1, 2, 3, 4]);
    /// assert_eq!(set.swap_remove(&2), true);
    /// assert_eq!(set.swap_remove(&2), false);
    /// assert_eq!(set, VecSet::from_iter([1, 4, 3]));
    /// ```
    pub fn swap_remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.base.swap_remove(value).is_some()
    }

    /// Removes an element from the set and returns it.
    ///
    /// The removed element is replaced by the last element of the set.
    ///
    /// If you need to preserve the element order, use [`remove`] instead.
    ///
    /// [`remove`]: VecSet::remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut v = VecSet::from(["foo", "bar", "baz", "qux"]);
    ///
    /// assert_eq!(v.swap_remove_index(0), "foo");
    /// assert_eq!(v, VecSet::from(["qux", "bar", "baz"]));
    ///
    /// assert_eq!(v.swap_remove_index(0), "qux");
    /// assert_eq!(v, VecSet::from(["baz", "bar"]));
    /// ```
    pub fn swap_remove_index(&mut self, index: usize) -> T {
        self.base.swap_remove_index(index).0
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
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from(["a", "b", "c", "d"]);
    /// set.swap_indices(1, 3);
    /// assert_eq!(set.to_vec(), ["a", "d", "c", "b"]);
    /// ```
    pub fn swap_indices(&mut self, a: usize, b: usize) {
        self.base.swap_indices(a, b);
    }

    /// Removes and returns the value in the set, if any, that is equal to the given one.
    ///
    /// The value may be any borrowed form of the set's value type, but [`Eq`] on the borrowed form
    /// *must* match those for the value type.
    ///
    /// Like `Vec::remove`, the element is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from([1, 2, 3]);
    /// assert_eq!(set.take(&2), Some(2));
    /// assert_eq!(set.take(&2), None);
    /// ```
    pub fn take<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        self.base.remove_entry(value).map(|(k, ())| k)
    }

    /// Removes and returns the value in the set, if any, that is equal to the given one.
    ///
    /// The value may be any borrowed form of the set's value type, but [`Eq`] on the borrowed form
    /// *must* match those for the value type.
    ///
    /// Like `Vec::swap_remove`, the element is removed by swapping it with the last element of the
    /// map and popping it off. **This perturbs the position of what used to be the last element!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from([1, 2, 3]);
    /// assert_eq!(set.take(&2), Some(2));
    /// assert_eq!(set.take(&2), None);
    /// ```
    pub fn swap_take<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        self.base.swap_remove_entry(value).map(|(k, ())| k)
    }
}

// Insertion operations.
impl<T> VecSet<T>
where
    T: Eq,
{
    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    ///
    /// - If the set did not previously contain this value, `true` is returned.
    /// - If the set already contained this value, `false` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::new();
    ///
    /// assert_eq!(set.insert(2), true);
    /// assert_eq!(set.insert(2), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        self.base.insert(value, ()).is_none()
    }
}

// Set operations.
impl<T> VecSet<T>
where
    T: Eq,
{
    /// Visits the values representing the difference, i.e., the values that are in `self` but not
    /// in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    /// let a = VecSet::from([1, 2, 3]);
    /// let b = VecSet::from([4, 2, 3, 4]);
    ///
    /// // Can be seen as `a - b`.
    /// for x in a.difference(&b) {
    ///     println!("{x}"); // Print 1
    /// }
    ///
    /// let diff: VecSet<_> = a.difference(&b).collect();
    /// assert_eq!(diff, [1].iter().collect());
    ///
    /// // Note that difference is not symmetric,
    /// // and `b - a` means something else:
    /// let diff: VecSet<_> = b.difference(&a).collect();
    /// assert_eq!(diff, [4].iter().collect());
    /// ```
    pub fn difference<'a>(&'a self, other: &'a VecSet<T>) -> Difference<'a, T> {
        Difference::new(self, other)
    }

    /// Visits the values representing the intersection, i.e., the values that are both in `self`
    /// and `other`.
    ///
    /// When an equal element is present in `self` and `other` then the resulting `Intersection`
    /// may yield references to one or the other. This can be relevant if `T` contains fields which
    /// are not compared by its `Eq` implementation, and may hold different value between the two
    /// equal copies of `T` in the two sets.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    /// let a = VecSet::from([1, 2, 3]);
    /// let b = VecSet::from([4, 2, 3, 4]);
    ///
    /// // Print 2, 3 in arbitrary order.
    /// for x in a.intersection(&b) {
    ///     println!("{x}");
    /// }
    ///
    /// let intersection: VecSet<_> = a.intersection(&b).collect();
    /// assert_eq!(intersection, [2, 3].iter().collect());
    /// ```
    pub fn intersection<'a>(&'a self, other: &'a VecSet<T>) -> Intersection<'a, T> {
        if self.len() <= other.len() {
            Intersection::new(self, other)
        } else {
            Intersection::new(other, self)
        }
    }

    /// Visits the values representing the symmetric difference, i.e., the values that are in
    /// `self` or in `other` but not in both.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    /// let a = VecSet::from([1, 2, 3]);
    /// let b = VecSet::from([4, 2, 3, 4]);
    ///
    /// // Print 1, 4 in arbitrary order.
    /// for x in a.symmetric_difference(&b) {
    ///     println!("{x}");
    /// }
    ///
    /// let diff1: VecSet<_> = a.symmetric_difference(&b).collect();
    /// let diff2: VecSet<_> = b.symmetric_difference(&a).collect();
    ///
    /// assert_eq!(diff1, diff2);
    /// assert_eq!(diff1, [1, 4].iter().collect());
    /// ```
    pub fn symmetric_difference<'a>(&'a self, other: &'a VecSet<T>) -> SymmetricDifference<'a, T> {
        SymmetricDifference::new(self, other)
    }

    /// Visits the values representing the union, i.e., all the values in `self` or `other`,
    /// without duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    /// let a = VecSet::from([1, 2, 3]);
    /// let b = VecSet::from([4, 2, 3, 4]);
    ///
    /// // Print 1, 2, 3, 4 in arbitrary order.
    /// for x in a.union(&b) {
    ///     println!("{x}");
    /// }
    ///
    /// let union: VecSet<_> = a.union(&b).collect();
    /// assert_eq!(union, [1, 2, 3, 4].iter().collect());
    /// ```
    pub fn union<'a>(&'a self, other: &'a VecSet<T>) -> Union<'a, T> {
        if self.len() >= other.len() {
            Union::new(self, other)
        } else {
            Union::new(other, self)
        }
    }

    /// Returns `true` if `self` has no elements in common with `other`. This is equivalent to
    /// checking for an empty intersection.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let a = VecSet::from([1, 2, 3]);
    /// let mut b = VecSet::new();
    ///
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(4);
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(1);
    /// assert_eq!(a.is_disjoint(&b), false);
    /// ```
    pub fn is_disjoint(&self, other: &VecSet<T>) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| !other.contains(v))
        } else {
            other.iter().all(|v| !self.contains(v))
        }
    }

    /// Returns `true` if the set is a subset of another, i.e., `other` contains at least all the
    /// values in `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let sup = VecSet::from([1, 2, 3]);
    /// let mut set = VecSet::new();
    ///
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(2);
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(4);
    /// assert_eq!(set.is_subset(&sup), false);
    /// ```
    pub fn is_subset(&self, other: &VecSet<T>) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| other.contains(v))
        } else {
            false
        }
    }

    /// Returns `true` if the set is a superset of another, i.e., `self` contains at least all the
    /// values in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let sub = VecSet::from([1, 2]);
    /// let mut set = VecSet::new();
    ///
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(0);
    /// set.insert(1);
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(2);
    /// assert_eq!(set.is_superset(&sub), true);
    /// ```
    pub fn is_superset(&self, other: &VecSet<T>) -> bool {
        other.is_subset(self)
    }
}

impl<T> Entries for VecSet<T> {
    type Entry = Slot<T, ()>;

    fn as_entries(&self) -> &[Self::Entry] {
        self.base.as_entries()
    }

    fn as_entries_mut(&mut self) -> &mut [Self::Entry] {
        self.base.as_entries_mut()
    }

    fn into_entries(self) -> Vec<Self::Entry> {
        self.base.into_entries()
    }
}
