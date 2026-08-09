//! `SortedVecSet` is a vector-based set implementation which keeps its elements sorted.

mod impls;
mod iter;
#[cfg(feature = "serde")]
mod serde;

use super::{Entries, TryReserveError, sorted_keyed::SortedKeyedVecSet};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::ops::RangeBounds;

pub use self::iter::*;

/// A vector-based set implementation which keeps its elements sorted.
///
/// Internally it is represented as a `Vec<T>` kept sorted by `T`'s [`Ord`] implementation.
/// Iteration order matches the sort order.
///
/// # Complexity
///
/// | operation                                                     | cost             |
/// |---------------------------------------------------------------|------------------|
/// | `get` / `contains` / `binary_search`                          | *O*(log *n*)     |
/// | `insert` / `remove` / `pop_first`                             | *O*(*n*) (shift) |
/// | `pop_last`                                                    | *O*(1)           |
/// | `append`                                                      | *O*(*n* + *m*)   |
/// | `union` / `intersection` / `difference` / `is_subset` / ...   | *O*(*n* + *m*)   |
///
/// Lookups are faster than [`VecSet`](crate::VecSet)'s linear scan, but writes pay a shift cost
/// that [`BTreeSet`](alloc::collections::BTreeSet) avoids. Set operations are merge-based and run
/// in linear time.
#[derive(Clone, Debug)]
pub struct SortedVecSet<T> {
    base: SortedKeyedVecSet<T, T>,
}

impl<T> SortedVecSet<T> {
    /// Create a new set. (Does not allocate.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let mut set: SortedVecSet<&str> = SortedVecSet::new();
    /// ```
    pub const fn new() -> Self {
        SortedVecSet {
            base: SortedKeyedVecSet::new(),
        }
    }

    /// Create a new set with capacity for `capacity` elements. (Does not allocate if `capacity`
    /// is zero.)
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let mut set: SortedVecSet<&str> = SortedVecSet::with_capacity(10);
    /// assert_eq!(set.len(), 0);
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        SortedVecSet {
            base: SortedKeyedVecSet::with_capacity(capacity),
        }
    }

    /// Returns the number of elements the set can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.base.capacity()
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let mut a = SortedVecSet::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1);
    /// assert_eq!(a.len(), 1);
    /// ```
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

    /// Shortens the set, keeping the first `len` (smallest) elements and dropping the rest.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let mut set = SortedVecSet::from(["d", "a", "c", "b"]);
    /// set.truncate(2);
    /// assert_eq!(set, SortedVecSet::from(["a", "b"]));
    /// ```
    pub fn truncate(&mut self, len: usize) {
        self.base.truncate(len);
    }

    /// Reserves capacity for at least `additional` more elements.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    pub fn reserve(&mut self, additional: usize) {
        self.base.reserve(additional);
    }

    /// Reserves the minimum capacity for at least `additional` more elements.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.base.reserve_exact(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional` more elements.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve_exact(additional)
    }

    /// Retains only the elements specified by the predicate. The sort order is preserved.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let mut set: SortedVecSet<i32> = SortedVecSet::from([0, 1, 2, 3, 4, 5, 6, 7]);
    /// set.retain(|&e| e % 2 == 0);
    /// assert_eq!(set.len(), 4);
    /// ```
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.base.retain(f);
    }

    /// Shrinks the capacity of the set as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.base.shrink_to_fit();
    }

    /// Shrinks the capacity of the set with a lower limit.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.base.shrink_to(min_capacity);
    }

    /// Splits the set into two at the given index.
    ///
    /// Returns a newly allocated set containing the elements in the range `[at, len)`. Both
    /// halves remain sorted.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let mut set = SortedVecSet::from(["b", "a", "c"]);
    /// let set2 = set.split_off(1);
    /// assert_eq!(set, SortedVecSet::from(["a"]));
    /// assert_eq!(set2, SortedVecSet::from(["b", "c"]));
    /// ```
    pub fn split_off(&mut self, at: usize) -> SortedVecSet<T> {
        SortedVecSet {
            base: self.base.split_off(at),
        }
    }

    /// Search over the set for a value.
    ///
    /// Returns the position where that value is present, or the position where it can be
    /// inserted to maintain the sort. See [`slice::binary_search`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let set = SortedVecSet::from(["a", "b", "d"]);
    /// assert_eq!(set.binary_search(&"b"), Ok(1));
    /// assert_eq!(set.binary_search(&"c"), Err(2));
    /// ```
    pub fn binary_search(&self, value: &T) -> Result<usize, usize>
    where
        T: Ord,
    {
        self.binary_search_by(|v| v.cmp(value))
    }

    /// Search over the set with a comparator function.
    pub fn binary_search_by<'a, F>(&'a self, f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> Ordering,
    {
        self.as_slice().binary_search_by(f)
    }

    /// Search over the set with an extraction function.
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> B,
        B: Ord,
    {
        self.as_slice().binary_search_by_key(b, f)
    }

    /// Returns the index of the partition point of the set according to the given predicate.
    pub fn partition_point<P>(&self, pred: P) -> usize
    where
        P: FnMut(&T) -> bool,
    {
        self.as_slice().partition_point(pred)
    }

    /// Removes the specified range from the vector in bulk, returning all removed elements as an
    /// iterator.
    ///
    /// The range is interpreted in index space, not value space.
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T>
    where
        R: RangeBounds<usize>,
    {
        Drain::new(self, range)
    }

    /// An iterator visiting all elements in sort order. The iterator element type is `&'a T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let set = SortedVecSet::from(["b", "a", "c"]);
    ///
    /// for elem in set.iter() {
    ///     println!("elem: {elem}");
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self.as_entries())
    }

    /// Extracts a slice containing the set elements in sort order.
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let set = SortedVecSet::from(["b", "a", "c"]);
    /// let slice = set.as_slice();
    /// assert_eq!(slice, ["a", "b", "c"]);
    /// ```
    pub fn as_slice(&self) -> &[T] {
        self.base.as_slice()
    }

    /// Copies the set elements into a new `Vec<T>` in sort order.
    pub fn to_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.base.to_vec()
    }

    /// Takes ownership of the set and returns its elements as a `Vec<T>` in sort order.
    pub fn into_vec(self) -> Vec<T> {
        self.base.into_vec()
    }

    /// Takes ownership of the provided vector and converts it into `SortedVecSet`.
    ///
    /// # Safety
    ///
    /// The vector must be sorted strictly (no duplicates). One way to guarantee this is to sort
    /// the vector (e.g. by using [`[T]::sort`][slice-sort]) and then drop duplicate elements
    /// (e.g. by using [`Vec::dedup`]).
    ///
    /// [slice-sort]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort
    ///
    /// # Example
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let mut vec = vec!["b", "a", "c", "b"];
    /// vec.sort();
    /// vec.dedup();
    /// // SAFETY: we've just sorted and deduplicated the vector.
    /// let set = unsafe { SortedVecSet::from_vec_unchecked(vec) };
    ///
    /// assert_eq!(set, SortedVecSet::from(["a", "b", "c"]));
    /// ```
    pub unsafe fn from_vec_unchecked(vec: Vec<T>) -> Self {
        SortedVecSet {
            base: unsafe { SortedKeyedVecSet::from_vec_unchecked(vec) },
        }
    }
}

// Lookup operations.
impl<T> SortedVecSet<T> {
    /// Return `true` if an equivalent to `value` exists in the set.
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.contains_key(value)
    }

    /// Get the first (least) element in the set.
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let set = SortedVecSet::from_iter(["b", "a"]);
    /// assert_eq!(set.first(), Some(&"a"));
    /// ```
    pub fn first(&self) -> Option<&T> {
        self.base.first()
    }

    /// Get the last (greatest) element in the set.
    pub fn last(&self) -> Option<&T> {
        self.base.last()
    }

    /// Returns a reference to the value in the set, if any, that is equal to the given value.
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.get(value)
    }

    /// Return references to the element stored at `index`, if it is present, else `None`.
    pub fn get_index(&self, index: usize) -> Option<&T> {
        self.base.get_index(index)
    }

    /// Returns the index and a reference to the value in the set, if any, that is equal to the
    /// given value.
    pub fn get_full<Q>(&self, value: &Q) -> Option<(usize, &T)>
    where
        T: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.get_full(value)
    }

    /// Return item index, if it exists in the set.
    pub fn get_index_of<Q>(&self, value: &Q) -> Option<usize>
    where
        T: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.get_index_of(value)
    }
}

// Removal operations.
impl<T> SortedVecSet<T> {
    /// Removes the first (least) element from the set and returns it, or [`None`] if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let mut set = SortedVecSet::from_iter(["b", "a"]);
    /// assert_eq!(set.pop_first(), Some("a"));
    /// assert_eq!(set.pop_first(), Some("b"));
    /// assert_eq!(set.pop_first(), None);
    /// ```
    pub fn pop_first(&mut self) -> Option<T> {
        self.base.pop_first()
    }

    /// Removes the last (greatest) element from the set and returns it, or [`None`] if it is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let mut set = SortedVecSet::from_iter(["b", "a"]);
    /// assert_eq!(set.pop_last(), Some("b"));
    /// assert_eq!(set.pop_last(), Some("a"));
    /// assert_eq!(set.pop_last(), None);
    /// ```
    pub fn pop_last(&mut self) -> Option<T> {
        self.base.pop_last()
    }

    /// Remove the element equivalent to `value`.
    ///
    /// The element is removed by shifting all of the elements that follow it, preserving their
    /// relative order (and therefore the sort invariant).
    ///
    /// Returns `true` if `value` was found in the set.
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.remove(value).is_some()
    }

    /// Removes and returns the element at position `index`, shifting all elements after it to the
    /// left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    pub fn remove_index(&mut self, index: usize) -> T {
        self.base.remove_index(index)
    }

    /// Removes and returns the value in the set, if any, that is equal to the given one.
    pub fn take<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.base.remove(value)
    }
}

// Insertion operations.
impl<T> SortedVecSet<T>
where
    T: Ord,
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
    /// use vecmap::SortedVecSet;
    ///
    /// let mut set = SortedVecSet::new();
    ///
    /// assert_eq!(set.insert(2), true);
    /// assert_eq!(set.insert(2), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        self.base.insert(value).is_none()
    }

    /// Moves all values from `other` into `self`, leaving `other` empty.
    ///
    /// When a value exists in both sets, the one from `other` replaces the one in `self`
    /// (matching [`BTreeSet::append`](alloc::collections::BTreeSet::append) semantics).
    pub fn append(&mut self, other: &mut SortedVecSet<T>) {
        self.base.append(&mut other.base);
    }
}

// Range iterators.
impl<T> SortedVecSet<T>
where
    T: Ord,
{
    /// Constructs an iterator over a sub-range of elements in the set.
    ///
    /// The simplest way is to use the range syntax `min..max`. The range may also be specified as
    /// `(Bound<&T>, Bound<&T>)` for more control over which bounds are inclusive.
    ///
    /// # Panics
    ///
    /// Panics if the range's start is greater than its end.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    ///
    /// let set: SortedVecSet<_> = [3, 5, 8].into_iter().collect();
    /// let collected: Vec<_> = set.range(4..9).copied().collect();
    /// assert_eq!(collected, vec![5, 8]);
    /// ```
    pub fn range<Q, R>(&self, range: R) -> Range<'_, T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        let (start, end) = self.base.key_range_to_indices(range);
        Range::new(&self.base.as_slice()[start..end])
    }
}

// Set operations.
impl<T> SortedVecSet<T>
where
    T: Ord,
{
    /// Visits the values representing the difference, i.e., the values that are in `self` but not
    /// in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecSet;
    /// let a = SortedVecSet::from([1, 2, 3]);
    /// let b = SortedVecSet::from([4, 2, 3]);
    ///
    /// let diff: SortedVecSet<_> = a.difference(&b).copied().collect();
    /// assert_eq!(diff, SortedVecSet::from([1]));
    /// ```
    pub fn difference<'a>(&'a self, other: &'a SortedVecSet<T>) -> Difference<'a, T> {
        Difference::new(self, other)
    }

    /// Visits the values representing the intersection.
    ///
    /// Runs in *O*(*n* + *m*) by walking both sorted sides in parallel.
    pub fn intersection<'a>(&'a self, other: &'a SortedVecSet<T>) -> Intersection<'a, T> {
        Intersection::new(self, other)
    }

    /// Visits the values representing the symmetric difference.
    ///
    /// Runs in *O*(*n* + *m*) by walking both sorted sides in parallel.
    pub fn symmetric_difference<'a>(
        &'a self,
        other: &'a SortedVecSet<T>,
    ) -> SymmetricDifference<'a, T> {
        SymmetricDifference::new(self, other)
    }

    /// Visits the values representing the union, in sort order with no duplicates.
    ///
    /// Runs in *O*(*n* + *m*) by walking both sorted sides in parallel.
    pub fn union<'a>(&'a self, other: &'a SortedVecSet<T>) -> Union<'a, T> {
        Union::new(self, other)
    }

    /// Returns `true` if `self` has no elements in common with `other`.
    ///
    /// Runs in *O*(*n* + *m*) by walking both sorted sides in parallel.
    pub fn is_disjoint(&self, other: &SortedVecSet<T>) -> bool {
        let mut a = self.as_slice().iter();
        let mut b = other.as_slice().iter();
        let (mut x, mut y) = (a.next(), b.next());
        while let (Some(xv), Some(yv)) = (x, y) {
            match xv.cmp(yv) {
                Ordering::Less => x = a.next(),
                Ordering::Greater => y = b.next(),
                Ordering::Equal => return false,
            }
        }
        true
    }

    /// Returns `true` if the set is a subset of another.
    ///
    /// Runs in *O*(*n* + *m*) by walking both sorted sides in parallel.
    pub fn is_subset(&self, other: &SortedVecSet<T>) -> bool {
        if self.len() > other.len() {
            return false;
        }
        let mut a = self.as_slice().iter().peekable();
        let mut b = other.as_slice().iter();
        while let Some(xv) = a.peek() {
            match b.next() {
                None => return false,
                Some(yv) => match xv.cmp(&yv) {
                    Ordering::Less => return false,
                    Ordering::Equal => {
                        a.next();
                    }
                    Ordering::Greater => {}
                },
            }
        }
        true
    }

    /// Returns `true` if the set is a superset of another.
    ///
    /// Runs in *O*(*n* + *m*) by walking both sorted sides in parallel.
    pub fn is_superset(&self, other: &SortedVecSet<T>) -> bool {
        other.is_subset(self)
    }
}

impl<T> Entries for SortedVecSet<T> {
    type Entry = T;

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
