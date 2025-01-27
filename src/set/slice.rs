use super::{Iter, Slot};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::ops::Index;
use core::ptr;

/// A dynamically-sized slice of keys in a [`VecSet`][crate::VecSet].
///
/// This supports indexed operations much like a `[T]` slice.
#[repr(transparent)]
pub struct Slice<T> {
    entries: [Slot<T>],
}

impl<T> Slice<T> {
    pub(super) const fn from_slice(entries: &[Slot<T>]) -> &Self {
        // SAFETY: `&[Slot<T>]` and `&Slice<T>` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<T>]>(entries) as *const Self) }
    }

    pub(super) const fn from_mut_slice(entries: &mut [Slot<T>]) -> &mut Slice<T> {
        // SAFETY: `&mut [Slot<T>]` and `&mut Slice<T>` have the same memory layout.
        unsafe { &mut *(ptr::from_mut::<[Slot<T>]>(entries) as *mut Slice<T>) }
    }

    /// Extracts a slice containing the set elements.
    ///
    /// This method provides access to the raw backing [`&[T]`][core::slice] of the `Slice<T>`.
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let set = VecSet::from(["b", "a", "c"]);
    /// let slice = set.as_std_slice();
    /// assert_eq!(slice, ["b", "a", "c"]);
    /// ```
    pub const fn as_std_slice(&self) -> &[T] {
        // SAFETY: `&[Slot<T>]` and `&[T]` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<T>]>(&self.entries) as *const [T]) }
    }

    /// Returns an empty slice.
    ///
    /// ```
    /// use vecmap::set::{Slice, VecSet};
    ///
    /// let set: VecSet<u32> = VecSet::new();
    /// let slice: &Slice<u32> = Slice::new();
    /// assert!(slice.is_empty());
    /// assert_eq!(slice, set.as_slice());
    /// ```
    pub const fn new<'a>() -> &'a Self {
        Slice::from_slice(&[])
    }

    /// Returns an empty mutable slice.
    ///
    /// ```
    /// use vecmap::set::{Slice, VecSet};
    ///
    /// let mut set: VecSet<u32> = VecSet::new();
    /// let slice: &mut Slice<u32> = Slice::new_mut();
    /// assert!(slice.is_empty());
    /// assert_eq!(slice, set.as_mut_slice());
    /// ```
    pub const fn new_mut<'a>() -> &'a mut Self {
        Slice::from_mut_slice(&mut [])
    }

    /// Returns the number of entries in the slice, also referred to as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// set.insert(1);
    /// let slice = set.as_slice();
    /// assert_eq!(slice.len(), 1);
    /// ```
    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if the slice contains no entries.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::new();
    /// let slice = set.as_slice();
    /// assert!(slice.is_empty());
    ///
    /// set.insert(1);
    ///
    /// let slice = set.as_slice();
    /// assert!(!slice.is_empty());
    /// ```
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
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
}

// Iterator adapters.
impl<T> Slice<T> {
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
        Iter::new(&self.entries)
    }
}

// Lookup operations.
impl<T> Slice<T> {
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
        self.get_index_of(value).is_some()
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
        self.entries.first().map(Slot::key)
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
        self.entries.last().map(Slot::key)
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
        self.get_index_of(value)
            .map(|index| self.entries[index].key())
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
        self.entries.get(index).map(Slot::key)
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
        self.get_index_of(value)
            .map(|index| (index, self.entries[index].key()))
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
        if self.entries.is_empty() {
            return None;
        }

        self.entries
            .iter()
            .position(|slot| slot.key().borrow() == value)
    }
}

// Mutation operations.
impl<T> Slice<T> {
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
        self.entries.reverse();
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
        self.entries.swap(a, b);
    }
}

// Sort operations.
impl<T> Slice<T> {
    /// Sorts the set.
    ///
    /// This sort is stable (i.e., does not reorder equal elements) and *O*(*n* \* log(*n*))
    /// worst-case.
    ///
    /// When applicable, unstable sorting is preferred because it is generally faster than stable
    /// sorting and it doesn't allocate auxiliary memory. See
    /// [`sort_unstable`](Self::sort_unstable).
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
        self.entries.sort();
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
        self.entries.sort_unstable();
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
        self.entries.sort_by(|a, b| compare(a.key(), b.key()));
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
        self.entries
            .sort_unstable_by(|a, b| compare(a.key(), b.key()));
    }

    /// Sort the set’s values in place using a key extraction function.
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
    /// use vecmap::VecSet;
    ///
    /// let mut set = VecSet::from(["b", "a", "c"]);
    ///
    /// set.sort_by_cached_key(|k| k.to_string());
    /// assert_eq!(set.as_std_slice(), ["a", "b", "c"]);
    /// ```
    pub fn sort_by_cached_key<K, F>(&mut self, mut sort_key: F)
    where
        K: Ord,
        F: FnMut(&T) -> K,
    {
        self.entries.sort_by_cached_key(|slot| sort_key(slot.key()));
    }
}

// Binary search operations.
impl<T> Slice<T> {
    /// Search over a sorted set for a value.
    ///
    /// Returns the position where that key is present, or the position where it can be inserted to
    /// maintain the sort. See [`slice::binary_search`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let set = VecSet::from(["a", "b", "d"]);
    /// assert_eq!(set.binary_search(&"b"), Ok(1));
    /// assert_eq!(set.binary_search(&"c"), Err(2));
    /// assert_eq!(set.binary_search(&"z"), Err(3));
    /// ```
    pub fn binary_search(&self, value: &T) -> Result<usize, usize>
    where
        T: Ord,
    {
        self.binary_search_by(|v| v.cmp(value))
    }

    /// Search over a sorted set with a comparator function.
    ///
    /// Returns the position where that value is present, or the position where it can be inserted
    /// to maintain the sort. See [`slice::binary_search_by`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let set = VecSet::from(["a", "b", "d"]);
    ///
    /// assert_eq!(set.binary_search_by(|probe| probe.cmp(&"b")), Ok(1));
    /// assert_eq!(set.binary_search_by(|probe| probe.cmp(&"c")), Err(2));
    /// assert_eq!(set.binary_search_by(|probe| probe.cmp(&"z")), Err(3));
    /// ```
    pub fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> Ordering,
    {
        self.entries.binary_search_by(|slot| f(slot.key()))
    }

    /// Search over a sorted set with an extraction function.
    ///
    /// Returns the position where that value is present, or the position where it can be inserted
    /// to maintain the sort. See [`slice::binary_search_by_key`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let map = VecSet::from([("a", 1), ("b", 2), ("d", 4)]);
    /// assert_eq!(map.binary_search_by_key(&"b", |&(k, _)| k), Ok(1));
    /// assert_eq!(map.binary_search_by_key(&"c", |&(k, _)| k), Err(2));
    /// assert_eq!(map.binary_search_by_key(&"z", |&(k, _)| k), Err(3));
    /// assert_eq!(map.binary_search_by_key(&4, |&(_, v)| v), Ok(2));
    /// ```
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> B,
        B: Ord,
    {
        self.entries.binary_search_by_key(b, |slot| f(slot.key()))
    }

    /// Returns the index of the partition point of a sorted set according to the given predicate
    /// (the index of the first element of the second partition).
    ///
    /// See [`slice::partition_point`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecSet;
    ///
    /// let map = VecSet::from([1, 2, 4]);
    /// assert_eq!(map.partition_point(|&v| v < 2), 1);
    /// assert_eq!(map.partition_point(|&v| v > 100), 0);
    /// assert_eq!(map.partition_point(|&v| v < 100), 3);
    /// ```
    pub fn partition_point<P>(&self, mut pred: P) -> usize
    where
        P: FnMut(&T) -> bool,
    {
        self.entries.partition_point(|slot| pred(slot.key()))
    }
}

impl<T> Index<usize> for Slice<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get_index(index).expect("Slice: index out of bounds")
    }
}

impl<T> Default for &Slice<T> {
    fn default() -> Self {
        Slice::new()
    }
}

impl<T> Default for &mut Slice<T> {
    fn default() -> Self {
        Slice::new_mut()
    }
}

impl<T: fmt::Debug> fmt::Debug for Slice<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: PartialEq> PartialEq for Slice<T> {
    fn eq(&self, other: &Self) -> bool {
        self.entries.len() == other.entries.len() && self.iter().eq(other)
    }
}

impl<T: Eq> Eq for Slice<T> {}

impl<T: PartialOrd> PartialOrd for Slice<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for Slice<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<'a, T> IntoIterator for &'a Slice<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
