use super::{Iter, Slot};
use alloc::boxed::Box;
use core::cmp::Ordering;
use core::ops::Deref;
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

    pub(super) fn from_boxed(entries: Box<[Slot<T>]>) -> Box<Self> {
        // SAFETY: `A [Slot<T>]` and a `Slice<T>` are essentially the same thing.
        unsafe { Box::from_raw(Box::into_raw(entries) as *mut Self) }
    }

    pub(super) fn as_raw_slice(&self) -> &[T] {
        // SAFETY: `&[Slot<T>]` and `&[T]` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<T>]>(&self.entries) as *const [T]) }
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
    /// assert_eq!(set.as_raw_slice(), ["a", "b", "c"]);
    /// ```
    pub fn sort_by_cached_key<K, F>(&mut self, mut sort_key: F)
    where
        K: Ord,
        F: FnMut(&T) -> K,
    {
        self.entries.sort_by_cached_key(|slot| sort_key(slot.key()));
    }
}

impl<T> Deref for Slice<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_raw_slice()
    }
}

impl<'a, T> IntoIterator for &'a Slice<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
