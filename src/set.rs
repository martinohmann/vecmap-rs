//! `VecSet` is a vector-based set implementation which retains the order inserted elements.

mod impls;
mod iter;

use super::{Entries, Slot, VecMap};
use alloc::vec::Vec;
use core::borrow::Borrow;

pub use self::iter::{IntoIter, Iter};

/// A vector-based set implementation which retains the order of inserted elements.
///
/// Internally it is represented as a `Vec<T>` to support keys that are neither `Hash` nor `Ord`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
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
}

// Removal operations.
impl<T> VecSet<T> {
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

    /// Remove the element equivalent to `value`.
    ///
    /// Like `Vec::swap_remove`, the element is removed by swapping it with the last element of
    /// the map and popping it off. **This perturbs the position of what used to be the last
    /// element!**
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
