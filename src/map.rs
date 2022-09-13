//! `VecMap` is a vector-based map implementation which retains the order inserted entries.

mod impls;

use alloc::vec::Vec;
use core::borrow::Borrow;
use core::mem;

/// A vector-based map implementation which retains the order of inserted entries.
///
/// Internally it is represented as a `Vec<(K, V)>` to support keys that are neither `Hash` nor
/// `Ord`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VecMap<K, V> {
    base: Vec<(K, V)>,
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

    /// Reverses the order of entries in the map, in place.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2), ("c", 3)]);
    /// map.reverse();
    /// assert_eq!(map, VecMap::from_iter([("c", 3), ("b", 2), ("a", 1)]));
    /// ```
    pub fn reverse(&mut self) {
        self.base.reverse();
    }

    /// Get the first key-value pair.
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    /// assert_eq!(map.first(), Some((&"a", &1)));
    /// ```
    pub fn first(&self) -> Option<(&K, &V)> {
        self.base.first().map(|e| (&e.0, &e.1))
    }

    /// Get the first key-value pair, with mutable access to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    ///
    /// if let Some((_, v)) = map.first_mut() {
    ///     *v = *v + 10;
    /// }
    /// assert_eq!(map.first(), Some((&"a", &11)));
    /// ```
    pub fn first_mut(&mut self) -> Option<(&K, &mut V)> {
        self.base.first_mut().map(|e| (&e.0, &mut e.1))
    }

    /// Get the last key-value pair.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    /// assert_eq!(map.last(), Some((&"b", &2)));
    /// map.pop();
    /// map.pop();
    /// assert_eq!(map.last(), None);
    /// ```
    pub fn last(&self) -> Option<(&K, &V)> {
        self.base.last().map(|e| (&e.0, &e.1))
    }

    /// Get the last key-value pair, with mutable access to the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::from_iter([("a", 1), ("b", 2)]);
    ///
    /// if let Some((_, v)) = map.last_mut() {
    ///     *v = *v + 10;
    /// }
    /// assert_eq!(map.last(), Some((&"b", &12)));
    /// ```
    pub fn last_mut(&mut self) -> Option<(&K, &mut V)> {
        self.base.last_mut().map(|e| (&e.0, &mut e.1))
    }

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
        self.base.pop()
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
}

// Lookup operations.
impl<K, V> VecMap<K, V> {
    /// Return `true` if an equivalent to `key` exists in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
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

    /// Return a reference to the value stored for `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_key_value(key).map(|(_, v)| v)
    }

    /// Return a mutable reference to the value stored for `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
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
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        match self.get_index_of(key) {
            Some(index) => Some(&mut self.base[index].1),
            None => None,
        }
    }

    /// Return references to the key-value pair stored at `index`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_index(0), Some((&1, &"a")));
    /// assert_eq!(map.get_index(1), None);
    /// ```
    pub fn get_index(&self, index: usize) -> Option<(&K, &V)> {
        self.base.get(index).map(|e| (&e.0, &e.1))
    }

    /// Return a reference to the key and a mutable reference to the value stored at `index`, if it
    /// is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// if let Some((_, v)) = map.get_index_mut(0) {
    ///     *v = "b";
    /// }
    /// assert_eq!(map[0], "b");
    /// ```
    pub fn get_index_mut(&mut self, index: usize) -> Option<(&K, &mut V)> {
        self.base.get_mut(index).map(|e| (&e.0, &mut e.1))
    }

    /// Return the index and references to the key-value pair stored for `key`, if it is present,
    /// else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_full(&1), Some((0, &1, &"a")));
    /// assert_eq!(map.get_full(&2), None);
    /// ```
    pub fn get_full<Q>(&self, key: &Q) -> Option<(usize, &K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        match self.get_index_of(key) {
            Some(index) => {
                let (k, v) = &self.base[index];
                Some((index, k, v))
            }
            None => None,
        }
    }

    /// Return the index, a reference to the key and a mutable reference to the value stored for
    /// `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    ///
    /// if let Some((_, _, v)) = map.get_full_mut(&1) {
    ///     *v = "b";
    /// }
    /// assert_eq!(map.get(&1), Some(&"b"));
    /// ```
    pub fn get_full_mut<Q>(&mut self, key: &Q) -> Option<(usize, &K, &mut V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        match self.get_index_of(key) {
            Some(index) => {
                let (k, v) = &mut self.base[index];
                Some((index, k, v))
            }
            None => None,
        }
    }

    /// Return references to the key-value pair stored for `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        match self.get_index_of(key) {
            Some(index) => {
                let (k, v) = &self.base[index];
                Some((k, v))
            }
            None => None,
        }
    }

    /// Return item index, if it exists in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert("a", 10);
    /// map.insert("b", 20);
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

        self.base.iter().position(|(k, _)| k.borrow() == key)
    }
}

// Removal operations.
impl<K, V> VecMap<K, V> {
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
        self.remove_entry(key).map(|(_, v)| v)
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
        match self.get_index_of(key) {
            Some(index) => Some(self.base.remove(index)),
            None => None,
        }
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
        self.swap_remove_entry(key).map(|(_, v)| v)
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
        match self.get_index_of(key) {
            Some(index) => Some(self.base.swap_remove(index)),
            None => None,
        }
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
        match self.get_index_of(&key) {
            Some(index) => {
                let old_value = mem::replace(&mut self.base[index], (key, value)).1;
                Some(old_value)
            }
            None => {
                self.base.push((key, value));
                None
            }
        }
    }
}
