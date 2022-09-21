use super::*;

/// Entry for an existing key-value pair or a vacant location to insert one.
#[derive(Debug)]
pub enum Entry<'a, K, V> {
    /// Existing slot with equivalent key.
    Occupied(OccupiedEntry<'a, K, V>),
    /// Vacant slot (no equivalent key in the map).
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and returns a mutable
    /// reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    ///
    /// map.entry("poneyland").or_insert(3);
    /// assert_eq!(map["poneyland"], 3);
    ///
    /// *map.entry("poneyland").or_insert(10) *= 2;
    /// assert_eq!(map["poneyland"], 6);
    /// ```
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<&str, String> = VecMap::new();
    /// let s = "hoho".to_string();
    ///
    /// map.entry("poneyland").or_insert_with(|| s);
    ///
    /// assert_eq!(map["poneyland"], "hoho".to_string());
    /// ```
    pub fn or_insert_with<F>(self, call: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(call()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows for generating key-derived values for insertion by providing the default
    /// function a reference to the key that was moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<&str, usize> = VecMap::new();
    ///
    /// map.entry("poneyland").or_insert_with_key(|key| key.chars().count());
    ///
    /// assert_eq!(map["poneyland"], 9);
    /// ```
    pub fn or_insert_with_key<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce(&K) -> V,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(&entry.key);
                entry.insert(value)
            }
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    /// Returns the index where the key-value pair exists or will be inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// assert_eq!(map.entry("poneyland").index(), 0);
    /// ```
    pub fn index(&self) -> usize {
        match self {
            Entry::Occupied(entry) => entry.index(),
            Entry::Vacant(entry) => entry.index(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into the
    /// map.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 42);
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 43);
    /// ```
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(mut o) => {
                f(o.get_mut());
                Entry::Occupied(o)
            }
            x => x,
        }
    }

    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() {
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<&str, Option<u32>> = VecMap::new();
    /// map.entry("poneyland").or_default();
    ///
    /// assert_eq!(map["poneyland"], None);
    /// # }
    /// ```
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(V::default()),
        }
    }
}

/// A view into an occupied entry in a `VecMap`. It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct OccupiedEntry<'a, K, V> {
    map: &'a mut VecMap<K, V>,
    key: K,
    index: usize,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub(super) fn new(map: &'a mut VecMap<K, V>, key: K, index: usize) -> OccupiedEntry<'a, K, V> {
        OccupiedEntry { map, key, index }
    }

    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// map.entry("poneyland").or_insert(12);
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Gets the index of the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// map.entry("poneyland").or_insert(12);
    /// assert_eq!(map.entry("poneyland").index(), 0);
    /// ```
    pub fn index(&self) -> usize {
        self.index
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// map.insert("foo", 1);
    ///
    /// if let Entry::Occupied(v) = map.entry("foo") {
    ///     v.into_key();
    /// }
    /// ```
    pub fn into_key(self) -> K {
        self.key
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.get(), &12);
    /// }
    /// ```
    pub fn get(&self) -> &V {
        &self.map[self.index]
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: Self::into_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(*o.get(), 22);
    ///
    ///     // We can use the same Entry multiple times.
    ///     *o.get_mut() += 2;
    /// }
    ///
    /// assert_eq!(map["poneyland"], 24);
    /// ```
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.map[self.index]
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: Self::get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     *o.into_mut() += 10;
    /// }
    ///
    /// assert_eq!(map["poneyland"], 22);
    /// ```
    pub fn into_mut(self) -> &'a mut V {
        &mut self.map[self.index]
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     assert_eq!(o.insert(15), 12);
    /// }
    ///
    /// assert_eq!(map["poneyland"], 15);
    /// ```
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Removes and return the key-value pair stored in the map for this entry.
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the last element of the
    /// map and popping it off. **This perturbs the position of what used to be the last
    /// element!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// map.entry("poneyland").or_insert(12);
    /// map.entry("foo").or_insert(13);
    /// map.entry("bar").or_insert(14);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     // We delete the entry from the map.
    ///     o.swap_remove_entry();
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// assert_eq!(map.get_index_of("foo"), Some(1));
    /// assert_eq!(map.get_index_of("bar"), Some(0));
    /// ```
    pub fn swap_remove_entry(self) -> (K, V) {
        self.map.swap_remove_index(self.index)
    }

    /// Removes and return the key-value pair stored in the map for this entry.
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// map.entry("poneyland").or_insert(12);
    /// map.entry("foo").or_insert(13);
    /// map.entry("bar").or_insert(14);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     // We delete the entry from the map.
    ///     o.remove_entry();
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// assert_eq!(map.get_index_of("foo"), Some(0));
    /// assert_eq!(map.get_index_of("bar"), Some(1));
    /// ```
    pub fn remove_entry(self) -> (K, V) {
        self.map.remove_index(self.index)
    }

    /// Removes the key-value pair stored in the map for this entry, and return the value.
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the last element of the
    /// map and popping it off. **This perturbs the position of what used to be the last
    /// element!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// map.entry("poneyland").or_insert(12);
    /// map.entry("foo").or_insert(13);
    /// map.entry("bar").or_insert(14);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.swap_remove(), 12);
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// assert_eq!(map.get_index_of("foo"), Some(1));
    /// assert_eq!(map.get_index_of("bar"), Some(0));
    /// ```
    pub fn swap_remove(self) -> V {
        self.swap_remove_entry().1
    }

    /// Removes the key-value pair stored in the map for this entry, and return the value.
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the elements that follow it,
    /// preserving their relative order. **This perturbs the index of all of those elements!**
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// map.entry("poneyland").or_insert(12);
    /// map.entry("foo").or_insert(13);
    /// map.entry("bar").or_insert(14);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.remove(), 12);
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// assert_eq!(map.get_index_of("foo"), Some(0));
    /// assert_eq!(map.get_index_of("bar"), Some(1));
    /// ```
    pub fn remove(self) -> V {
        self.remove_entry().1
    }
}

/// A view into a vacant entry in a `VecMap`. It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct VacantEntry<'a, K, V> {
    map: &'a mut VecMap<K, V>,
    key: K,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub(super) fn new(map: &'a mut VecMap<K, V>, key: K) -> VacantEntry<'a, K, V> {
        VacantEntry { map, key }
    }

    /// Gets a reference to the key that would be used when inserting a value through the
    /// `VacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Return the index where the key-value pair will be inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    /// assert_eq!(map.entry("poneyland").index(), 0);
    /// ```
    pub fn index(&self) -> usize {
        self.map.len()
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    ///
    /// if let Entry::Vacant(v) = map.entry("poneyland") {
    ///     v.into_key();
    /// }
    /// ```
    pub fn into_key(self) -> K {
        self.key
    }

    /// Sets the value of the entry with the `VacantEntry`'s key, and returns a mutable reference
    /// to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    /// use vecmap::map::Entry;
    ///
    /// let mut map: VecMap<&str, u32> = VecMap::new();
    ///
    /// if let Entry::Vacant(o) = map.entry("poneyland") {
    ///     o.insert(37);
    /// }
    /// assert_eq!(map["poneyland"], 37);
    /// ```
    pub fn insert(self, value: V) -> &'a mut V {
        let index = self.map.push(self.key, value);
        &mut self.map[index]
    }
}
