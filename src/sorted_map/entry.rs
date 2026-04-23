use super::SortedVecMap;
use crate::Slot;
use core::mem;

/// Entry for an existing key-value pair or a vacant slot in a [`SortedVecMap`].
#[derive(Debug)]
pub enum Entry<'a, K, V> {
    /// Existing slot with equivalent key.
    Occupied(OccupiedEntry<'a, K, V>),
    /// Vacant slot (no equivalent key in the map).
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: Ord,
{
    /// Ensures a value is in the entry by inserting the default if empty, and returns a mutable
    /// reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::SortedVecMap;
    ///
    /// let mut map: SortedVecMap<&str, u32> = SortedVecMap::new();
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
    pub fn or_insert_with<F>(self, call: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(call()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default
    /// function. The default function receives a reference to the key that was moved during the
    /// `.entry(key)` call so callers can compute a value from the key without cloning.
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
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(entry) => entry.key(),
            Entry::Vacant(entry) => entry.key(),
        }
    }

    /// Returns the index where the key-value pair exists or will be inserted.
    pub fn index(&self) -> usize {
        match self {
            Entry::Occupied(entry) => entry.index(),
            Entry::Vacant(entry) => entry.index(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into
    /// the map.
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

    /// Ensures a value is in the entry by inserting the default value if empty, and returns a
    /// mutable reference to the value in the entry.
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

/// A view into an occupied entry in a [`SortedVecMap`]. It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct OccupiedEntry<'a, K, V> {
    map: &'a mut SortedVecMap<K, V>,
    key: K,
    index: usize,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub(super) fn new(
        map: &'a mut SortedVecMap<K, V>,
        key: K,
        index: usize,
    ) -> OccupiedEntry<'a, K, V> {
        OccupiedEntry { map, key, index }
    }

    /// Gets a reference to the key in the entry.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Gets the index of the entry within the sorted sequence.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Take ownership of the key.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        &self.map[self.index]
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.map[self.index]
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in the entry with a
    /// lifetime bound to the map itself.
    pub fn into_mut(self) -> &'a mut V {
        &mut self.map[self.index]
    }

    /// Sets the value of the entry, and returns the entry's old value.
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Removes and returns the key-value pair stored in the map for this entry.
    ///
    /// Like `Vec::remove`, the pair is removed by shifting all of the elements that follow it,
    /// preserving their relative order (and therefore the sort invariant).
    pub fn remove_entry(self) -> (K, V) {
        self.map.remove_index(self.index)
    }

    /// Removes the key-value pair stored in the map for this entry, and returns the value.
    pub fn remove(self) -> V {
        self.remove_entry().1
    }
}

/// A view into a vacant entry in a [`SortedVecMap`]. It is part of the [`Entry`] enum.
///
/// The vacant entry stores the insertion index (the `Err` result of the failed binary search)
/// so that inserting into it is a single shift of at most *n* elements, without a second search.
#[derive(Debug)]
pub struct VacantEntry<'a, K, V> {
    map: &'a mut SortedVecMap<K, V>,
    key: K,
    index: usize,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub(super) fn new(
        map: &'a mut SortedVecMap<K, V>,
        key: K,
        index: usize,
    ) -> VacantEntry<'a, K, V> {
        VacantEntry { map, key, index }
    }

    /// Gets a reference to the key that would be used when inserting a value through the
    /// `VacantEntry`.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Returns the index at which the key-value pair will be inserted.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Take ownership of the key.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Sets the value of the entry with the `VacantEntry`'s key, and returns a mutable reference
    /// to it.
    pub fn insert(self, value: V) -> &'a mut V {
        // SAFETY: the binary search that produced `self.index` guaranteed the slot is vacant and
        // that inserting at this position preserves the sort order.
        unsafe {
            self.map
                .base
                .insert_at_unchecked(self.index, Slot::new(self.key, value));
        }
        &mut self.map[self.index]
    }
}
