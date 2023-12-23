use super::{Entries, IterMut2, KeysMut, Slot, VecMap};
use core::borrow::Borrow;

/// Opt-in mutable access to keys.
///
/// These methods expose `&mut K`, mutable references to the key as it is stored in the map.
///
/// You are allowed to modify the keys in the map **as long as the modified key does not compare
/// equal to another key already in the map**.
///
/// If keys are modified erroneously, you are no longer able to look up values for duplicate keys
/// directly. This is sound (memory safe) but a logical error hazard (just like implementing
/// `PartialEq`, `Eq`, or `Hash` incorrectly would be).
///
/// This trait is sealed and cannot be implemented for types outside this crate.
pub trait MutableKeys: private::Sealed {
    /// The map's key type.
    type Key;

    /// The map's value type.
    type Value;

    /// Return the index, a mutable reference to the key and a mutable reference to the value
    /// stored for `key`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::map::{MutableKeys, VecMap};
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    ///
    /// if let Some((_, k, v)) = map.get_full_mut2(&1) {
    ///     *k = 2;
    ///     *v = "b";
    /// }
    /// assert_eq!(map.get(&1), None);
    /// assert_eq!(map.get(&2), Some(&"b"));
    /// ```
    fn get_full_mut2<Q>(&mut self, key: &Q) -> Option<(usize, &mut Self::Key, &mut Self::Value)>
    where
        Self::Key: Borrow<Q>,
        Q: Eq + ?Sized;

    /// Return a mutable reference to the key and a mutable reference to the value stored at
    /// `index`, if it is present, else `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::map::{MutableKeys, VecMap};
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// if let Some((k, v)) = map.get_index_mut2(0) {
    ///     *k = 2;
    ///     *v = "b";
    /// }
    /// assert_eq!(map[0], "b");
    /// assert_eq!(map.get(&1), None);
    /// assert_eq!(map.get(&2), Some(&"b"));
    /// ```
    fn get_index_mut2(&mut self, index: usize) -> Option<(&mut Self::Key, &mut Self::Value)>;

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&mut k, &mut v)` returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::map::{MutableKeys, VecMap};
    ///
    /// let mut map: VecMap<i32, i32> = (0..8).map(|x| (x, x*10)).collect();
    /// map.retain2(|k, v| {
    ///     std::mem::swap(k, v);  
    ///     *v % 2 == 0
    /// });
    /// assert_eq!(map.len(), 4);
    /// assert_eq!(map, VecMap::from([(0, 0), (20, 2), (40, 4), (60, 6)]));
    /// ```
    fn retain2<F>(&mut self, f: F)
    where
        F: FnMut(&mut Self::Key, &mut Self::Value) -> bool;

    /// An iterator visiting all key-value pairs in insertion order, with mutable references to the
    /// values. The iterator element type is `(&'a mut K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::map::{MutableKeys, VecMap};
    ///
    /// let mut map = VecMap::from([
    ///     ('a', 1),
    ///     ('b', 2),
    ///     ('c', 3),
    /// ]);
    ///
    /// // Update all values
    /// for (key, val) in map.iter_mut2() {
    ///     *key = key.to_ascii_uppercase();
    ///     *val *= 2;
    /// }
    ///
    /// assert_eq!(map, VecMap::from([('A', 2), ('B', 4), ('C', 6)]));
    /// ```
    fn iter_mut2(&mut self) -> IterMut2<'_, Self::Key, Self::Value>;

    /// An iterator visiting all keys mutably in insertion order. The iterator element type is `&'a
    /// mut K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::map::{MutableKeys, VecMap};
    ///
    /// let mut map = VecMap::from([
    ///     (1, "a"),
    ///     (2, "b"),
    ///     (3, "c"),
    /// ]);
    ///
    /// for key in map.keys_mut() {
    ///     *key = *key * 10;
    /// }
    ///
    /// assert_eq!(map, VecMap::from([(10, "a"), (20, "b"), (30, "c")]));
    /// ```
    fn keys_mut(&mut self) -> KeysMut<'_, Self::Key, Self::Value>;
}

impl<K, V> MutableKeys for VecMap<K, V> {
    type Key = K;
    type Value = V;

    fn get_full_mut2<Q>(&mut self, key: &Q) -> Option<(usize, &mut K, &mut V)>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.get_index_of(key).map(|index| {
            let (key, value) = self.base[index].muts();
            (index, key, value)
        })
    }

    fn get_index_mut2(&mut self, index: usize) -> Option<(&mut K, &mut V)> {
        self.base.get_mut(index).map(Slot::muts)
    }

    fn retain2<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut K, &mut V) -> bool,
    {
        self.base.retain_mut(|slot| {
            let (key, value) = slot.muts();
            f(key, value)
        });
    }

    fn iter_mut2(&mut self) -> IterMut2<'_, K, V> {
        IterMut2::new(self.as_entries_mut())
    }

    fn keys_mut(&mut self) -> KeysMut<'_, K, V> {
        KeysMut::new(self.as_entries_mut())
    }
}

mod private {
    pub trait Sealed {}

    impl<K, V> Sealed for super::VecMap<K, V> {}
}
