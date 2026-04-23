use super::SortedVecMap;
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::ops::{Index, IndexMut};

impl<K, V> Default for SortedVecMap<K, V> {
    fn default() -> Self {
        SortedVecMap::new()
    }
}

impl<K, V, Q> Index<&Q> for SortedVecMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("SortedVecMap: key not found")
    }
}

impl<K, V, Q> IndexMut<&Q> for SortedVecMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.get_mut(key).expect("SortedVecMap: key not found")
    }
}

impl<K, V> Index<usize> for SortedVecMap<K, V> {
    type Output = V;

    fn index(&self, index: usize) -> &V {
        self.get_index(index)
            .expect("SortedVecMap: index out of bounds")
            .1
    }
}

impl<K, V> IndexMut<usize> for SortedVecMap<K, V> {
    fn index_mut(&mut self, index: usize) -> &mut V {
        self.get_index_mut(index)
            .expect("SortedVecMap: index out of bounds")
            .1
    }
}

impl<K, V> Extend<(K, V)> for SortedVecMap<K, V>
where
    K: Ord,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = (K, V)>,
    {
        self.base
            .extend(iterable.into_iter().map(|(k, v)| crate::Slot::new(k, v)));
    }
}

impl<'a, K: Clone + Ord, V: Clone> Extend<(&'a K, &'a V)> for SortedVecMap<K, V> {
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = (&'a K, &'a V)>,
    {
        self.extend(
            iterable
                .into_iter()
                .map(|(key, value)| (key.clone(), value.clone())),
        );
    }
}

impl<'a, K: Clone + Ord, V: Clone> Extend<&'a (K, V)> for SortedVecMap<K, V> {
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = &'a (K, V)>,
    {
        self.extend(
            iterable
                .into_iter()
                .map(|(key, value)| (key.clone(), value.clone())),
        );
    }
}

impl<Item, K, V> FromIterator<Item> for SortedVecMap<K, V>
where
    Self: Extend<Item>,
{
    fn from_iter<I: IntoIterator<Item = Item>>(iter: I) -> Self {
        let mut map = SortedVecMap::new();
        map.extend(iter);
        map
    }
}

impl<K, V> From<Vec<(K, V)>> for SortedVecMap<K, V>
where
    K: Ord,
{
    /// Constructs a sorted map from a vector of `(key → value)` pairs.
    ///
    /// The input is sorted by key. When duplicate keys are present, the *last* occurrence wins
    /// (matching the behaviour of inserting pairs one-by-one and of
    /// [`BTreeMap::from_iter`](alloc::collections::BTreeMap::from_iter)). Runs in *O*(*n* log *n*).
    fn from(vec: Vec<(K, V)>) -> Self {
        // SAFETY: `Vec<(K, V)>` and `Vec<Slot<K, V>>` have the same memory layout.
        let base_vec: Vec<crate::Slot<K, V>> = unsafe { crate::transmute_vec(vec) };
        SortedVecMap {
            base: base_vec.into(),
        }
    }
}

impl<K, V> From<&[(K, V)]> for SortedVecMap<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    fn from(slice: &[(K, V)]) -> Self {
        SortedVecMap::from_iter(slice)
    }
}

impl<K, V> From<&mut [(K, V)]> for SortedVecMap<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    fn from(slice: &mut [(K, V)]) -> Self {
        // False-positive, we're re-slicing on purpose.
        #[allow(clippy::redundant_slicing)]
        SortedVecMap::from_iter(&slice[..])
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for SortedVecMap<K, V>
where
    K: Ord,
{
    fn from(arr: [(K, V); N]) -> Self {
        SortedVecMap::from_iter(arr)
    }
}

impl<K, V> PartialEq for SortedVecMap<K, V>
where
    K: PartialEq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.base == other.base
    }
}

impl<K, V> Eq for SortedVecMap<K, V>
where
    K: Eq,
    V: Eq,
{
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::sorted_map::Entry;
    use alloc::vec;
    use core::ops::Bound;

    #[test]
    fn eq() {
        assert_ne!(SortedVecMap::from([("a", 1)]), SortedVecMap::from([]));
        assert_eq!(
            SortedVecMap::from([("a", 1)]),
            SortedVecMap::from([("a", 1)])
        );
        assert_eq!(
            SortedVecMap::from([("a", 1), ("b", 2)]),
            SortedVecMap::from([("b", 2), ("a", 1)])
        );
    }

    #[test]
    fn ordered_iteration() {
        let map = SortedVecMap::from([(3, "c"), (1, "a"), (2, "b")]);
        let collected: alloc::vec::Vec<_> = map.iter().map(|(k, v)| (*k, *v)).collect();
        assert_eq!(collected, alloc::vec![(1, "a"), (2, "b"), (3, "c")]);
    }

    // `From<Vec>` and `FromIterator` must both resolve duplicate keys the same way: last value
    // wins, matching the one-by-one `insert` behaviour and `BTreeMap::from_iter`.
    #[test]
    fn from_vec_keeps_last_value_on_duplicate() {
        let map = SortedVecMap::from(vec![("a", 1), ("b", 2), ("a", 10), ("b", 20)]);
        assert_eq!(map.len(), 2);
        assert_eq!(map[&"a"], 10);
        assert_eq!(map[&"b"], 20);
    }

    #[test]
    fn from_iter_keeps_last_value_on_duplicate() {
        let map: SortedVecMap<_, _> = [("a", 1), ("b", 2), ("a", 10)].into_iter().collect();
        assert_eq!(map[&"a"], 10);
        assert_eq!(map[&"b"], 2);
    }

    // VacantEntry stores the insertion index from the binary search. Inserting through it must
    // preserve the sort order at all positions — front, middle, and back.
    #[test]
    fn vacant_entry_insert_at_boundaries() {
        let mut map: SortedVecMap<i32, &str> = SortedVecMap::new();
        // Insert into empty (index 0).
        assert!(matches!(map.entry(5), Entry::Vacant(_)));
        map.entry(5).or_insert("five");

        // Insert at front (index 0).
        if let Entry::Vacant(v) = map.entry(1) {
            assert_eq!(v.index(), 0);
            v.insert("one");
        } else {
            panic!("expected vacant");
        }

        // Insert at back (index len).
        if let Entry::Vacant(v) = map.entry(10) {
            assert_eq!(v.index(), 2);
            v.insert("ten");
        } else {
            panic!("expected vacant");
        }

        // Insert in middle.
        if let Entry::Vacant(v) = map.entry(7) {
            assert_eq!(v.index(), 2);
            v.insert("seven");
        } else {
            panic!("expected vacant");
        }

        let collected: alloc::vec::Vec<_> = map.iter().map(|(k, v)| (*k, *v)).collect();
        assert_eq!(
            collected,
            vec![(1, "one"), (5, "five"), (7, "seven"), (10, "ten")]
        );
    }

    #[test]
    fn occupied_entry_replaces_in_place() {
        let mut map = SortedVecMap::from([(1, "a"), (2, "b"), (3, "c")]);
        match map.entry(2) {
            Entry::Occupied(mut o) => {
                assert_eq!(o.index(), 1);
                assert_eq!(o.insert("B"), "b");
            }
            Entry::Vacant(_) => panic!("expected occupied"),
        }
        assert_eq!(map[&2], "B");
        assert_eq!(map.as_slice(), &[(1, "a"), (2, "B"), (3, "c")]);
    }

    // `range` with mixed inclusive/exclusive bounds on both sides.
    #[test]
    fn range_with_exclusive_bounds() {
        let map = SortedVecMap::from([(1, 'a'), (3, 'c'), (5, 'e'), (7, 'g'), (9, 'i')]);

        let collected: alloc::vec::Vec<_> = map.range(3..=7).map(|(k, _)| *k).collect();
        assert_eq!(collected, vec![3, 5, 7]);

        let collected: alloc::vec::Vec<_> = map.range(3..7).map(|(k, _)| *k).collect();
        assert_eq!(collected, vec![3, 5]);

        // Both-exclusive range.
        let collected: alloc::vec::Vec<_> = map
            .range((Bound::Excluded(&3), Bound::Excluded(&7)))
            .map(|(k, _)| *k)
            .collect();
        assert_eq!(collected, vec![5]);

        // Unbounded ends.
        let collected: alloc::vec::Vec<_> = map
            .range((Bound::Unbounded, Bound::Included(&3)))
            .map(|(k, _)| *k)
            .collect();
        assert_eq!(collected, vec![1, 3]);
    }

    #[test]
    #[should_panic(expected = "range start is greater than range end")]
    fn range_panics_on_reversed_bounds() {
        let map = SortedVecMap::from([(1, 'a'), (3, 'c'), (5, 'e')]);
        let (lo, hi) = (5, 3);
        let _ = map.range(lo..hi);
    }

    #[test]
    fn range_mut_updates_values_without_disturbing_order() {
        let mut map = SortedVecMap::from([(1, 0), (3, 0), (5, 0), (7, 0)]);
        for (_, v) in map.range_mut(3..=5) {
            *v = 100;
        }
        assert_eq!(map[&1], 0);
        assert_eq!(map[&3], 100);
        assert_eq!(map[&5], 100);
        assert_eq!(map[&7], 0);
        // Sort order preserved.
        let keys: alloc::vec::Vec<_> = map.keys().copied().collect();
        assert_eq!(keys, vec![1, 3, 5, 7]);
    }

    // `append` must preserve sort order, apply BTreeMap-style "other wins" semantics on
    // overlapping keys, and leave `other` empty.
    #[test]
    fn append_with_overlap_other_wins() {
        let mut a = SortedVecMap::from([(1, "a"), (3, "c"), (5, "e")]);
        let mut b = SortedVecMap::from([(3, "C"), (4, "d"), (6, "f")]);
        a.append(&mut b);

        assert!(b.is_empty());
        assert_eq!(
            a.as_slice(),
            &[(1, "a"), (3, "C"), (4, "d"), (5, "e"), (6, "f")]
        );
    }

    #[test]
    fn append_empty_other() {
        let mut a = SortedVecMap::from([(1, "a"), (2, "b")]);
        let mut b: SortedVecMap<i32, &str> = SortedVecMap::new();
        a.append(&mut b);
        assert_eq!(a.len(), 2);
    }

    #[test]
    fn append_empty_self() {
        let mut a: SortedVecMap<i32, &str> = SortedVecMap::new();
        let mut b = SortedVecMap::from([(1, "a"), (2, "b")]);
        a.append(&mut b);
        assert_eq!(a.len(), 2);
        assert!(b.is_empty());
    }

    #[test]
    fn retain_preserves_sort_order() {
        let mut map: SortedVecMap<i32, i32> = (0..10).map(|x| (x, x * 10)).collect();
        map.retain(|&k, _| k % 3 == 0);
        let keys: alloc::vec::Vec<_> = map.keys().copied().collect();
        assert_eq!(keys, vec![0, 3, 6, 9]);
    }

    #[test]
    fn drain_with_empty_range_leaves_map_untouched() {
        let mut map = SortedVecMap::from([(1, "a"), (2, "b"), (3, "c")]);
        let collected: alloc::vec::Vec<_> = map.drain(1..1).collect();
        assert!(collected.is_empty());
        assert_eq!(map.len(), 3);
    }

    #[test]
    fn first_and_last_mutable() {
        let mut map = SortedVecMap::from([(1, 10), (2, 20), (3, 30)]);
        if let Some((k, v)) = map.first_key_value_mut() {
            assert_eq!(*k, 1);
            *v = 100;
        }
        if let Some((k, v)) = map.last_key_value_mut() {
            assert_eq!(*k, 3);
            *v = 300;
        }
        assert_eq!(map[&1], 100);
        assert_eq!(map[&3], 300);
    }

    #[test]
    fn pop_first_and_last_ordering() {
        let mut map = SortedVecMap::from([(2, 'b'), (1, 'a'), (3, 'c')]);
        assert_eq!(map.pop_first(), Some((1, 'a')));
        assert_eq!(map.pop_last(), Some((3, 'c')));
        assert_eq!(map.pop_first(), Some((2, 'b')));
        assert_eq!(map.pop_first(), None);
        assert_eq!(map.pop_last(), None);
    }

    // PartialEq is relaxed to K: PartialEq — we must be able to compare maps whose key type is
    // PartialEq but not Ord.
    #[test]
    fn partial_eq_does_not_require_ord_on_value() {
        // Floats are PartialEq but not Ord; keys are integers (Ord), values are f64 (PartialEq).
        let a = SortedVecMap::from([(1_u8, 1.5_f64), (2, 2.5)]);
        let b = SortedVecMap::from([(1_u8, 1.5_f64), (2, 2.5)]);
        assert!(a == b);
    }
}
