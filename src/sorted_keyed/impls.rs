use super::{Keyed, SortedKeyedVecSet};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::ops::{Index, IndexMut};

impl<K, V> Default for SortedKeyedVecSet<K, V> {
    fn default() -> Self {
        SortedKeyedVecSet::new()
    }
}

impl<K, V, Q> Index<&Q> for SortedKeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("SortedKeyedVecSet: key not found")
    }
}

impl<K, V, Q> IndexMut<&Q> for SortedKeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.get_mut(key).expect("SortedKeyedVecSet: key not found")
    }
}

impl<K, V> Index<usize> for SortedKeyedVecSet<K, V> {
    type Output = V;

    fn index(&self, index: usize) -> &Self::Output {
        &self.base[index]
    }
}

impl<K, V> IndexMut<usize> for SortedKeyedVecSet<K, V> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.base[index]
    }
}

impl<K, V> Extend<V> for SortedKeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Ord,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = V>,
    {
        let iter = iterable.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            let size_hint = iter.size_hint().0;
            size_hint / 2 + size_hint % 2
        };
        self.reserve(reserve);
        iter.for_each(move |value| {
            self.insert(value);
        });
    }
}

impl<'a, K, V: Clone> Extend<&'a V> for SortedKeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Ord,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = &'a V>,
    {
        self.extend(iterable.into_iter().cloned());
    }
}

impl<K, V> FromIterator<V> for SortedKeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Ord,
{
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let lower = iter.size_hint().0;
        let mut set = SortedKeyedVecSet::with_capacity(lower);
        set.extend(iter);
        set
    }
}

impl<K, V> From<Vec<V>> for SortedKeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Ord,
{
    /// Constructs a sorted set from a vector of values.
    ///
    /// When duplicate keys are present, the *last* occurrence wins (matching the behaviour of
    /// inserting values one-by-one and of [`BTreeMap::from_iter`]).
    ///
    /// [`BTreeMap::from_iter`]: alloc::collections::BTreeMap::from_iter
    fn from(mut vec: Vec<V>) -> Self {
        // Reverse + stable sort places the *last* occurrence of each key first within its run, so
        // `dedup_by` keeps the latest value.
        vec.reverse();
        vec.sort_by(|a, b| a.key().cmp(b.key()));
        vec.dedup_by(|a, b| Keyed::key(&*a).cmp(Keyed::key(&*b)).is_eq());
        // SAFETY: the vector is now sorted by key with no duplicates.
        unsafe { Self::from_vec_unchecked(vec) }
    }
}

impl<K, V> From<&[V]> for SortedKeyedVecSet<K, V>
where
    V: Clone + Keyed<K>,
    K: Ord,
{
    fn from(slice: &[V]) -> Self {
        slice.iter().cloned().collect()
    }
}

impl<K, V> From<&mut [V]> for SortedKeyedVecSet<K, V>
where
    V: Clone + Keyed<K>,
    K: Ord,
{
    fn from(slice: &mut [V]) -> Self {
        slice.iter().cloned().collect()
    }
}

impl<K, V, const N: usize> From<[V; N]> for SortedKeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Ord,
{
    fn from(arr: [V; N]) -> Self {
        SortedKeyedVecSet::from_iter(arr)
    }
}

impl<K, V> PartialEq for SortedKeyedVecSet<K, V>
where
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        // Both sides are sorted by key with no duplicates, so a slice-wise comparison suffices.
        self.base == other.base
    }
}

impl<K, V> Eq for SortedKeyedVecSet<K, V> where V: Eq {}

#[cfg(test)]
mod test {
    use super::*;
    extern crate alloc;
    use alloc::vec;

    #[derive(Debug, PartialEq, Eq, Clone)]
    struct Entry(i32, &'static str);

    impl Keyed<i32> for Entry {
        fn key(&self) -> &i32 {
            &self.0
        }
    }

    #[test]
    fn default() {
        let set: SortedKeyedVecSet<i32, Entry> = SortedKeyedVecSet::default();
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn index_by_key() {
        let mut set = SortedKeyedVecSet::<i32, Entry>::new();
        set.insert(Entry(1, "a"));
        assert_eq!(set[&1], Entry(1, "a"));
    }

    #[test]
    fn extend_and_sort() {
        let mut set = SortedKeyedVecSet::<i32, Entry>::new();
        set.extend(vec![Entry(3, "c"), Entry(1, "a"), Entry(2, "b")]);
        assert_eq!(set.len(), 3);
        assert_eq!(set.as_slice()[0], Entry(1, "a"));
        assert_eq!(set.as_slice()[1], Entry(2, "b"));
        assert_eq!(set.as_slice()[2], Entry(3, "c"));
    }

    #[test]
    fn from_vec_dedup_keeps_last() {
        let set = SortedKeyedVecSet::<i32, Entry>::from(vec![
            Entry(2, "b"),
            Entry(1, "a"),
            Entry(2, "b2"),
        ]);
        assert_eq!(set.len(), 2);
        assert_eq!(set[&1], Entry(1, "a"));
        // Duplicate key (2) kept the last-seen value, matching `insert` semantics.
        assert_eq!(set[&2], Entry(2, "b2"));
    }

    #[test]
    fn remove_preserves_order() {
        let mut set = SortedKeyedVecSet::<i32, Entry>::new();
        set.insert(Entry(1, "a"));
        set.insert(Entry(2, "b"));
        set.insert(Entry(3, "c"));
        assert_eq!(set.remove(&2), Some(Entry(2, "b")));
        assert_eq!(set.as_slice()[0], Entry(1, "a"));
        assert_eq!(set.as_slice()[1], Entry(3, "c"));
    }

    #[test]
    fn pop_first_and_last() {
        let mut set = SortedKeyedVecSet::<i32, Entry>::new();
        set.insert(Entry(2, "b"));
        set.insert(Entry(1, "a"));
        set.insert(Entry(3, "c"));
        assert_eq!(set.pop_first(), Some(Entry(1, "a")));
        assert_eq!(set.pop_last(), Some(Entry(3, "c")));
        assert_eq!(set.pop_first(), Some(Entry(2, "b")));
        assert_eq!(set.pop_first(), None);
    }

    #[test]
    fn key_range() {
        let set = SortedKeyedVecSet::<i32, Entry>::from(vec![
            Entry(1, "a"),
            Entry(3, "c"),
            Entry(5, "e"),
            Entry(7, "g"),
        ]);
        assert_eq!(set.key_range_to_indices::<i32, _>(2..6), (1, 3));
        assert_eq!(set.key_range_to_indices::<i32, _>(..), (0, 4));
        assert_eq!(set.key_range_to_indices::<i32, _>(3..=5), (1, 3));
    }

    #[test]
    fn eq() {
        assert_eq!(
            SortedKeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a"), Entry(2, "b")]),
            SortedKeyedVecSet::<i32, Entry>::from(vec![Entry(2, "b"), Entry(1, "a")])
        );
        assert_ne!(
            SortedKeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a")]),
            SortedKeyedVecSet::<i32, Entry>::from(vec![])
        );
    }
}
