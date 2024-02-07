use super::{Keyed, KeyedVecSet};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::ops::Index;

impl<K, V> Default for KeyedVecSet<K, V> {
    fn default() -> Self {
        KeyedVecSet::new()
    }
}

impl<K, V, Q> Index<&Q> for KeyedVecSet<K, V>
where
    K: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
    V: Keyed<K>,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("KeyedVecSet: key not found")
    }
}

impl<K, V> Index<usize> for KeyedVecSet<K, V> {
    type Output = V;

    fn index(&self, index: usize) -> &V {
        self.get_index(index)
            .expect("KeyedVecSet: index out of bounds")
    }
}

impl<K, V> Extend<V> for KeyedVecSet<K, V>
where
    K: Ord,
    V: Keyed<K>,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = V>,
    {
        let iter = iterable.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            // Round up but make sure we don’t overflow when size_hint ==
            // usize::MAX.
            let size_hint = iter.size_hint().0;
            size_hint / 2 + size_hint % 2
        };
        self.reserve(reserve);
        for v in iter {
            self.insert(v);
        }
    }
}

impl<'a, K, V: 'a> Extend<&'a V> for KeyedVecSet<K, V>
where
    K: Ord,
    V: Clone + Keyed<K>,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = &'a V>,
    {
        self.extend(iterable.into_iter().cloned());
    }
}

impl<Item, K, V> FromIterator<Item> for KeyedVecSet<K, V>
where
    Self: Extend<Item>,
{
    fn from_iter<I: IntoIterator<Item = Item>>(iter: I) -> Self {
        let mut map = KeyedVecSet::new();
        map.extend(iter.into_iter());
        map
    }
}

impl<K, V> From<Vec<V>> for KeyedVecSet<K, V>
where
    K: Ord + PartialEq,
    V: Keyed<K>,
{
    /// Constructs map from a vector of values.
    ///
    /// Values with duplicated keys will be deduplicated.
    fn from(mut vec: Vec<V>) -> Self {
        vec.sort_by(|a, b| a.key().cmp(b.key()));
        vec.dedup_by(|a, b| (*a).key() == (*b).key());
        unsafe { Self::from_vec_unchecked(vec) }
    }
}

impl<K, V> From<&[V]> for KeyedVecSet<K, V>
where
    K: Ord,
    V: Clone + Keyed<K>,
{
    fn from(slice: &[V]) -> Self {
        KeyedVecSet::from_iter(slice)
    }
}

impl<K, V> From<&mut [V]> for KeyedVecSet<K, V>
where
    K: Ord,
    V: Clone + Keyed<K>,
{
    fn from(slice: &mut [V]) -> Self {
        // False-positive, we're re-slicing on purpose to go from `&mut [(K, V)]` to `&[(K, V)]`.
        #[allow(clippy::redundant_slicing)]
        KeyedVecSet::from_iter(&slice[..])
    }
}

impl<K, V, const N: usize> From<[V; N]> for KeyedVecSet<K, V>
where
    K: Ord,
    V: Keyed<K>,
{
    fn from(arr: [V; N]) -> Self {
        KeyedVecSet::from_iter(arr)
    }
}

impl<K, V> PartialEq for KeyedVecSet<K, V>
where
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.base.eq(&other.base)
    }
}

impl<K, V> Eq for KeyedVecSet<K, V>
where
    K: Eq,
    V: Eq,
{
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn eq() {
        assert_ne!(
            KeyedVecSet::<&str, (&str, i32)>::from([("a", 1)]),
            KeyedVecSet::from([])
        );
        assert_ne!(
            KeyedVecSet::<&str, (&str, i32)>::from([("a", 1)]),
            KeyedVecSet::from([("b", 2)])
        );
        assert_eq!(
            KeyedVecSet::<&str, (&str, i32)>::from([("a", 1)]),
            KeyedVecSet::from([("a", 1)])
        );
        assert_ne!(
            KeyedVecSet::<&str, (&str, i32)>::from([("a", 1)]),
            KeyedVecSet::<&str, (&str, i32)>::from([("a", 1), ("b", 2)])
        );
        assert_eq!(
            KeyedVecSet::<&str, (&str, i32)>::from([("a", 1), ("b", 2)]),
            KeyedVecSet::<&str, (&str, i32)>::from([("a", 1), ("b", 2)])
        );
        assert_eq!(
            KeyedVecSet::<&str, (&str, i32)>::from([("a", 1), ("b", 2)]),
            KeyedVecSet::<&str, (&str, i32)>::from([("b", 2), ("a", 1)])
        );
    }
}
