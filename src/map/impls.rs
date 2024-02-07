use crate::KeyedVecSet;

use super::VecMap;
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::ops::{Index, IndexMut};

impl<K, V> Default for VecMap<K, V> {
    fn default() -> Self {
        VecMap::new()
    }
}

impl<K, V, Q> Index<&Q> for VecMap<K, V>
where
    K: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("VecMap: key not found")
    }
}

impl<K, V, Q> IndexMut<&Q> for VecMap<K, V>
where
    K: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.get_mut(key).expect("VecMap: key not found")
    }
}

impl<K, V> Index<usize> for VecMap<K, V> {
    type Output = V;

    fn index(&self, index: usize) -> &V {
        self.get_index(index)
            .expect("VecMap: index out of bounds")
            .1
    }
}

impl<K, V> IndexMut<usize> for VecMap<K, V> {
    fn index_mut(&mut self, index: usize) -> &mut V {
        self.get_index_mut(index)
            .expect("VecMap: index out of bounds")
            .1
    }
}

impl<K, V> Extend<(K, V)> for VecMap<K, V>
where
    K: Ord,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = (K, V)>,
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
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, K, V> Extend<(&'a K, &'a V)> for VecMap<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
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

impl<'a, K, V> Extend<&'a (K, V)> for VecMap<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
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

impl<Item, K, V> FromIterator<Item> for VecMap<K, V>
where
    Self: Extend<Item>,
{
    fn from_iter<I: IntoIterator<Item = Item>>(iter: I) -> Self {
        let mut map = VecMap::new();
        map.extend(iter.into_iter());
        map
    }
}

impl<K, V> From<Vec<(K, V)>> for VecMap<K, V>
where
    K: Ord,
{
    /// Constructs map from a vector of `(key → value)` pairs.
    fn from(vec: Vec<(K, V)>) -> Self {
        let base = KeyedVecSet::from(vec);
        Self { base }
    }
}

impl<K, V> From<&[(K, V)]> for VecMap<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    fn from(slice: &[(K, V)]) -> Self {
        VecMap::from_iter(slice)
    }
}

impl<K, V> From<&mut [(K, V)]> for VecMap<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    fn from(slice: &mut [(K, V)]) -> Self {
        // False-positive, we're re-slicing on purpose to go from `&mut [(K, V)]` to `&[(K, V)]`.
        #[allow(clippy::redundant_slicing)]
        VecMap::from_iter(&slice[..])
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for VecMap<K, V>
where
    K: Ord,
{
    fn from(arr: [(K, V); N]) -> Self {
        VecMap::from_iter(arr)
    }
}

impl<K, V> PartialEq for VecMap<K, V>
where
    K: PartialEq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.base.eq(&other.base)
    }
}

impl<K, V> Eq for VecMap<K, V>
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
        assert_ne!(VecMap::from([("a", 1)]), VecMap::from([]));
        assert_ne!(VecMap::from([("a", 1)]), VecMap::from([("b", 2)]));
        assert_eq!(VecMap::from([("a", 1)]), VecMap::from([("a", 1)]));
        assert_ne!(VecMap::from([("a", 1)]), VecMap::from([("a", 1), ("b", 2)]));
        assert_eq!(
            VecMap::from([("a", 1), ("b", 2)]),
            VecMap::from([("a", 1), ("b", 2)])
        );
        assert_eq!(
            VecMap::from([("a", 1), ("b", 2)]),
            VecMap::from([("b", 2), ("a", 1)])
        );
    }
}
