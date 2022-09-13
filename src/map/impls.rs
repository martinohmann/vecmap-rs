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
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("VecMap: key not found")
    }
}

impl<K, V, Q> IndexMut<&Q> for VecMap<K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
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
    K: Eq,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let iter = iterable.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            (iter.size_hint().0 + 1) / 2
        };
        self.reserve(reserve);
        iter.for_each(move |(k, v)| {
            self.insert(k, v);
        });
    }
}

impl<'a, K, V> Extend<(&'a K, &'a V)> for VecMap<K, V>
where
    K: Copy + Eq,
    V: Copy,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = (&'a K, &'a V)>,
    {
        self.extend(iterable.into_iter().map(|(&key, &value)| (key, value)));
    }
}

impl<K, V> FromIterator<(K, V)> for VecMap<K, V>
where
    K: Eq,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let iter = iter.into_iter();
        let lower = iter.size_hint().0;
        let mut map = VecMap::with_capacity(lower);
        map.extend(iter);
        map
    }
}

impl<K, V> From<Vec<(K, V)>> for VecMap<K, V>
where
    K: Eq,
{
    fn from(vec: Vec<(K, V)>) -> Self {
        VecMap::from_iter(vec)
    }
}

impl<K, V> From<&[(K, V)]> for VecMap<K, V>
where
    K: Clone + Eq,
    V: Clone,
{
    fn from(slice: &[(K, V)]) -> Self {
        VecMap::from_iter(slice.to_vec())
    }
}

impl<K, V> From<&mut [(K, V)]> for VecMap<K, V>
where
    K: Clone + Eq,
    V: Clone,
{
    fn from(slice: &mut [(K, V)]) -> Self {
        VecMap::from_iter(slice.to_vec())
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for VecMap<K, V>
where
    K: Eq,
{
    fn from(arr: [(K, V); N]) -> Self {
        VecMap::from_iter(arr)
    }
}
