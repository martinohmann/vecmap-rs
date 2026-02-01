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
        self.base
            .extend(iterable.into_iter().map(|(k, v)| crate::Slot::new(k, v)));
    }
}

impl<'a, K: Clone + Eq, V: Clone> Extend<(&'a K, &'a V)> for VecMap<K, V> {
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

impl<'a, K: Clone + Eq, V: Clone> Extend<&'a (K, V)> for VecMap<K, V> {
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
        map.extend(iter);
        map
    }
}

impl<K, V> From<Vec<(K, V)>> for VecMap<K, V>
where
    K: Eq,
{
    /// Constructs map from a vector of `(key → value)` pairs.
    ///
    /// **Note**: This conversion has a quadratic complexity because the
    /// conversion preserves order of elements while at the same time having to
    /// make sure no duplicate keys exist. To avoid it, sort and deduplicate
    /// the vector and use [`VecMap::from_vec_unchecked`] instead.
    fn from(mut vec: Vec<(K, V)>) -> Self {
        crate::dedup(&mut vec, |rhs, lhs| rhs.0 == lhs.0);
        // SAFETY: We've just deduplicated the elements.
        unsafe { Self::from_vec_unchecked(vec) }
    }
}

impl<K, V> From<&[(K, V)]> for VecMap<K, V>
where
    K: Clone + Eq,
    V: Clone,
{
    fn from(slice: &[(K, V)]) -> Self {
        VecMap::from_iter(slice)
    }
}

impl<K, V> From<&mut [(K, V)]> for VecMap<K, V>
where
    K: Clone + Eq,
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
    K: Eq,
{
    fn from(arr: [(K, V); N]) -> Self {
        VecMap::from_iter(arr)
    }
}

impl<K, V> PartialEq for VecMap<K, V>
where
    K: Eq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.base == other.base
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
