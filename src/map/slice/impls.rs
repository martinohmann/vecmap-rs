use super::{Iter, IterMut, Slice};
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::ops::{Index, IndexMut};

impl<K, V, Q> Index<&Q> for Slice<K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("Slice: key not found")
    }
}

impl<K, V, Q> IndexMut<&Q> for Slice<K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.get_mut(key).expect("Slice: key not found")
    }
}

impl<K, V> Index<usize> for Slice<K, V> {
    type Output = V;

    fn index(&self, index: usize) -> &V {
        self.get_index(index).expect("Slice: index out of bounds").1
    }
}

impl<K, V> IndexMut<usize> for Slice<K, V> {
    fn index_mut(&mut self, index: usize) -> &mut V {
        self.get_index_mut(index)
            .expect("Slice: index out of bounds")
            .1
    }
}

impl<K, V> Default for &Slice<K, V> {
    fn default() -> Self {
        Slice::new()
    }
}

impl<K, V> Default for &mut Slice<K, V> {
    fn default() -> Self {
        Slice::new_mut()
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Slice<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<K: PartialEq, V: PartialEq> PartialEq for Slice<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.entries.len() == other.entries.len() && self.iter().eq(other)
    }
}

impl<K: Eq, V: Eq> Eq for Slice<K, V> {}

impl<K: PartialOrd, V: PartialOrd> PartialOrd for Slice<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<K: Ord, V: Ord> Ord for Slice<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<'a, K, V> IntoIterator for &'a Slice<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut Slice<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
