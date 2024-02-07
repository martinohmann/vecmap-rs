use super::KeyedVecSet;
use alloc::vec::Vec;

impl<K, V> IntoIterator for KeyedVecSet<K, V> {
    type Item = V;

    type IntoIter = <Vec<V> as core::iter::IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.base.into_iter()
    }
}

impl<'a, K, V> IntoIterator for &'a KeyedVecSet<K, V> {
    type Item = &'a V;

    type IntoIter = <&'a Vec<V> as core::iter::IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        (&self.base).into_iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut KeyedVecSet<K, V> {
    type Item = &'a mut V;

    type IntoIter = <&'a mut Vec<V> as core::iter::IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        (&mut self.base).into_iter()
    }
}
