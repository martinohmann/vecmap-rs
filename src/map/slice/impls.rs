use super::{Iter, IterMut, MapSlice};
use crate::VecMap;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::ops::{self, Bound, Index, IndexMut};

impl<K, V, Q> Index<&Q> for MapSlice<K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("MapSlice: key not found")
    }
}

impl<K, V, Q> IndexMut<&Q> for MapSlice<K, V>
where
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.get_mut(key).expect("MapSlice: key not found")
    }
}

impl<K, V> Index<usize> for MapSlice<K, V> {
    type Output = V;

    fn index(&self, index: usize) -> &V {
        self.get_index(index)
            .expect("MapSlice: index out of bounds")
            .1
    }
}

impl<K, V> IndexMut<usize> for MapSlice<K, V> {
    fn index_mut(&mut self, index: usize) -> &mut V {
        self.get_index_mut(index)
            .expect("MapSlice: index out of bounds")
            .1
    }
}

// We can't have `impl<I: RangeBounds<usize>> Index<I>` because that conflicts
// both upstream with `Index<usize>` and downstream with `Index<&Q>`.
// Instead, we repeat the implementations for all the core range types.
macro_rules! impl_index_range {
    ($range:ty) => {
        impl<K, V> Index<$range> for VecMap<K, V> {
            type Output = MapSlice<K, V>;

            fn index(&self, range: $range) -> &Self::Output {
                self.get_range(range).expect("VecMap: range out of bounds")
            }
        }

        impl<K, V> IndexMut<$range> for VecMap<K, V> {
            fn index_mut(&mut self, range: $range) -> &mut Self::Output {
                self.get_range_mut(range)
                    .expect("VecMap: range out of bounds")
            }
        }

        impl<K, V> Index<$range> for MapSlice<K, V> {
            type Output = MapSlice<K, V>;

            fn index(&self, range: $range) -> &Self::Output {
                self.get_range(range)
                    .expect("MapSlice: range out of bounds")
            }
        }

        impl<K, V> IndexMut<$range> for MapSlice<K, V> {
            fn index_mut(&mut self, range: $range) -> &mut Self::Output {
                self.get_range_mut(range)
                    .expect("MapSlice: range out of bounds")
            }
        }
    };
}

impl_index_range!(ops::Range<usize>);
impl_index_range!(ops::RangeFrom<usize>);
impl_index_range!(ops::RangeFull);
impl_index_range!(ops::RangeInclusive<usize>);
impl_index_range!(ops::RangeTo<usize>);
impl_index_range!(ops::RangeToInclusive<usize>);
impl_index_range!((Bound<usize>, Bound<usize>));

impl<K, V> Default for &MapSlice<K, V> {
    fn default() -> Self {
        MapSlice::new()
    }
}

impl<K, V> Default for &mut MapSlice<K, V> {
    fn default() -> Self {
        MapSlice::new_mut()
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for MapSlice<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

macro_rules! impl_partial_eq_slice {
    ($ty:ty) => {
        impl<K: PartialEq, V: PartialEq, const N: usize> PartialEq<[(K, V); N]> for $ty {
            fn eq(&self, other: &[(K, V); N]) -> bool {
                self.as_slice().eq(other)
            }
        }

        impl<K: PartialEq, V: PartialEq> PartialEq<[(K, V)]> for $ty {
            fn eq(&self, other: &[(K, V)]) -> bool {
                self.as_slice().eq(other)
            }
        }
    };
}

impl_partial_eq_slice!(MapSlice<K, V>);
impl_partial_eq_slice!(&MapSlice<K, V>);
impl_partial_eq_slice!(&mut MapSlice<K, V>);

impl<K: PartialEq, V: PartialEq> PartialEq for MapSlice<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice().eq(other.as_slice())
    }
}

impl<K: Eq, V: Eq> Eq for MapSlice<K, V> {}

impl<K: PartialOrd, V: PartialOrd> PartialOrd for MapSlice<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<K: Ord, V: Ord> Ord for MapSlice<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<'a, K, V> IntoIterator for &'a MapSlice<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut MapSlice<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

#[cfg(test)]
mod test {
    use crate::vecmap;

    #[test]
    fn eq() {
        let mut map = vecmap! {"a" => 1, "b" => 2, "c" => 3};
        let mut map_clone = map.clone();

        assert_eq!(map, map_clone);
        assert_eq!(map.as_map_slice(), map_clone.as_map_slice());
        assert_eq!(map.as_map_slice(), &[("a", 1), ("b", 2), ("c", 3)]);
        assert_eq!(map.as_map_slice(), [("a", 1), ("b", 2), ("c", 3)]);
        assert_eq!(map.as_mut_map_slice(), [("a", 1), ("b", 2), ("c", 3)]);

        map_clone.swap_indices(0, 2);

        assert_eq!(map, map_clone);
        assert_ne!(map.as_map_slice(), map_clone.as_map_slice());
        assert_ne!(map.as_map_slice(), &[("c", 3), ("b", 2), ("a", 1)]);
        assert_ne!(map.as_map_slice(), [("c", 3), ("b", 2), ("a", 1)]);
        assert_ne!(map.as_mut_map_slice(), [("c", 3), ("b", 2), ("a", 1)]);
    }
}
