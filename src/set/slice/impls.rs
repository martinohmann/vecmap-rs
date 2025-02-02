use super::{Iter, SetSlice};
use crate::VecSet;
use core::cmp::Ordering;
use core::fmt;
use core::ops::{self, Bound, Index};

impl<T> Index<usize> for SetSlice<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get_index(index)
            .expect("SetSlice: index out of bounds")
    }
}

// We can't have `impl<I: RangeBounds<usize>> Index<I>` because that conflicts
// both upstream with `Index<usize>` and downstream with `Index<&Q>`.
// Instead, we repeat the implementations for all the core range types.
macro_rules! impl_index_range {
    ($range:ty) => {
        impl<T> Index<$range> for VecSet<T> {
            type Output = SetSlice<T>;

            fn index(&self, range: $range) -> &Self::Output {
                self.get_range(range).expect("VecSet: range out of bounds")
            }
        }

        impl<T> Index<$range> for SetSlice<T> {
            type Output = SetSlice<T>;

            fn index(&self, range: $range) -> &Self::Output {
                self.get_range(range)
                    .expect("SetSlice: range out of bounds")
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

impl<T> Default for &SetSlice<T> {
    fn default() -> Self {
        SetSlice::new()
    }
}

impl<T> Default for &mut SetSlice<T> {
    fn default() -> Self {
        SetSlice::new_mut()
    }
}

impl<T: fmt::Debug> fmt::Debug for SetSlice<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

macro_rules! impl_partial_eq_slice {
    ($ty:ty) => {
        impl<T: PartialEq, const N: usize> PartialEq<[T; N]> for $ty {
            fn eq(&self, other: &[T; N]) -> bool {
                self.as_slice().eq(other)
            }
        }

        impl<T: PartialEq> PartialEq<[T]> for $ty {
            fn eq(&self, other: &[T]) -> bool {
                self.as_slice().eq(other)
            }
        }
    };
}

impl_partial_eq_slice!(SetSlice<T>);
impl_partial_eq_slice!(&SetSlice<T>);
impl_partial_eq_slice!(&mut SetSlice<T>);

impl<T: PartialEq> PartialEq for SetSlice<T> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice().eq(other.as_slice())
    }
}

impl<T: Eq> Eq for SetSlice<T> {}

impl<T: PartialOrd> PartialOrd for SetSlice<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for SetSlice<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<'a, T> IntoIterator for &'a SetSlice<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::vecset;
    use alloc::vec::Vec;

    #[test]
    fn eq() {
        let mut set = vecset! {1, 2, 3};
        let mut set_clone = set.clone();

        assert_eq!(set, set_clone);
        assert_eq!(set.as_set_slice(), set_clone.as_set_slice());
        assert_eq!(set.as_set_slice(), &[1, 2, 3]);
        assert_eq!(set.as_set_slice(), [1, 2, 3]);
        assert_eq!(set.as_mut_set_slice(), [1, 2, 3]);

        set_clone.swap_indices(0, 2);

        assert_eq!(set, set_clone);
        assert_ne!(set.as_set_slice(), set_clone.as_set_slice());
        assert_ne!(set.as_set_slice(), &[3, 2, 1]);
        assert_ne!(set.as_set_slice(), [3, 2, 1]);
        assert_ne!(set.as_mut_set_slice(), [3, 2, 1]);
    }

    #[test]
    fn slice_index() {
        fn check(vec_slice: &[i32], set_slice: &SetSlice<i32>, sub_slice: &SetSlice<i32>) {
            assert_eq!(set_slice, sub_slice);
            assert_eq!(set_slice, vec_slice);
        }

        let vec: Vec<i32> = (0..10).map(|i| i * i).collect();
        let set: VecSet<i32> = vec.iter().cloned().collect();
        let slice = set.as_set_slice();

        // RangeFull
        check(&vec[..], &set[..], &slice[..]);

        for i in 0usize..10 {
            // Index
            assert_eq!(vec[i], set[i]);
            assert_eq!(vec[i], slice[i]);

            // RangeFrom
            check(&vec[i..], &set[i..], &slice[i..]);

            // RangeTo
            check(&vec[..i], &set[..i], &slice[..i]);

            // RangeToInclusive
            check(&vec[..=i], &set[..=i], &slice[..=i]);

            // (Bound<usize>, Bound<usize>)
            let bounds = (Bound::Excluded(i), Bound::Unbounded);
            check(&vec[i + 1..], &set[bounds], &slice[bounds]);

            for j in i..=10 {
                // Range
                check(&vec[i..j], &set[i..j], &slice[i..j]);
            }

            for j in i..10 {
                // RangeInclusive
                check(&vec[i..=j], &set[i..=j], &slice[i..=j]);
            }
        }
    }
}
