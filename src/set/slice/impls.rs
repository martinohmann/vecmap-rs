use super::{Iter, SetSlice};
use core::cmp::Ordering;
use core::fmt;
use core::ops::Index;

impl<T> Index<usize> for SetSlice<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get_index(index)
            .expect("SetSlice: index out of bounds")
    }
}

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
    use crate::vecset;

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
}
