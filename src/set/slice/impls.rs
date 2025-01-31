use super::{Iter, Slice};
use core::cmp::Ordering;
use core::fmt;
use core::ops::Index;

impl<T> Index<usize> for Slice<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get_index(index).expect("Slice: index out of bounds")
    }
}

impl<T> Default for &Slice<T> {
    fn default() -> Self {
        Slice::new()
    }
}

impl<T> Default for &mut Slice<T> {
    fn default() -> Self {
        Slice::new_mut()
    }
}

impl<T: fmt::Debug> fmt::Debug for Slice<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

macro_rules! impl_partial_eq_std_slice {
    ($ty:ty) => {
        impl<T: PartialEq, const N: usize> PartialEq<[T; N]> for $ty {
            fn eq(&self, other: &[T; N]) -> bool {
                self.as_std_slice().eq(other)
            }
        }

        impl<T: PartialEq> PartialEq<[T]> for $ty {
            fn eq(&self, other: &[T]) -> bool {
                self.as_std_slice().eq(other)
            }
        }
    };
}

impl_partial_eq_std_slice!(Slice<T>);
impl_partial_eq_std_slice!(&Slice<T>);
impl_partial_eq_std_slice!(&mut Slice<T>);

impl<T: PartialEq> PartialEq for Slice<T> {
    fn eq(&self, other: &Self) -> bool {
        self.as_std_slice().eq(other.as_std_slice())
    }
}

impl<T: Eq> Eq for Slice<T> {}

impl<T: PartialOrd> PartialOrd for Slice<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for Slice<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<'a, T> IntoIterator for &'a Slice<T> {
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
        assert_eq!(set.as_slice(), set_clone.as_slice());
        assert_eq!(set.as_slice(), &[1, 2, 3]);
        assert_eq!(set.as_slice(), [1, 2, 3]);
        assert_eq!(set.as_mut_slice(), [1, 2, 3]);

        set_clone.swap_indices(0, 2);

        assert_eq!(set, set_clone);
        assert_ne!(set.as_slice(), set_clone.as_slice());
        assert_ne!(set.as_slice(), &[3, 2, 1]);
        assert_ne!(set.as_slice(), [3, 2, 1]);
        assert_ne!(set.as_mut_slice(), [3, 2, 1]);
    }
}
