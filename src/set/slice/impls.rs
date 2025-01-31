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

impl<T: PartialEq> PartialEq for Slice<T> {
    fn eq(&self, other: &Self) -> bool {
        self.entries.len() == other.entries.len() && self.iter().eq(other)
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
