use core::ops::{BitAnd, BitOr, BitXor, Index, Sub};

use super::VecSet;
use alloc::vec::Vec;

impl<T> Default for VecSet<T> {
    fn default() -> Self {
        VecSet::new()
    }
}

impl<T> Index<usize> for VecSet<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get_index(index).expect("VecSet: index out of bounds")
    }
}

impl<T> Extend<T> for VecSet<T>
where
    T: Eq,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = T>,
    {
        iterable.into_iter().for_each(|value| {
            self.insert(value);
        });
    }
}

impl<'a, T> Extend<&'a T> for VecSet<T>
where
    T: 'a + Copy + Eq,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.base.extend(iterable.into_iter().copied());
    }
}

impl<T> FromIterator<T> for VecSet<T>
where
    T: Eq,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut set = VecSet::new();
        set.extend(iter);
        set
    }
}

impl<T> From<Vec<T>> for VecSet<T>
where
    T: Eq,
{
    /// Constructs set from a vector.
    ///
    /// When the input contains equal elements, the first occurrence is kept and
    /// later equal values are ignored — the same rule as
    /// [`insert`][VecSet::insert], [`extend`][Extend::extend], and
    /// [`FromIterator`].
    ///
    /// **Note**: This conversion has a quadratic complexity because the
    /// conversion preserves order of elements while at the same time having to
    /// make sure no duplicate elements exist. To avoid it, sort and deduplicate
    /// the vector and use [`VecSet::from_vec_unchecked`] instead.
    fn from(mut vec: Vec<T>) -> Self {
        crate::dedup_keep_first(&mut vec, |lhs, rhs| lhs == rhs);
        // SAFETY: We've just deduplicated the elements.
        unsafe { Self::from_vec_unchecked(vec) }
    }
}

impl<T> From<&[T]> for VecSet<T>
where
    T: Clone + Eq,
{
    fn from(slice: &[T]) -> Self {
        slice.iter().cloned().collect()
    }
}

impl<T> From<&mut [T]> for VecSet<T>
where
    T: Clone + Eq,
{
    fn from(slice: &mut [T]) -> Self {
        slice.iter().cloned().collect()
    }
}

impl<T, const N: usize> From<[T; N]> for VecSet<T>
where
    T: Eq,
{
    fn from(arr: [T; N]) -> Self {
        VecSet::from_iter(arr)
    }
}

impl<T> PartialEq for VecSet<T>
where
    T: Eq,
{
    fn eq(&self, other: &VecSet<T>) -> bool {
        self.base == other.base
    }
}

impl<T> Eq for VecSet<T> where T: Eq {}

impl<T> BitAnd<&VecSet<T>> for &VecSet<T>
where
    T: Eq + Clone,
{
    type Output = VecSet<T>;

    /// Returns the set intersection, cloned into a new set.
    ///
    /// Values are collected in the same order that they appear in `self`.
    fn bitand(self, other: &VecSet<T>) -> Self::Output {
        self.intersection(other).cloned().collect()
    }
}

impl<T> BitOr<&VecSet<T>> for &VecSet<T>
where
    T: Eq + Clone,
{
    type Output = VecSet<T>;

    /// Returns the set union, cloned into a new set.
    ///
    /// Values from `self` are collected in their original order, followed by values that are
    /// unique to `other` in their original order.
    fn bitor(self, other: &VecSet<T>) -> Self::Output {
        self.union(other).cloned().collect()
    }
}

impl<T> BitXor<&VecSet<T>> for &VecSet<T>
where
    T: Eq + Clone,
{
    type Output = VecSet<T>;

    /// Returns the set symmetric-difference, cloned into a new set.
    ///
    /// Values from `self` are collected in their original order, followed by values from `other`
    /// in their original order.
    fn bitxor(self, other: &VecSet<T>) -> Self::Output {
        self.symmetric_difference(other).cloned().collect()
    }
}

impl<T> Sub<&VecSet<T>> for &VecSet<T>
where
    T: Eq + Clone,
{
    type Output = VecSet<T>;

    /// Returns the set difference, cloned into a new set.
    ///
    /// Values are collected in the same order that they appear in `self`.
    fn sub(self, other: &VecSet<T>) -> Self::Output {
        self.difference(other).cloned().collect()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    extern crate alloc;
    use alloc::vec;

    #[derive(Clone, Debug)]
    #[allow(dead_code)]
    struct Item(i32, &'static str);

    impl Eq for Item {}

    impl PartialEq for Item {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    fn set_via_inserts(items: &[Item]) -> VecSet<Item> {
        let mut set = VecSet::new();
        for item in items {
            set.insert(item.clone());
        }
        set
    }

    #[test]
    fn constructor_parity_with_insert() {
        let input = vec![Item(1, "first"), Item(2, "b"), Item(1, "second")];
        let expected = set_via_inserts(&[Item(1, "first"), Item(2, "b"), Item(1, "second")]);

        assert_eq!(VecSet::from(input.clone()), expected);
        assert_eq!(input.into_iter().collect::<VecSet<_>>(), expected);
        assert_eq!(
            VecSet::from([Item(1, "first"), Item(2, "b"), Item(1, "second")]),
            expected
        );
        assert_eq!(expected.as_slice(), &[Item(1, "first"), Item(2, "b")]);
    }

    #[test]
    fn insert_rejects_duplicate_without_replacing() {
        let mut set = VecSet::new();
        assert!(set.insert(Item(1, "first")));
        assert!(!set.insert(Item(1, "second")));
        assert_eq!(set.as_slice(), &[Item(1, "first")]);
    }

    #[test]
    fn extend_parity_with_insert() {
        let mut via_extend = VecSet::new();
        via_extend.extend([Item(1, "first"), Item(2, "b"), Item(1, "second")]);

        let via_insert = set_via_inserts(&[Item(1, "first"), Item(2, "b"), Item(1, "second")]);
        assert_eq!(via_extend, via_insert);
    }

    #[test]
    fn append_parity_with_insert() {
        let mut base = set_via_inserts(&[Item(1, "first")]);
        let mut extra = VecSet::from(vec![Item(1, "second"), Item(2, "b")]);

        base.append(&mut extra);

        let expected = set_via_inserts(&[Item(1, "first"), Item(1, "second"), Item(2, "b")]);
        assert_eq!(base, expected);
        assert!(extra.is_empty());
    }
}
