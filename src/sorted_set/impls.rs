use core::ops::{BitAnd, BitOr, BitXor, Index, Sub};

use super::SortedVecSet;
use alloc::vec::Vec;

impl<T> Default for SortedVecSet<T> {
    fn default() -> Self {
        SortedVecSet::new()
    }
}

impl<T> Index<usize> for SortedVecSet<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get_index(index)
            .expect("SortedVecSet: index out of bounds")
    }
}

impl<T> Extend<T> for SortedVecSet<T>
where
    T: Ord,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.base.extend(iterable);
    }
}

impl<'a, T> Extend<&'a T> for SortedVecSet<T>
where
    T: 'a + Copy + Ord,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.base.extend(iterable.into_iter().copied());
    }
}

impl<T> FromIterator<T> for SortedVecSet<T>
where
    T: Ord,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        SortedVecSet {
            base: super::SortedKeyedVecSet::from_iter(iter),
        }
    }
}

impl<T> From<Vec<T>> for SortedVecSet<T>
where
    T: Ord,
{
    /// Constructs a sorted set from a vector.
    ///
    /// The vector is sorted and deduplicated internally. Runs in *O*(*n* log *n*).
    fn from(vec: Vec<T>) -> Self {
        SortedVecSet { base: vec.into() }
    }
}

impl<T> From<&[T]> for SortedVecSet<T>
where
    T: Clone + Ord,
{
    fn from(slice: &[T]) -> Self {
        SortedVecSet { base: slice.into() }
    }
}

impl<T> From<&mut [T]> for SortedVecSet<T>
where
    T: Clone + Ord,
{
    fn from(slice: &mut [T]) -> Self {
        SortedVecSet { base: slice.into() }
    }
}

impl<T, const N: usize> From<[T; N]> for SortedVecSet<T>
where
    T: Ord,
{
    fn from(arr: [T; N]) -> Self {
        SortedVecSet { base: arr.into() }
    }
}

impl<T> PartialEq for SortedVecSet<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &SortedVecSet<T>) -> bool {
        self.base == other.base
    }
}

impl<T> Eq for SortedVecSet<T> where T: Eq {}

impl<T> BitAnd<&SortedVecSet<T>> for &SortedVecSet<T>
where
    T: Ord + Clone,
{
    type Output = SortedVecSet<T>;

    /// Returns the set intersection, cloned into a new set.
    fn bitand(self, other: &SortedVecSet<T>) -> Self::Output {
        self.intersection(other).cloned().collect()
    }
}

impl<T> BitOr<&SortedVecSet<T>> for &SortedVecSet<T>
where
    T: Ord + Clone,
{
    type Output = SortedVecSet<T>;

    /// Returns the set union, cloned into a new set.
    fn bitor(self, other: &SortedVecSet<T>) -> Self::Output {
        self.union(other).cloned().collect()
    }
}

impl<T> BitXor<&SortedVecSet<T>> for &SortedVecSet<T>
where
    T: Ord + Clone,
{
    type Output = SortedVecSet<T>;

    /// Returns the set symmetric-difference, cloned into a new set.
    fn bitxor(self, other: &SortedVecSet<T>) -> Self::Output {
        self.symmetric_difference(other).cloned().collect()
    }
}

impl<T> Sub<&SortedVecSet<T>> for &SortedVecSet<T>
where
    T: Ord + Clone,
{
    type Output = SortedVecSet<T>;

    /// Returns the set difference, cloned into a new set.
    fn sub(self, other: &SortedVecSet<T>) -> Self::Output {
        self.difference(other).cloned().collect()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use alloc::vec;
    use core::ops::Bound;

    #[test]
    fn ordered_iteration() {
        let set = SortedVecSet::from([3, 1, 2]);
        let v: alloc::vec::Vec<_> = set.iter().copied().collect();
        assert_eq!(v, alloc::vec![1, 2, 3]);
    }

    #[test]
    fn from_vec_dedup() {
        let set = SortedVecSet::from(alloc::vec![3, 1, 2, 1, 3]);
        assert_eq!(set.len(), 3);
        assert_eq!(set.as_slice(), &[1, 2, 3]);
    }

    fn collect<'a, I: IntoIterator<Item = &'a i32>>(iter: I) -> alloc::vec::Vec<i32> {
        iter.into_iter().copied().collect()
    }

    // Merge-based set-op iterators: verify correctness on disjoint, overlapping, equal, and empty
    // inputs.
    #[test]
    fn intersection_disjoint() {
        let a = SortedVecSet::from([1, 3, 5]);
        let b = SortedVecSet::from([2, 4, 6]);
        assert!(a.intersection(&b).next().is_none());
    }

    #[test]
    fn intersection_overlapping() {
        let a = SortedVecSet::from([1, 2, 3, 4, 5]);
        let b = SortedVecSet::from([2, 4, 6]);
        assert_eq!(collect(a.intersection(&b)), vec![2, 4]);
        // Symmetric.
        assert_eq!(collect(b.intersection(&a)), vec![2, 4]);
    }

    #[test]
    fn intersection_equal_sets() {
        let a = SortedVecSet::from([1, 2, 3]);
        assert_eq!(collect(a.intersection(&a)), vec![1, 2, 3]);
    }

    #[test]
    fn intersection_with_empty() {
        let a = SortedVecSet::from([1, 2, 3]);
        let b: SortedVecSet<i32> = SortedVecSet::new();
        assert!(a.intersection(&b).next().is_none());
        assert!(b.intersection(&a).next().is_none());
    }

    #[test]
    fn difference_overlapping() {
        let a = SortedVecSet::from([1, 2, 3, 4, 5]);
        let b = SortedVecSet::from([2, 4, 6]);
        assert_eq!(collect(a.difference(&b)), vec![1, 3, 5]);
        assert_eq!(collect(b.difference(&a)), vec![6]);
    }

    #[test]
    fn difference_with_empty() {
        let a = SortedVecSet::from([1, 2, 3]);
        let b: SortedVecSet<i32> = SortedVecSet::new();
        assert_eq!(collect(a.difference(&b)), vec![1, 2, 3]);
        assert!(b.difference(&a).next().is_none());
    }

    #[test]
    fn union_preserves_order_and_dedups() {
        let a = SortedVecSet::from([1, 3, 5]);
        let b = SortedVecSet::from([2, 3, 4]);
        assert_eq!(collect(a.union(&b)), vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn union_with_empty() {
        let a = SortedVecSet::from([1, 2, 3]);
        let b: SortedVecSet<i32> = SortedVecSet::new();
        assert_eq!(collect(a.union(&b)), vec![1, 2, 3]);
        assert_eq!(collect(b.union(&a)), vec![1, 2, 3]);
    }

    #[test]
    fn symmetric_difference_in_sorted_order() {
        let a = SortedVecSet::from([1, 2, 3, 4]);
        let b = SortedVecSet::from([3, 4, 5, 6]);
        assert_eq!(collect(a.symmetric_difference(&b)), vec![1, 2, 5, 6]);
    }

    #[test]
    fn is_subset_and_superset() {
        let a = SortedVecSet::from([1, 2, 3]);
        let b = SortedVecSet::from([1, 2, 3, 4, 5]);
        assert!(a.is_subset(&b));
        assert!(b.is_superset(&a));
        assert!(!b.is_subset(&a));
        assert!(!a.is_superset(&b));
        // Proper-subset-like edge: equal sets are subsets of each other.
        assert!(a.is_subset(&a));
        // Disjoint.
        let c = SortedVecSet::from([10, 20]);
        assert!(!c.is_subset(&a));
        // Subset of empty.
        let empty: SortedVecSet<i32> = SortedVecSet::new();
        assert!(empty.is_subset(&a));
        assert!(!a.is_subset(&empty));
    }

    #[test]
    fn is_disjoint_merge_walk() {
        let a = SortedVecSet::from([1, 3, 5]);
        let b = SortedVecSet::from([2, 4, 6]);
        assert!(a.is_disjoint(&b));
        let c = SortedVecSet::from([5, 7]);
        assert!(!a.is_disjoint(&c));
        let empty: SortedVecSet<i32> = SortedVecSet::new();
        assert!(a.is_disjoint(&empty));
    }

    #[test]
    fn range_with_exclusive_bounds() {
        let set = SortedVecSet::from([1, 3, 5, 7, 9]);

        let collected: alloc::vec::Vec<_> = set.range(3..7).copied().collect();
        assert_eq!(collected, vec![3, 5]);

        let collected: alloc::vec::Vec<_> = set
            .range((Bound::Excluded(&3), Bound::Excluded(&9)))
            .copied()
            .collect();
        assert_eq!(collected, vec![5, 7]);
    }

    #[test]
    #[should_panic(expected = "range start is greater than range end")]
    fn range_panics_on_reversed_bounds() {
        let set = SortedVecSet::from([1, 3, 5]);
        let (lo, hi) = (5, 3);
        let _ = set.range(lo..hi);
    }

    #[test]
    fn append_with_overlap_other_wins_sort_invariant() {
        let mut a = SortedVecSet::from([1, 3, 5]);
        let mut b = SortedVecSet::from([3, 4, 6]);
        a.append(&mut b);
        assert_eq!(a.as_slice(), &[1, 3, 4, 5, 6]);
        assert!(b.is_empty());
    }

    #[test]
    fn append_empty_sides() {
        let mut a: SortedVecSet<i32> = SortedVecSet::new();
        let mut b = SortedVecSet::from([1, 2, 3]);
        a.append(&mut b);
        assert_eq!(a.as_slice(), &[1, 2, 3]);
        assert!(b.is_empty());

        let mut c = SortedVecSet::from([1, 2, 3]);
        let mut d: SortedVecSet<i32> = SortedVecSet::new();
        c.append(&mut d);
        assert_eq!(c.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn split_off_keeps_both_halves_sorted() {
        let mut a = SortedVecSet::from([1, 2, 3, 4, 5]);
        let b = a.split_off(3);
        assert_eq!(a.as_slice(), &[1, 2, 3]);
        assert_eq!(b.as_slice(), &[4, 5]);
    }

    #[test]
    fn drain_then_set_remains_sorted() {
        let mut set = SortedVecSet::from([1, 2, 3, 4, 5]);
        let drained: alloc::vec::Vec<_> = set.drain(1..4).collect();
        assert_eq!(drained, vec![2, 3, 4]);
        assert_eq!(set.as_slice(), &[1, 5]);
    }

    // Operator overloads use the iterators, so smoke-test them.
    #[test]
    fn operators_collect_correctly() {
        let a = SortedVecSet::from([1, 2, 3, 4]);
        let b = SortedVecSet::from([3, 4, 5, 6]);
        assert_eq!(&a & &b, SortedVecSet::from([3, 4]));
        assert_eq!(&a | &b, SortedVecSet::from([1, 2, 3, 4, 5, 6]));
        assert_eq!(&a ^ &b, SortedVecSet::from([1, 2, 5, 6]));
        assert_eq!(&a - &b, SortedVecSet::from([1, 2]));
    }

    // `Difference`/`Intersection`/etc. are Clone — verify.
    #[test]
    fn iterator_clones_are_independent() {
        let a = SortedVecSet::from([1, 2, 3, 4, 5]);
        let b = SortedVecSet::from([2, 4]);
        let diff = a.difference(&b);
        let cloned = diff.clone();
        assert_eq!(collect(diff), vec![1, 3, 5]);
        assert_eq!(collect(cloned), vec![1, 3, 5]);
    }
}
