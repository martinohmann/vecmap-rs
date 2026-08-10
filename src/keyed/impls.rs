use super::{Keyed, KeyedVecSet};
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::ops::{Index, IndexMut};

impl<K, V> Default for KeyedVecSet<K, V> {
    fn default() -> Self {
        KeyedVecSet::new()
    }
}

impl<K, V, Q> Index<&Q> for KeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("KeyedVecSet: key not found")
    }
}

impl<K, V, Q> IndexMut<&Q> for KeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Borrow<Q>,
    Q: Eq + ?Sized,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.get_mut(key).expect("KeyedVecSet: key not found")
    }
}

impl<K, V> Index<usize> for KeyedVecSet<K, V> {
    type Output = V;

    fn index(&self, index: usize) -> &Self::Output {
        &self.base[index]
    }
}

impl<K, V> IndexMut<usize> for KeyedVecSet<K, V> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.base[index]
    }
}

impl<K, V> Extend<V> for KeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Eq,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = V>,
    {
        let iter = iterable.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            // Round up but make sure we don't overflow when size_hint ==
            // usize::MAX.
            let size_hint = iter.size_hint().0;
            size_hint / 2 + size_hint % 2
        };
        self.reserve(reserve);
        iter.for_each(move |value| {
            self.insert(value);
        });
    }
}

impl<'a, K, V: Clone> Extend<&'a V> for KeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Eq,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = &'a V>,
    {
        self.extend(iterable.into_iter().cloned());
    }
}

impl<K, V> FromIterator<V> for KeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Eq,
{
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let lower = iter.size_hint().0;
        let mut set = KeyedVecSet::with_capacity(lower);
        set.extend(iter);
        set
    }
}

impl<K, V> From<Vec<V>> for KeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Eq,
{
    /// Constructs set from a vector of values.
    ///
    /// When the input contains duplicate keys, the first insertion position is
    /// kept and the last associated value wins — the same rule as
    /// [`insert`][KeyedVecSet::insert], [`extend`][Extend::extend], and
    /// [`FromIterator`].
    ///
    /// **Note**: This conversion has a quadratic complexity because the
    /// conversion preserves order of elements while at the same time having to
    /// make sure no duplicate keys exist. To avoid it, sort and deduplicate
    /// the vector and use [`KeyedVecSet::from_vec_unchecked`] instead.
    fn from(mut vec: Vec<V>) -> Self {
        crate::dedup_keep_last_value(&mut vec, |lhs, rhs| lhs.key() == rhs.key());
        // SAFETY: We've just deduplicated the elements.
        unsafe { Self::from_vec_unchecked(vec) }
    }
}

impl<K, V> From<&[V]> for KeyedVecSet<K, V>
where
    V: Clone + Keyed<K>,
    K: Eq,
{
    fn from(slice: &[V]) -> Self {
        slice.iter().cloned().collect()
    }
}

impl<K, V> From<&mut [V]> for KeyedVecSet<K, V>
where
    V: Clone + Keyed<K>,
    K: Eq,
{
    fn from(slice: &mut [V]) -> Self {
        slice.iter().cloned().collect()
    }
}

impl<K, V, const N: usize> From<[V; N]> for KeyedVecSet<K, V>
where
    V: Keyed<K>,
    K: Eq,
{
    fn from(arr: [V; N]) -> Self {
        KeyedVecSet::from_iter(arr)
    }
}

impl<K, V> PartialEq for KeyedVecSet<K, V>
where
    V: Keyed<K> + PartialEq,
    K: Eq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|value| other.get(value.key()).is_some_and(|v| *value == *v))
    }
}

impl<K, V> Eq for KeyedVecSet<K, V>
where
    V: Keyed<K> + Eq,
    K: Eq,
{
}

#[cfg(test)]
mod test {
    use super::*;
    extern crate alloc;
    use alloc::vec;

    #[derive(Debug, PartialEq, Eq, Clone)]
    struct Entry(i32, &'static str);

    impl Keyed<i32> for Entry {
        fn key(&self) -> &i32 {
            &self.0
        }
    }

    #[test]
    fn default() {
        let set: KeyedVecSet<i32, Entry> = KeyedVecSet::default();
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn index_by_key() {
        let mut set = KeyedVecSet::<i32, Entry>::new();
        set.insert(Entry(1, "a"));
        assert_eq!(set[&1], Entry(1, "a"));
    }

    #[test]
    #[should_panic(expected = "KeyedVecSet: key not found")]
    fn index_by_key_not_found() {
        let set: KeyedVecSet<i32, Entry> = KeyedVecSet::new();
        let _ = &set[&1];
    }

    #[test]
    fn index_mut_by_key() {
        let mut set = KeyedVecSet::<i32, Entry>::new();
        set.insert(Entry(1, "a"));
        set[&1] = Entry(1, "b");
        assert_eq!(set[&1], Entry(1, "b"));
    }

    #[test]
    fn extend() {
        let mut set = KeyedVecSet::<i32, Entry>::new();
        set.extend(vec![Entry(1, "a"), Entry(2, "b")]);
        assert_eq!(set.len(), 2);
        assert_eq!(set[&1], Entry(1, "a"));
    }

    #[test]
    fn from_vec() {
        let set =
            KeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a"), Entry(2, "b"), Entry(1, "c")]);
        assert_eq!(set.len(), 2);
        assert_eq!(set[&1], Entry(1, "c"));
    }

    fn set_via_inserts(entries: &[Entry]) -> KeyedVecSet<i32, Entry> {
        let mut set = KeyedVecSet::new();
        for entry in entries {
            set.insert(entry.clone());
        }
        set
    }

    #[test]
    fn constructor_parity_with_insert() {
        let input = vec![Entry(1, "a"), Entry(2, "b"), Entry(1, "c")];
        let expected = set_via_inserts(&[Entry(1, "a"), Entry(2, "b"), Entry(1, "c")]);

        assert_eq!(KeyedVecSet::from(input.clone()), expected);
        assert_eq!(input.into_iter().collect::<KeyedVecSet<_, _>>(), expected);
        assert_eq!(
            KeyedVecSet::from([Entry(1, "a"), Entry(2, "b"), Entry(1, "c")]),
            expected
        );
        assert_eq!(expected.get(&1), Some(&Entry(1, "c")));
        assert_eq!(expected.as_slice(), &[Entry(1, "c"), Entry(2, "b")]);
    }

    #[test]
    fn extend_parity_with_insert() {
        let mut via_extend = KeyedVecSet::new();
        via_extend.extend(vec![Entry(1, "a"), Entry(2, "b"), Entry(1, "c")]);

        let via_insert = set_via_inserts(&[Entry(1, "a"), Entry(2, "b"), Entry(1, "c")]);
        assert_eq!(via_extend, via_insert);
    }

    #[test]
    fn eq() {
        assert_ne!(
            KeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a")]),
            KeyedVecSet::<i32, Entry>::from(vec![])
        );
        assert_ne!(
            KeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a")]),
            KeyedVecSet::<i32, Entry>::from(vec![Entry(2, "b")])
        );
        assert_eq!(
            KeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a")]),
            KeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a")])
        );
        assert_ne!(
            KeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a")]),
            KeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a"), Entry(2, "b")])
        );
        assert_eq!(
            KeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a"), Entry(2, "b")]),
            KeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a"), Entry(2, "b")])
        );
        assert_eq!(
            KeyedVecSet::<i32, Entry>::from(vec![Entry(1, "a"), Entry(2, "b")]),
            KeyedVecSet::<i32, Entry>::from(vec![Entry(2, "b"), Entry(1, "a")])
        );
    }
}
