use super::VecSet;
use alloc::vec::Vec;

impl<T> Default for VecSet<T> {
    fn default() -> Self {
        VecSet::new()
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
        let iter = iterable.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            (iter.size_hint().0 + 1) / 2
        };
        self.reserve(reserve);
        iter.for_each(move |elem| {
            self.insert(elem);
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
        self.extend(iterable.into_iter().cloned());
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
        let iter = iter.into_iter();
        let lower = iter.size_hint().0;
        let mut map = VecSet::with_capacity(lower);
        map.extend(iter);
        map
    }
}

impl<T> From<Vec<T>> for VecSet<T>
where
    T: Eq,
{
    fn from(vec: Vec<T>) -> Self {
        VecSet::from_iter(vec)
    }
}

impl<T> From<&[T]> for VecSet<T>
where
    T: Clone + Eq,
{
    fn from(slice: &[T]) -> Self {
        VecSet::from_iter(slice.to_vec())
    }
}

impl<T> From<&mut [T]> for VecSet<T>
where
    T: Clone + Eq,
{
    fn from(slice: &mut [T]) -> Self {
        VecSet::from_iter(slice.to_vec())
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
