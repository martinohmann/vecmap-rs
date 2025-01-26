use super::Slot;
use alloc::boxed::Box;
use core::ops::Deref;
use core::ptr;

#[repr(transparent)]
pub struct Slice<K, V> {
    entries: [Slot<K, V>],
}

impl<K, V> Slice<K, V> {
    pub(super) const fn from_slice(entries: &[Slot<K, V>]) -> &Slice<K, V> {
        // SAFETY: `&[Slot<K, V>]` and `&Slice<K, V>` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<K, V>]>(entries) as *const Slice<K, V>) }
    }

    pub(super) const fn from_mut_slice(entries: &mut [Slot<K, V>]) -> &mut Slice<K, V> {
        // SAFETY: `&mut [Slot<K, V>]` and `&mut Slice<K, V>` have the same memory layout.
        unsafe { &mut *(ptr::from_mut::<[Slot<K, V>]>(entries) as *mut Slice<K, V>) }
    }

    pub(super) fn from_boxed(entries: Box<[Slot<K, V>]>) -> Box<Slice<K, V>> {
        // SAFETY: `A [Slot<K, V>]` and a `Slice<K, V>` are essentially the same thing.
        unsafe { Box::from_raw(Box::into_raw(entries) as *mut Slice<K, V>) }
    }

    fn as_raw_slice(&self) -> &[(K, V)] {
        // SAFETY: `&[Slot<K, V>]` and `&[(K, V)]` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<K, V>]>(&self.entries) as *const [(K, V)]) }
    }
}

impl<K, V> Deref for Slice<K, V> {
    type Target = [(K, V)];

    fn deref(&self) -> &Self::Target {
        self.as_raw_slice()
    }
}
