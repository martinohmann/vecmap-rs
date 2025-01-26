use super::Slot;
use alloc::boxed::Box;
use core::ops::Deref;
use core::ptr;

#[repr(transparent)]
pub struct Slice<T> {
    entries: [Slot<T>],
}

impl<T> Slice<T> {
    pub(super) const fn from_slice(entries: &[Slot<T>]) -> &Self {
        // SAFETY: `&[Slot<T>]` and `&Slice<T>` have the same memory layout because `Slice<T>` is
        // just a transparent wrapper.
        unsafe { &*(ptr::from_ref::<[Slot<T>]>(entries) as *const Self) }
    }

    pub(super) const fn from_mut_slice(entries: &mut [Slot<T>]) -> &mut Self {
        // SAFETY: `&mut [Slot<T>]` and `&mut Slice<T>` have the same memory layout because `Slice<T>` is
        // just a transparent wrapper.
        unsafe { &mut *(ptr::from_mut::<[Slot<T>]>(entries) as *mut Self) }
    }

    pub(super) fn from_boxed(entries: Box<[Slot<T>]>) -> Box<Self> {
        // SAFETY: `A [Slot<T>]` and a `Slice<T>` are essentially the same thing.
        unsafe { Box::from_raw(Box::into_raw(entries) as *mut Self) }
    }

    fn as_raw_slice(&self) -> &[T] {
        // SAFETY: `&[Slot<T>]` and `&[T]` have the same memory layout.
        unsafe { &*(ptr::from_ref::<[Slot<T>]>(&self.entries) as *const [T]) }
    }
}

impl<T> Deref for Slice<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_raw_slice()
    }
}
