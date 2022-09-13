#![doc = include_str!("../README.md")]
#![no_std]
#![warn(missing_docs)]

extern crate alloc;

pub mod map;

#[doc(inline)]
pub use self::map::VecMap;

// The type used to store entries in a `VecMap`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Slot<K, V> {
    key: K,
    value: V,
}

// Accessor methods which can be used in `map` functions.
impl<K, V> Slot<K, V> {
    fn value_ref(&self) -> &V {
        &self.value
    }

    fn value_mut(&mut self) -> &mut V {
        &mut self.value
    }

    fn key_value(self) -> (K, V) {
        (self.key, self.value)
    }

    fn refs(&self) -> (&K, &V) {
        (&self.key, &self.value)
    }

    fn ref_mut(&mut self) -> (&K, &mut V) {
        (&self.key, &mut self.value)
    }
}
