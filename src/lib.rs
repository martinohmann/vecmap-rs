#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![warn(missing_docs)]
#![warn(clippy::pedantic)]
#![allow(
    clippy::match_wildcard_for_single_variants,
    clippy::module_name_repetitions,
    clippy::must_use_candidate,
    clippy::return_self_not_must_use
)]
#![no_std]

extern crate alloc;

#[macro_use]
mod macros;
pub mod map;
pub mod set;

#[doc(inline)]
pub use self::map::VecMap;
#[doc(inline)]
pub use self::set::VecSet;
use alloc::vec::Vec;

// The type used to store entries in a `VecMap`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Slot<K, V> {
    key: K,
    value: V,
}

// Accessor methods which can be used in `map` functions.
impl<K, V> Slot<K, V> {
    fn key_ref(&self) -> &K {
        &self.key
    }

    fn key_mut(&mut self) -> &mut K {
        &mut self.key
    }

    fn key(self) -> K {
        self.key
    }

    fn value_ref(&self) -> &V {
        &self.value
    }

    fn value_mut(&mut self) -> &mut V {
        &mut self.value
    }

    fn value(self) -> V {
        self.value
    }

    fn refs(&self) -> (&K, &V) {
        (&self.key, &self.value)
    }

    fn ref_mut(&mut self) -> (&K, &mut V) {
        (&self.key, &mut self.value)
    }

    fn muts(&mut self) -> (&mut K, &mut V) {
        (&mut self.key, &mut self.value)
    }

    fn key_value(self) -> (K, V) {
        (self.key, self.value)
    }
}

// Trait for obtaining access to the entries in a collection.
trait Entries {
    type Entry;

    fn as_entries(&self) -> &[Self::Entry];

    fn as_entries_mut(&mut self) -> &mut [Self::Entry];

    fn into_entries(self) -> Vec<Self::Entry>;
}

/// Deduplicate elements in an unsorted vector.
fn dedup<T>(vec: &mut Vec<T>, eq_fn: impl Fn(&T, &T) -> bool) {
    let mut out = 1;
    let len = vec.len();
    for i in 1..len {
        if (0..i).all(|j| !eq_fn(&vec[i], &vec[j])) {
            vec.swap(out, i);
            out += 1;
        }
    }
    vec.truncate(out);
}

#[test]
fn test_dedup() {
    fn test(want: &[u32], arr: &[u32]) {
        let mut vec = arr.to_vec();
        dedup(&mut vec, |i, j| i == j);
        assert_eq!(want, vec.as_slice());
    }

    test(&[], &[]);
    test(&[1], &[1]);
    test(&[1], &[1, 1]);
    test(&[1], &[1, 1, 1]);
    test(&[3, 1, 2], &[3, 1, 2]);
    test(&[3, 1, 2], &[3, 1, 2, 1, 2, 3]);
}
