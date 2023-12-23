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
#[repr(transparent)]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Slot<K, V> {
    entry: (K, V),
}

// Accessor methods which can be used in `map` functions.
impl<K, V> Slot<K, V> {
    #[inline]
    fn new(key: K, value: V) -> Self {
        Slot {
            entry: (key, value),
        }
    }
}

// Accessor methods which can be used in `map` functions.
impl<K, V> Slot<K, V> {
    #[inline]
    fn key_ref(&self) -> &K {
        &self.entry.0
    }

    #[inline]
    fn key_mut(&mut self) -> &mut K {
        &mut self.entry.0
    }

    #[inline]
    fn key(self) -> K {
        self.entry.0
    }

    #[inline]
    fn value_ref(&self) -> &V {
        &self.entry.1
    }

    #[inline]
    fn value_mut(&mut self) -> &mut V {
        &mut self.entry.1
    }

    #[inline]
    fn value(self) -> V {
        self.entry.1
    }

    #[inline]
    fn refs(&self) -> (&K, &V) {
        (&self.entry.0, &self.entry.1)
    }

    #[inline]
    fn ref_mut(&mut self) -> (&K, &mut V) {
        (&self.entry.0, &mut self.entry.1)
    }

    #[inline]
    fn muts(&mut self) -> (&mut K, &mut V) {
        (&mut self.entry.0, &mut self.entry.1)
    }

    #[inline]
    fn key_value(self) -> (K, V) {
        (self.entry.0, self.entry.1)
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

// https://github.com/martinohmann/vecmap-rs/issues/18
//
// If `Slot<K, V>` does not have the same memory layout as `(K, V)`, e.g. due to possible field
// reordering, this test will:
//
// - Segfault with "SIGSEGV: invalid memory reference" in the `unsafe` block in `VecMap::as_slice`
//   when run via `cargo test`.
// - Trigger a miri error when run via `cargo +nightly miri test`.
#[test]
fn issue_18() {
    use alloc::string::String;
    use core::{fmt, mem};

    fn test<K, V>(slice: &[(K, V)])
    where
        K: Clone + Eq + fmt::Debug,
        V: Clone + PartialEq + fmt::Debug,
    {
        assert_eq!(mem::size_of::<Slot<K, V>>(), mem::size_of::<(K, V)>());
        assert_eq!(mem::align_of::<Slot<K, V>>(), mem::align_of::<(K, V)>());

        let map = VecMap::from(slice);
        assert_eq!(map.as_slice(), slice);
    }

    test(&[(1i64, String::from("foo")), (2, String::from("bar"))]);
    test(&[(String::from("foo"), 1i64), (String::from("bar"), 2)]);
    test(&[(true, 1i64), (false, 2)]);
    test(&[(1i64, true), (2, false)]);
}
