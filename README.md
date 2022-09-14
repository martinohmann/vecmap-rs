# vecmap-rs

[![Build Status](https://github.com/martinohmann/vecmap-rs/workflows/ci/badge.svg)](https://github.com/martinohmann/vecmap-rs/actions?query=workflow%3Aci)

A vector-based ordered map implementation with support for `#![no_std]`.

Map keys are not required to be hashable and do not need to form a total order.
Therefore, `VecMap<K, V>` can be used with key types which neither implement
`Hash` nor `Ord`.

Since vecmap-rs is a `Vec<(K, V)>` under the hood, worst case lookup and
insertion performance is `O(n)` and scales with the number of map entries.
Thus, its main use case are small collections with unhashable keys.

For key types that implement `Hash` and `Ord` consider using a map implementation with better performance such as
[`HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html) and
[`BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html) from the standard library or popular alternatives like [`IndexMap`](https://docs.rs/indexmap/latest/indexmap/).

## License

The source code of vecmap-rs is licensed under either of [Apache License,
Version 2.0](LICENSE-APACHE.md) or [MIT license](LICENSE-MIT) at your option.
