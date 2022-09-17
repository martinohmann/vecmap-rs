# vecmap-rs

[![Build Status](https://github.com/martinohmann/vecmap-rs/workflows/ci/badge.svg)](https://github.com/martinohmann/vecmap-rs/actions?query=workflow%3Aci)
[![crates.io](https://img.shields.io/crates/v/vecmap-rs)](https://crates.io/crates/vecmap-rs)
[![docs.rs](https://img.shields.io/docsrs/vecmap-rs)](https://docs.rs/vecmap-rs)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A vector-based ordered map and set implementations with zero dependencies and
support for `#![no_std]`.

Map keys are not required to be hashable and do not need to form a total order.
Therefore, `VecMap<K, V>` and `VecSet<T>` can be used with key types which
neither implement `Hash` nor `Ord`.

Since vecmap-rs is a `Vec<(K, V)>` under the hood, worst case lookup and
insertion performance is `O(n)` and scales with the number of map entries.
Thus, its main use case are small collections with unhashable keys.

For key types that implement `Hash` and `Ord` consider using a map or set
implementation with better performance such as
[`HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html)/[`HashSet`](https://doc.rust-lang.org/std/collections/struct.HashSet.html)
and
[`BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html)/[`BTreeSet`](https://doc.rust-lang.org/std/collections/struct.BTreeSet.html)
from the standard library or popular alternatives like
[`IndexMap`](https://docs.rs/indexmap/latest/indexmap/map/struct.IndexMap.html)/[`IndexSet`](https://docs.rs/indexmap/latest/indexmap/set/struct.IndexMap.html).

## Cargo features

The following features are available:

* `serde`: Provides `Serialize` and `Deserialize` implementations for `VecMap`
  and `VecSet`. This feature is disabled by default. Enabling it will pull in
  `serde` as a dependency.

## License

The source code of vecmap-rs is licensed under either of [Apache License,
Version 2.0](LICENSE-APACHE.md) or [MIT license](LICENSE-MIT) at your option.
