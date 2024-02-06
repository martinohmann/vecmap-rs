# vecset

[![Build Status](https://github.com/youknowone/vecset/workflows/ci/badge.svg)](https://github.com/youknowone/vecset/actions?query=workflow%3Aci)
[![crates.io](https://img.shields.io/crates/v/vecset)](https://crates.io/crates/vecset)
[![docs.rs](https://img.shields.io/docsrs/vecset)](https://docs.rs/vecset)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

A vector-based sorted map and set implementation with zero dependencies and
support for `#![no_std]`.

Map keys are required to form a total order.

## Cargo features

The following features are available:

* `serde`: Provides [`Serialize`](https://docs.rs/serde/latest/serde/ser/trait.Serialize.html)
  and [`Deserialize`](https://docs.rs/serde/latest/serde/de/trait.Deserialize.html)
  implementations for `VecMap` and `VecSet`. This feature is disabled by
  default. Enabling it will pull in `serde` as a dependency.

## License

The source code of vecset is licensed under either of [Apache License,
Version 2.0](LICENSE-APACHE.md) or [MIT license](LICENSE-MIT) at your option.
