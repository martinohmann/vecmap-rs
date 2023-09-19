# Changelog

## [0.1.12](https://github.com/martinohmann/vecmap-rs/compare/v0.1.11...v0.1.12) (2023-09-19)


### Features

* **map:** add `insert_at` ([7cbef1d](https://github.com/martinohmann/vecmap-rs/commit/7cbef1d3ee44c3002a9bdfe57117b9d315845fee))
* **map:** impl `ExactSizeIterator` and `Debug` for `Drain` ([aca02b4](https://github.com/martinohmann/vecmap-rs/commit/aca02b4327d768e48ff6f9fada94ea98eac3c61d))


### Bug Fixes

* **set:** remove unnecessary trait bounds from `Drain` ([5643f73](https://github.com/martinohmann/vecmap-rs/commit/5643f737a487d7045a7a170b383c36796f977786))

## [0.1.11](https://github.com/martinohmann/vecmap-rs/compare/v0.1.10...v0.1.11) (2023-06-23)


### Features

* add `swap_indices` ([a219c7f](https://github.com/martinohmann/vecmap-rs/commit/a219c7f32c636a3d4721948810d600737c13cb82))
* add `truncate` ([a1e1625](https://github.com/martinohmann/vecmap-rs/commit/a1e1625ad70c33e2af3580807647c1514af686fc))

## [0.1.10](https://github.com/martinohmann/vecmap-rs/compare/v0.1.9...v0.1.10) (2023-03-18)


### Features

* **map:** add `MutableKeys` trait ([#12](https://github.com/martinohmann/vecmap-rs/issues/12)) ([a2fc16b](https://github.com/martinohmann/vecmap-rs/commit/a2fc16b2393d9786ee5cba58f98d49367721d689))

## [0.1.9](https://github.com/martinohmann/vecmap-rs/compare/v0.1.8...v0.1.9) (2022-12-13)


### Bug Fixes

* remove unnecessary usages of `mem::transmute` ([41d90b6](https://github.com/martinohmann/vecmap-rs/commit/41d90b6c8a5cbae5be56dd0b4ae12cda4968eff7))

## [0.1.8](https://github.com/martinohmann/vecmap-rs/compare/v0.1.7...v0.1.8) (2022-10-30)


### Features

* **set:** implement `Clone` for `IntoIter` ([e78d5ee](https://github.com/martinohmann/vecmap-rs/commit/e78d5eea597703f25ef02965f2f55bf23faac647))


### Miscellaneous

* enable `clippy::pedantic` warnings ([d61b8f8](https://github.com/martinohmann/vecmap-rs/commit/d61b8f83572973b500a5603239d140d2d9faba1d))

## [0.1.7](https://github.com/martinohmann/vecmap-rs/compare/v0.1.6...v0.1.7) (2022-10-11)


### Miscellaneous

* **test:** switch to `serde_test` ([a980545](https://github.com/martinohmann/vecmap-rs/commit/a9805459bc7997e0cdd630653bcc01be3923005f))

## [0.1.6](https://github.com/martinohmann/vecmap-rs/compare/v0.1.5...v0.1.6) (2022-10-02)


### Features

* add `as_slice`, `to_vec` and `into_vec` methods ([3f1906d](https://github.com/martinohmann/vecmap-rs/commit/3f1906d45f0452ddb625a587f27adf0df47b64a8))


### Bug Fixes

* remove some needless borrows ([29bd06e](https://github.com/martinohmann/vecmap-rs/commit/29bd06e9634b181eeba0e23da319035a153794e7))

## [0.1.5](https://github.com/martinohmann/vecmap-rs/compare/v0.1.4...v0.1.5) (2022-09-21)


### Features

* **entry:** add `into_key` method to `OccupiedEntry` ([f94cbc3](https://github.com/martinohmann/vecmap-rs/commit/f94cbc376c053f9055ee2ac1a6f78eccc46189e1))

## [0.1.4](https://github.com/martinohmann/vecmap-rs/compare/v0.1.3...v0.1.4) (2022-09-18)


### Features

* add sort methods ([b443fe3](https://github.com/martinohmann/vecmap-rs/commit/b443fe37ab3fcf56bb9a15032c2a85324a67dfaf))
* implement `Clone` for all immutable iterators ([86478ba](https://github.com/martinohmann/vecmap-rs/commit/86478ba668ce7c4641f3ce76b9103b1da2b457ac))

## [0.1.3](https://github.com/martinohmann/vecmap-rs/compare/v0.1.2...v0.1.3) (2022-09-17)


### Features

* add `remove_index` ([fbf9e96](https://github.com/martinohmann/vecmap-rs/commit/fbf9e9674ffc3dafcc59e351a612054c508a9c67))
* add `split_off` ([ef05a94](https://github.com/martinohmann/vecmap-rs/commit/ef05a94571dff910b5f53d8f277ef23b840f7d42))
* add `VecSet` ([#5](https://github.com/martinohmann/vecmap-rs/issues/5)) ([52cbc1e](https://github.com/martinohmann/vecmap-rs/commit/52cbc1eb1e90abe2c3b453f7957b109465c8e5bb))

## [0.1.2](https://github.com/martinohmann/vecmap-rs/compare/v0.1.1...v0.1.2) (2022-09-15)


### Features

* add `drain` ([380b801](https://github.com/martinohmann/vecmap-rs/commit/380b801c75df8b847d90186d499c4a829b56331a))
* add `retain` ([da11a0a](https://github.com/martinohmann/vecmap-rs/commit/da11a0ad069bcef7d47275453f2844a7858bde14))
* add `shrink_to_fit` and `shrink_to` ([e38cb08](https://github.com/martinohmann/vecmap-rs/commit/e38cb08c0ed00a8cdad0e80ecff629e37582f6ec))


### Bug Fixes

* manually implement `PartialEq` and `Eq` ([6809137](https://github.com/martinohmann/vecmap-rs/commit/680913709db23fa14e592af5c6f3a362f4e4680a))


### Miscellaneous

* add documentation link to `Cargo.toml` ([4c76dc1](https://github.com/martinohmann/vecmap-rs/commit/4c76dc156b34e2fe2580035f9c3c67c645546439))

## [0.1.1](https://github.com/martinohmann/vecmap-rs/compare/v0.1.0...v0.1.1) (2022-09-14)


### Features

* add `vecmap!` macro ([0d188cf](https://github.com/martinohmann/vecmap-rs/commit/0d188cfc114eb9fba123fbbcb261a48ee717c908))


### Miscellaneous

* fix crate categories ([d22090d](https://github.com/martinohmann/vecmap-rs/commit/d22090db7a10bfe9233b7ba97c47752777ffbfaa))
* fix license identifier ([4f07cb3](https://github.com/martinohmann/vecmap-rs/commit/4f07cb30dc567153fa3ef71039273f01d4003194))

## 0.1.0 (2022-09-14)


### Features

* add `Entry` API ([720e480](https://github.com/martinohmann/vecmap-rs/commit/720e480782409ba0c6939b1647464e6d01a51302))
* add `insert_full` ([e8fec92](https://github.com/martinohmann/vecmap-rs/commit/e8fec923e5e5937725dc0bb1e7538740aa4e2273))
* add `serde` feature ([618c7be](https://github.com/martinohmann/vecmap-rs/commit/618c7be4753a3d929769b27a81556d352dda21f0))
* add `VecMap` and basic operations ([18f244f](https://github.com/martinohmann/vecmap-rs/commit/18f244f5d14e86965d7fefd7bbe95cca9f7e1765))
* add iterators ([4a016c8](https://github.com/martinohmann/vecmap-rs/commit/4a016c8785c77edb4b4a15ca6f5119e2fc7dcdaf))


### Miscellaneous

* dual-license under MIT and Apache 2.0 ([d7fe6ec](https://github.com/martinohmann/vecmap-rs/commit/d7fe6ec3a06efc4229f6017360de70f4f954e5f6))
* initial commit ([63dbc94](https://github.com/martinohmann/vecmap-rs/commit/63dbc946cb3f8c647e39612d53b19cf4493e8f1a))
* prepare release ([0cb9f49](https://github.com/martinohmann/vecmap-rs/commit/0cb9f497de2d088042c00a86568796d424c6841f))
