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
pub mod keyed;
pub mod map;
pub mod set;

#[doc(inline)]
pub use self::keyed::{Keyed, KeyedVecSet};
#[doc(inline)]
pub use self::map::VecMap;
#[doc(inline)]
pub use self::set::VecSet;
