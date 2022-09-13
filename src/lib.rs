#![doc = include_str!("../README.md")]
#![no_std]
#![warn(missing_docs)]

extern crate alloc;

pub mod map;

#[doc(inline)]
pub use self::map::VecMap;
