//! Ethereum ABI encoding decoding library.
#![warn(missing_docs)]
#![no_std]

#![feature(slice_concat_ext)]

#[macro_use]
extern crate sgx_tstd as std;
/*
#![feature(alloc)]
#[macro_use]
extern crate alloc;
*/
extern crate rustc_hex as hex;
extern crate serde;
extern crate serde_json;
extern crate tiny_keccak;

#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate error_chain;

extern crate ethereum_types;

use std::vec::Vec;
//use alloc::vec::Vec;

pub mod param_type;
pub mod token;
mod constructor;
mod contract;
mod decoder;
mod encoder;
mod errors;
mod event;
mod event_param;
mod filter;
mod function;
mod log;
mod operation;
mod param;
pub mod signature;
mod util;

pub use param_type::ParamType;
pub use constructor::Constructor;
pub use contract::{Contract, Functions, Events};
pub use token::Token;
pub use errors::{Error, ErrorKind, Result, ResultExt};
pub use encoder::encode;
pub use decoder::decode;
pub use filter::{Topic, TopicFilter, RawTopicFilter};
pub use function::Function;
pub use param::Param;
pub use log::{Log, RawLog, LogParam};
pub use event::Event;
pub use event_param::EventParam;

/// ABI address.
pub type Address = ethereum_types::Address;

/// ABI fixed bytes.
pub type FixedBytes = Vec<u8>;

/// ABI bytes.
pub type Bytes = Vec<u8>;

/// ABI signed integer.
pub type Int = ethereum_types::U256;

/// ABI unsigned integer.
pub type Uint = ethereum_types::U256;

/// Commonly used FixedBytes of size 32
pub type Hash = ethereum_types::H256;
