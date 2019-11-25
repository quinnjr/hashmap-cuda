// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

//! `hashmap-cuda` prelude module for loading necessary dependencies.
//!
//! Inclusions overlap with some exports from `core::prelude::v1` in a
//! `#![no_std]` application and `std::prelude::v1` when
//! the standard library is available for completeness.
cfg_if::cfg_if! {
  if #[cfg(feature = "std")] {
    #[allow(deprecated, unused_imports)]
    pub(crate) use ::std::{
      alloc::Layout,
      borrow::Borrow,
      cell::{ RefCell, RefMut },
      cmp::{ Eq, Ord, PartialEq, PartialOrd },
      convert::{ AsMut, AsRef, From, Into, TryFrom, TryInto },
      default::Default,
      // ffi,
      fmt::{ Debug, Display, Error as FmtError, Formatter, Result as FmtResult }
      future::Future,
      hash::{ BuildHasher, BuildHasherDefault, Hash, Hasher },
      iter::{ FromIterator, FusedIterator, IntoIterator },
      marker::{ PhantomData },
      ops::Index,
      process,
      ptr,
      rc,
      result::Result as StdResult,
      sync::{ atomic, Arc, mpsc, Mutex, RwLock },
      // task,
      thread::{ self, Result as ThreadResult },
      time
    };
  } else {
    #[allow(deprecated, unused_imports)]
    pub use(crate) ::core::{
      alloc::Layout,
      borrow::Borrow,
      clone::Clone,
      cmp::{ Eq, Ord, PartialEq, PartialOrd },
      convert::{ AsMut, AsRef, From, Into, TryFrom, TryInto },
      default::Defualt,
      fmt::{ Debug, Display, Error as FmtError, Formatter, Result as FmtResult },
      future::Future,
      hash::{ BuildHasher, BuildHasherDefault, Hash, Hasher, SipHasher },
      iter::{ FromIterator, FusedIterator, IntoIterator },
      mem,
      ops::Index,
      result::Result as StdResult,
      time
    }
  }
}
