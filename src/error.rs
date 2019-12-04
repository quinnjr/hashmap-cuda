// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use failure::Fail;

use core::{
  convert::From,
  fmt::{ Debug, Display, Formatter, Result as FmtResult },
};

/// The error type for `try_reserve` methods.
///
/// TODO: Consider removing and just using `CollectionAllocError`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TryReserveError {
  /// Error due to the computed capacity exceeding the collection's maximum
  /// (usually `isize::MAX` bytes).
  CapacityOverflow,
  /// The memory allocator returned an error
  AllocError {
    /// The layout of allocation request that failed
    layout: ::core::alloc::Layout,
    non_exhaustive: (),
  }
}

/// Augments `AllocErr` with a `CapacityOverflow` variant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CollectionAllocErr {
  /// Error due to the computed capacity exceeding the collection's maximum
  /// (usually `isize::MAX` bytes).
  CapacityOverflow,
  /// Error due to the allocator.
  AllocErr {
    /// The layout of the allocation request that failed.
    layout: ::core::alloc::Layout,
  }
}

macro_rules! error_enumeration {
  (
    $(
      $( #[$meta:meta] )?
      $name:ident => $cause:path
    ),*
  ) => {
    #[derive(Clone, Debug, Fail)]
    pub enum Error {
      $(
        $(#[$meta])?
        $name(#[fail(cause)] $cause),
      )*
    }

    $(
      $(#[$meta])?
      impl From<$cause> for Error {
        fn from(err: $cause) -> Self { Self::$name(err) }
      }
    )*

    impl ::core::fmt::Display for Error {
      fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        write!(f, "{}", self)
      }
    }
  };
}

error_enumeration! {
  AllocLayout => ::core::alloc::LayoutErr,
  CellBorrow => ::core::cell::BorrowError,
  Fail => failure::Error,
  Format => ::core::fmt::Error,
  ParseInt => ::core::num::ParseIntError,
  ParseFloat => ::core::num::ParseFloatError,
  TryFromInt => ::core::num::TryFromIntError,
  TryReserve => self::TryReserveError,
  CollectionAlloc => self::CollectionAllocErr,
  CurandError => cuda::rand::CurandError,
  CuError => cuda::driver::CuError,
  CudaRuntimeError => cuda::runtime::CudaError,
  // #[cfg(feature = "std")] BoxedError => ::std::boxed::Box<dyn ::std::error::Error>,
  #[cfg(feature = "std")] FromString => ::std::string::String
}
