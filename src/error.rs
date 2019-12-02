// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use failure::Fail;

use core::{
  convert::From,
  fmt::{ Debug, Display, Formatter, Result as FmtResult },
};

/// The error type for `try_reserve` methods.
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
  };
}

error_enumeration! {
  AllocLayout => ::core::alloc::LayoutErr,
  // #[cfg(feature = "std")] BoxedError => ::std::boxed::Box<dyn ::std::error::Error>,
  CellBorrow => ::core::cell::BorrowError,
  Fail => failure::Error,
  Format => ::core::fmt::Error,
  ParseInt => ::core::num::ParseIntError,
  ParseFloat => ::core::num::ParseFloatError,
  // #[cfg(feature = "std")] StringError => ::std::string::String,
  TryFromInt => ::core::num::TryFromIntError,
  TryReserve => self::TryReserveError,
  CollectionAlloc => self::CollectionAllocErr,
  CurandError => cuda::rand::CurandError,
  CuError => cuda::driver::CuError,
  CudaRuntimeError => cuda::runtime::CudaError

}
