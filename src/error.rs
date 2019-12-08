// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use failure::{ Backtrace, Context, Fail};

use core::{
  convert::From,
  fmt::{ Debug, Display, Formatter, Result as FmtResult }
};

macro_rules! error_enumeration {
  (
    $kind_name:ident,
    $(
      $(#[$meta:meta])?
      $name:ident => $error:path
    ),*
  ) => {
    /// Generated custom [`ErrorKind`] enum.
    /// [`ErrorKind`]: https://boats.gitlab.io/failure/error-errorkind.html
    #[derive(Debug, Fail)]
    pub enum $kind_name {
      $(
        /// Variant $name
        $(#[$meta])?
        $name(#[cause] $error),
      )*
    }

    $(
      $(#[$meta])?
      impl From<$error> for $kind_name {
        fn from(err: $error) -> Self { Self::$name(err) }
      }
    )*

    impl Display for $kind_name {
      fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        write!(f, "{}", self)
      }
    }
  }
}

error_enumeration! {
  ErrorKind,
  Fail => failure::Error,
  AllocLayout => ::core::alloc::LayoutErr,
  CellBorrow => ::core::cell::BorrowError,
  Format => ::core::fmt::Error,
  ParseInt => ::core::num::ParseIntError,
  ParseFloat => ::core::num::ParseFloatError,
  TryFromInt => ::core::num::TryFromIntError,
  TryReserve => self::TryReserveError,
  CollectionAlloc => self::CollectionAllocErr,
  CurandError => self::CurandErrorExt,
  CudaRuntimeError => self::CudaErrorExt,
  CudaDriverError => self::CuErrorExt
}

/// The error type for `try_reserve` methods.
///
/// TODO: Consider removing and just using `CollectionAllocError`.
#[derive(Clone, Debug, Eq, PartialEq, Fail)]
pub enum TryReserveError {
  /// Error due to the computed capacity exceeding the collection's maximum
  /// (usually `isize::MAX` bytes).
  #[fail(display = "Capactity overflow")]
  CapacityOverflow,
  /// The memory allocator returned an error
  #[fail(display = "Memory allocator returned an error")]
  AllocError {
    /// The layout of allocation request that failed
    layout: ::core::alloc::Layout,
    /// Non-exhaustive unit type
    non_exhaustive: (),
  }
}

/// Augments `AllocErr` with a `CapacityOverflow` variant.
#[derive(Clone, Debug, Eq, PartialEq, Fail)]
pub enum CollectionAllocErr {
  /// Error due to the computed capacity exceeding the collection's maximum
  /// (usually `isize::MAX` bytes).
  #[fail(display = "Capactity overflow")]
  CapacityOverflow,
  /// Error due to the allocator.
  #[fail(display = "Memory allocator returned an error")]
  AllocErr {
    /// The layout of the allocation request that failed.
    layout: ::core::alloc::Layout,
  }
}

impl From<cuda::rand::CurandError> for ErrorKind {
  fn from(e: cuda::rand::CurandError) -> Self {
    Self::CurandError(CurandErrorExt { inner: e })
  }
}

impl From<cuda::driver::CuError> for ErrorKind {
  fn from(e: cuda::driver::CuError) -> Self {
    Self::CudaDriverError(CuErrorExt { inner: e })
  }
}

impl From<cuda::runtime::CudaError> for ErrorKind {
  fn from(e: cuda::runtime::CudaError) -> Self {
    Self::CudaRuntimeError(CudaErrorExt { inner: e })
  }
}

/// Temporary error implementation for [`CurandError`] until
/// proper support for the `Error` trait is implemented in
/// `cuda`.
/// [`CurandError`]: https://docs.rs/cuda/0.4.0-pre.2/cuda/rand/struct.CurandError.html
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CurandErrorExt {
  inner: cuda::rand::CurandError
}

impl Fail for CurandErrorExt {
  fn name(&self) -> Option<&str> {
    self.inner.get_name()
  }

  fn cause(&self) -> Option<&dyn Fail> { None }

  fn backtrace(&self) -> Option<&Backtrace> { None }

  fn context<D>(self, context: D) -> Context<D>
    where D: Display + Send + Sync + 'static, Self: Sized
  {
    Context::new(context)
  }
}

impl Display for CurandErrorExt {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    write!(f, "{}: {}", self.inner.get_code(), self.inner.get_name().unwrap())
  }
}

/// Temporary error implementation for [`CuError`] until
/// proper support for the `Error` trait is implemented in
/// `cuda`.
/// [`CuError`]: https://docs.rs/cuda/0.4.0-pre.2/cuda/driver/struct.CuError.html
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CuErrorExt {
  inner: cuda::driver::CuError
}

impl Fail for CuErrorExt {
  fn name(&self) -> Option<&str> {
    Some(self.inner.get_name())
  }

  fn cause(&self) -> Option<&dyn Fail> { None }

  fn backtrace(&self) -> Option<&Backtrace> { None }

  fn context<D>(self, context: D) -> Context<D>
    where D: Display + Send + Sync + 'static, Self: Sized
  {
    Context::new(context)
  }
}

impl Display for CuErrorExt {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    write!(f, "{} {}: {}", self.inner.get_code(), self.inner.get_name(),
      self.inner.get_desc())
  }
}

/// Temporary error implementation for [`CudaError`] until
/// proper support for the `Error` trait is implemented in
/// `cuda`.
/// [`CudaError`]: https://docs.rs/cuda/0.4.0-pre.2/cuda/runtime/struct.CudaError.html
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CudaErrorExt {
  inner: cuda::runtime::CudaError
}

impl Fail for CudaErrorExt {
  #[cfg(feature = "std")]
  fn name(&self) -> Option<&str> {
    let raw_s = unsafe { cuda::ffi::cuda_runtime_api::cudaGetErrorString(self.inner.0) };
    if raw_s.is_null() {
      return Some("(null)")
    }
    let cs = unsafe { std::ffi::CStr::from_ptr(raw_s) };
    let s = match cs.to_str() {
      Ok(s) => s,
      Err(_) => "(Invalid utf-8)"
    };
    Some(s)
  }

  #[cfg(not(feature = "std"))]
  fn name(&self) -> Option<&str> {
    Some("(CudaError)")
  }

  fn cause(&self) -> Option<&dyn Fail> { None }

  fn backtrace(&self) -> Option<&Backtrace> { None }

  fn context<D>(self, context: D) -> Context<D>
    where D: Display + Send + Sync + 'static, Self: Sized
  {
    Context::new(context)
  }
}

impl Display for CudaErrorExt {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    write!(f, "{}: {}", self.inner.get_code(), self.inner.get_string())
  }
}
