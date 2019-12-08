// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use core::{
  hash::{ BuildHasher, Hasher }
};

use crate::external::SipHasher13;

#[cfg(feature = "ahash")]
/// Use [`ahash`] as the default hash builder when
/// the ahash feature is present
pub type DefaultHashBuilder = ahash::ABuildHasher;

#[cfg(not(feature = "ahash"))]
/// Default hash builder when not using [`ahash`].
pub enum DefaultHashBuilder {}

/// The default [`Hasher`] used by [`RandomState`].
///
/// TODO: Consider reimplementing hasher with CUDA-specific logic.
///
/// [`RandomState`]: struct.RandomState.html
/// [`Hasher`]: ../../hash/trait.Hasher.html
#[derive(Clone, Debug)]
pub struct DefaultHasher(pub SipHasher13);

impl DefaultHasher {
  /// Creates a new `DefaultHasher`.
  ///
  /// This hasher is not guaranteed to be the same as all other
  /// `DefaultHasher` instances, but is the same as all
  /// other `DefaultHasher` instances created
  /// through `new` or `default`.
  pub fn new() -> Self {
    Self(SipHasher13::new_with_keys(0, 0))
  }
}

impl Default for DefaultHasher {
  /// Creates a new `DefaultHasher` using `new`.
  /// See its documentation for more.
  fn default() -> Self {
    DefaultHasher::new()
  }
}

impl Hasher for DefaultHasher {
  fn write(&mut self, msg: &[u8]) {
    self.0.write(msg)
  }

  fn finish(&self) -> u64 {
    self.0.finish()
  }
}

impl BuildHasher for DefaultHasher {
  type Hasher = SipHasher13;
  #[inline]
  fn build_hasher(&self) -> Self::Hasher {
    Self::Hasher::new()
  }
}
