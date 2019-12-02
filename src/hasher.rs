// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

#[allow(deprecated)]
use core::hash::{
  Hasher,
  SipHasher
};

#[cfg(feature = "ahash")]
pub type DefaultHashBuilder = ahash::ABuildHasher;

#[cfg(not(feature = "ahash"))]
pub enum DefaultHashBuilder {}

/// The default [`Hasher`] used by [`RandomState`].
///
/// The internal algorithm is not specified, and so it and
/// its hashes should
/// not be relied upon over releases.
///
/// [`RandomState`]: struct.RandomState.html
/// [`Hasher`]: ../../hash/trait.Hasher.html
#[allow(deprecated)]
#[derive(Clone, Debug)]
pub struct DefaultHasher(pub SipHasher);

impl DefaultHasher {
  /// Creates a new `DefaultHasher`.
  ///
  /// This hasher is not guaranteed to be the same as all other
  /// `DefaultHasher` instances, but is the same as all
  /// other `DefaultHasher` instances created
  /// through `new` or `default`.
  #[allow(deprecated)]
  pub fn new() -> Self {
    DefaultHasher(SipHasher::new_with_keys(0, 0))
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
