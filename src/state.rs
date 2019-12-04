// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use crate::{
  hasher::DefaultHasher,
  raw
};

#[allow(deprecated)]
use core::{
  cell::Cell,
  fmt::{ Debug, Display, Formatter, Result as FmtResult },
  hash::{ BuildHasher, SipHasher }
};

/// `RandomState` is the default state for [`HashMap`] types.
///
/// A particular instance `RandomState` will create the
/// same instances of [`Hasher`], but the hashers created
/// by two different `RandomState` instances are unlikely to
/// produce the same result for the same values.
///
/// [`HashMap`]: struct.HashMap.html
/// [`Hasher`]: ../../hash/trait.Hasher.html
///
/// # Examples
///
/// ```
/// use hashmap_cuda::{ HashMap, RandomState };
///
/// let s = RandomState::new();
/// let mut map = HashMap::with_hasher(s);
/// map.insert(1, 2);
/// ```
#[derive(Clone)]
pub struct RandomState {
  k0: u64,
  k1: u64
}

impl RandomState {
  /// Constructs a new `RandomState` that is initialized with
  /// random keys.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cude::RandomState;
  ///
  /// let s = RandomState::new();
  /// ```
  #[allow(deprecated)]
  #[feature(std)] //TODO: CUDA rng?
  pub fn new() -> Self {
    let keys: (u64, u64) = raw::cuda::hashmap_random_keys().unwrap();

    Self { k0: keys.0, k1: keys.1 }
  }
}

impl Default for RandomState {
  /// Constructs a new `RandomState`.
  fn default() -> Self {
    RandomState::new()
  }
}

impl Debug for RandomState {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.pad("RandomState { .. }")
  }
}

impl BuildHasher for RandomState {
  type Hasher = DefaultHasher;
  #[allow(deprecated)]
  fn build_hasher(&self) -> DefaultHasher {
    DefaultHasher(SipHasher::new_with_keys(self.k0, self.k1))
  }
}
