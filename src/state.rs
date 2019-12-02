// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use crate::{
  hasher::DefaultHasher,
  raw::sys
};

use core::cell::Cell;
#[allow(deprecated)]
use core::hash::SipHasher;
use core::hash::BuildHasher;

use core::fmt::{ Debug, Display, Formatter, Result as FmtResult };

use cuda::{ self, rand };

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
    // thread_local!(static KEYS: Cell<(u64, u64)> = {
    //   Cell::new(sys::hashmap_random_keys())
    // });
    // Ensure CUDA initialization
    if !cuda::driver::cuda_initialized().ok() {
      cuda::driver::cuda_init().unwrap();
    };

    let mut keys: (u64, u64);
    let generator = rand::CurandGenerator::<rand::CurandDefaultRng>::create();

    generator.gen_u64(*keys.0, 1).unwrap();
    generator.gen_u64(*keys.1, 1).unwrap();

    // static KEYS: (u64, u64) = {
    //   let generator = rand::CurandGenerator<rand::>::create();
    //   let mut k1, k2: u64;
    //   generator.gen_u64(*k1, 1).unwrap();
    //   generator.gen_u64(*k2, 1).unwrap();
    //
    //   (k1, k2)
    // };
    Self { k0: keys.0, k1: keys.1 }

    // KEYS.with(|keys| {
    //   let (k0, k1) = keys.get();
    //   keys.set((k0.wrapping_add(1), k1));
    //   Self { k0: k0, k1: k1 }
    // })
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
  #[feature(std)]
  fn build_hasher(&self) -> DefaultHasher {
    DefaultHasher(SipHasher::new_with_keys(self.k0, self.k1))
  }
}
