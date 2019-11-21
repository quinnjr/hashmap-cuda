// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

//ignore-tidy-filelength

#![cfg_attr(
  debug_assertions,
  all(
    allow(
      dead_code,
      unused_variables
    ),
    warn(
      missing_docs
    )
  )
)]

#![cfg_attr(
  not(debug_assertions),
  deny(
    missing_docs,
    unused_variables
  )
)]

use std::{
  borrow::Borrow,
  cell::Cell,
  collections::TryReserveError,
  default::Default,
  fmt::{ self, Display, Debug, Formatter, Result as FmtResult },
  #[allow(deprecated)]
  hash::{ BuildHasher, Hash, Hasher, SipHasher13 },
  iter::{ FromIterator, FusedIterator },
  ops::Index,
  sys
}

///
pub struct RandomState;

///
#[derive(Clone, Debug)]
pub struct HashMap<K, V, S = RandomState> {
  capacity: usize
}

impl<K: Hash + Eq, V> HashMap<K, V, RandomState> {
  /// Creates an empty `Hashmap`.
  ///
  /// ```
  /// use hashmap-cuda::HashMap;
  /// let mut map: HashMap<&str, i64> = HashMap::new();
  /// ```
  #[inline]
  pub fn new() -> Self<K, V, RandomState> {
    Self::default()
  }

  /// Creates an empty `Hashmap` with a specified initial capacity.
  ///
  /// ```
  /// use hashmap-cuda::HashMap;
  /// let mut map: HashMap<&str, i64> = HashMap::with_capacity(100);
  /// ```
  #[inline]
  pub fn with_capacity(capacity: usize) -> Self {
    Self {
      capacity: capacity
    }
  }


}

impl <K, V, S> HashMap<K, V, S> where
  K: Eq + Hash,
  S: BuildHasher
{
  /// Creates an empty `HashMap` with a specified hashing implementation.
  #[inline]
  pub fn with_hasher() -> Self<K, V, S> {
    unimplemented!()
  }
}

impl<K, V, S> HashMap<K, V, S> {
  /// Returns the number of elements the map can hold without reallocating.
  ///
  /// This number is a lower bound; the `HashMap<K, V>` might be able to hold
  /// more, but is guaranteed to be able to hold at least this many.
  ///
  /// ```
  /// use hashmap-cuda::HashMap;
  /// let mut map: HashMap<&str, i64> = HashMap::with_capacity(100);
  /// assert!(map.capacity() >= 100);
  /// ```
  #[inline]
  pub fn capacity(&self) -> usize {
    self.capacity
  }
}

impl<K, V, S> Default for HashMap<K, V, S> {
  fn default() -> Self {
    unimplemented!()
  }
}

impl <K, V, S> Display for HashMap<K, V, S> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    unimplmented!()
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn new() {
    let m = HashMap::new();
    assert!(m != ());
  }
}
