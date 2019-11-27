// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use core::fmt::{ Debug, Display, Formatter, Result as FmtResult };
use core::iter::FusedIterator;

use crate::iterator::Iter;

/// An iterator over the keys of a `HashMap`.
///
/// This `struct` is created by the [`keys`] method on
/// [`HashMap`]. See its documentation for more.
///
/// [`keys`]: struct.HashMap.html#method.keys
/// [`HashMap`]: struct.HashMap.html
///
/// See Also: #26925 Implemented `#[derive(Clone)]`
#[derive(Clone)]
pub struct Keys<'a, K: 'a, V: 'a> {
  inner: Iter<'a, K, V>
}

impl<K: Debug, V>Debug for Keys<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_list().entries(self.clone()).finish()
  }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
  type Item = &'a K;

  fn next(&mut self) -> Option<&'a K> {
    self.inner.next().map(|(k, _)| k)
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    self.inner.size_hint()
  }
}

impl<K, V> ExactSizeIterator for Keys<'_, K, V> {
  fn len(&self) -> usize {
    self.inner.len()
  }
}

impl<K, V> FusedIterator for Keys<'_, K, V> {}
