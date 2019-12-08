// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use crate::iterator::{ Iter, IterMut };

use core::{
  fmt::{ Debug, Formatter, Result as FmtResult },
  iter::FusedIterator
};

/// An iterator over the values of a `HashMap`.
///
/// This `struct` is created by the [`values`] method on
/// [`HashMap`]. See its documentation for more.
///
/// [`values`]: struct.HashMap.html#method.values
/// [`HashMap`]: struct.HashMap.html
pub struct Values<'a, K: 'a, V: 'a> {
  pub(crate) inner: Iter<'a, K, V>
}

impl<K, V: Debug> Debug for Values<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_list().entries(self.clone()).finish()
  }
}

impl<K, V> Clone for Values<'_, K, V> {
  #[inline]
  fn clone(&self) -> Self {
    Self {
      inner: self.inner.clone()
    }
  }
}

/// A mutable iterator over the values of a `HashMap`.
///
/// This `struct` is created by the [`values_mut`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`values_mut`]: struct.HashMap.html#method.values_mut
/// [`HashMap`]: struct.HashMap.html
pub struct ValuesMut<'a, K: 'a, V: 'a> {
  pub(crate) inner: IterMut<'a, K, V>,
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
  type Item = &'a V;

  fn next(&mut self) -> Option<&'a V> {
    self.inner.next().map(|(_, v)| v)
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    self.inner.size_hint()
  }
}

impl<K, V> ExactSizeIterator for Values<'_, K, V> {
  fn len(&self) -> usize {
    self.inner.len()
  }
}

impl<K, V> FusedIterator for Values<'_, K, V> {}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
  type Item = &'a mut V;

  fn next(&mut self) -> Option<&'a mut V> {
    self.inner.next().map(|(_, v)| v)
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    self.inner.size_hint()
  }
}

impl<K, V> ExactSizeIterator for ValuesMut<'_, K, V> {
  fn len(&self) -> usize {
    self.inner.len()
  }
}

impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}


impl<K, V> Debug for ValuesMut<'_, K, V>
  where K: Debug, V: Debug
{
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_list().entries(self.inner.iter()).finish()
  }
}
