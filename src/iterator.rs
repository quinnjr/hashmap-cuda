// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use core::fmt::{ Debug, Display, Formatter, Result as FmtResult };
use core::iter::FusedIterator;

/// An iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`iter`] method on [`HashMap`].
/// See its documentation for more.
///
/// [`iter`]: struct.HashMap.html#method.iter
/// [`HashMap`]: struct.HashMap.html
///
/// See Also: #26925 (Added `#[derive(Clone)]` instead of `Clone` impl)
#[derive(Clone)]
pub struct Iter<'a, K: 'a, V: 'a> {
  // // base: base::Iter<'a, K, V>,
}

impl<K: Debug, V: Debug> Debug for Iter<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    todo!()
  }
}

/// A mutable iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`iter_mut`] method
/// on [`HashMap`]. See its documentation for more.
///
/// [`iter_mut`]: struct.HashMap.html#method.iter_mut
/// [`HashMap`]: struct.HashMap.html
pub struct IterMut<'a, K: 'a, V: 'a> {
  // // base: base::IterMut<'a, K, V>
}

impl<'a, K, V> IterMut<'a, K, V> {
  /// Returns a iterator of references over the remaining items.
  pub(super) fn iter(&self) -> Iter<'_, K, V> {
    todo!()
  }
}

/// An owning iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`into_iter`] method on
/// [`HashMap`][`HashMap`] (provided by the `IntoIterator` trait).
/// See its documentation for more.
///
/// [`into_iter`]: struct.HashMap.html#method.into_iter
/// [`HashMap`]: struct.HashMap.html
pub struct IntoIter<K, V> {
  // // base: base::IntoIter<K, V>,
}

impl<K, V> IntoIter<K, V> {
  /// Returns a iterator of references over the remaining items.
  pub(super) fn iter(&self) -> Iter<'_, K, V> {
    todo!()
  }
}

/// A draining iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`drain`] method on [`HashMap`].
/// See its documentation for more.
///
/// [`drain`]: struct.HashMap.html#method.drain
/// [`HashMap`]: struct.HashMap.html
pub struct Drain<'a, K: 'a, V: 'a> {
  // // base: base::Drain<'a, K, V>,
}

impl<'a, K, V> Drain<'a, K, V> {
  /// Returns a iterator of references over the remaining items.
  pub(super) fn iter(&self) -> Iter<'_, K, V> {
    todo!()
  }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
  type Item = (&'a K, &'a V);

  fn next(&mut self) -> Option<(&'a K, &'a V)> {
    todo!()
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    todo!()
  }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
  fn len(&self) -> usize {
    todo!()
  }
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
  type Item = (&'a K, &'a mut V);

  fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
    todo!()
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    todo!()
  }
}

impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {
  fn len(&self) -> usize {
    todo!()
  }
}

impl<K, V> FusedIterator for IterMut<'_, K, V> {}

impl<K, V> Debug for IterMut<'_, K, V>
  where K: Debug, V: Debug
{
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_list().entries(self.iter()).finish()
  }
}

impl<K, V> Iterator for IntoIter<K, V> {
  type Item = (K, V);

  fn next(&mut self) -> Option<(K, V)> {
    todo!()
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    todo!()
  }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
  fn len(&self) -> usize {
    todo!()
  }
}

impl<K, V> FusedIterator for IntoIter<K, V> {}

impl<K: Debug, V: Debug> Debug for IntoIter<K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_list().entries(self.iter()).finish()
  }
}

impl<'a, K, V> Iterator for Drain<'a, K, V> {
  type Item = (K, V);

  fn next(&mut self) -> Option<(K, V)> {
    todo!()
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    todo!()
  }
}

impl<K, V> ExactSizeIterator for Drain<'_, K, V> {
  fn len(&self) -> usize {
    todo!()
  }
}

impl<K, V> FusedIterator for Drain<'_, K, V> {}

impl<K, V> Debug for Drain<'_, K, V>
  where K: Debug, V: Debug
{
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_list().entries(self.iter()).finish()
  }
}
