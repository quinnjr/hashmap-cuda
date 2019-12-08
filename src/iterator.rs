// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use core::{
  fmt::{ Debug, Formatter, Result as FmtResult },
  iter::FusedIterator,
  marker::PhantomData
};

use crate::{
  raw::{ RawDrain, RawIter, RawIntoIter }
};

/// An iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`iter`] method on [`HashMap`].
/// See its documentation for more.
///
/// [`iter`]: struct.HashMap.html#method.iter
/// [`HashMap`]: struct.HashMap.html
pub struct Iter<'a, K: 'a, V: 'a> {
  pub(crate) inner: RawIter<(K, V)>,
  pub(crate) marker: PhantomData<(&'a K, &'a V)>
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
impl<K, V> Clone for Iter<'_, K, V> {
  #[inline]
  fn clone(&self) -> Self {
    Self {
      inner: self.inner.clone(),
      marker: PhantomData
    }
  }
}

impl<K: Debug, V: Debug> Debug for Iter<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_list().entries(self.clone()).finish()
  }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
  type Item = (&'a K, &'a V);

  #[inline]
  fn next(&mut self) -> Option<(&'a K, &'a V)> {
    self.inner.next().map(|x| unsafe {
      let r = x.as_ref();
      (&r.0, &r.1)
    })
  }
  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    self.inner.size_hint()
  }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
  #[inline]
  fn len(&self) -> usize {
    self.inner.len()
  }
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}


/// A mutable iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`iter_mut`] method
/// on [`HashMap`]. See its documentation for more.
///
/// [`iter_mut`]: struct.HashMap.html#method.iter_mut
/// [`HashMap`]: struct.HashMap.html
pub struct IterMut<'a, K: 'a, V: 'a> {
  pub(crate) inner: RawIter<(K, V)>,
  pub(crate) marker: PhantomData<(&'a K, &'a mut V)>
}

/// We override the default Send impl which has K: Sync instead of K: Send. Both
/// are correct, but this one is more general since it allows keys which
/// implement Send but not Sync.
unsafe impl<K: Send, V: Send> Send for IterMut<'_, K, V> {}

impl<'a, K, V> IterMut<'a, K, V> {
  /// Returns a iterator of references over the remaining items.
  #[inline]
  pub(super) fn iter(&self) -> Iter<'_, K, V> {
    Iter {
      inner: self.inner.clone(),
      marker: PhantomData
    }
  }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
  type Item = (&'a K, &'a mut V);

  #[inline]
  fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
    self.inner.next().map(|x| unsafe {
      let r = x.as_mut();
      (&r.0, &mut r.1)
    })
  }
  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    self.inner.size_hint()
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
  pub(crate) inner: RawIntoIter<(K, V)>
}

impl<K, V> IntoIter<K, V> {
  /// Returns a iterator of references over the remaining items.
  #[inline]
  pub(super) fn iter(&self) -> Iter<'_, K, V> {
    Iter {
      inner: self.inner.iter(),
      marker: PhantomData
    }
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
  pub(crate) inner: RawDrain<'a, (K, V)>
}

impl<'a, K, V> Drain<'a, K, V> {
  /// Returns a iterator of references over the remaining items.
  #[inline]
  pub(super) fn iter(&self) -> Iter<'_, K, V> {
    Iter {
      inner: self.inner.iter(),
      marker: PhantomData
    }
  }
}

impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {
  #[inline]
  fn len(&self) -> usize {
    self.inner.len()
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

  #[inline]
  fn next(&mut self) -> Option<(K, V)> {
    self.inner.next()
  }

  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    self.inner.size_hint()
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

  #[inline]
  fn next(&mut self) -> Option<(K, V)> {
    self.inner.next()
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    self.inner.size_hint()
  }
}

impl<K, V> ExactSizeIterator for Drain<'_, K, V> {
  fn len(&self) -> usize {
    self.inner.len()
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
