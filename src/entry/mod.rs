// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use crate::{
  HashMap,
  iterator::{ Drain, IntoIter, Iter, IterMut },
  map_raw_entry,
  result::Result,
  scopeguard
};

use core::{
  borrow::Borrow,
  fmt::{ Debug, Formatter },
  hash::{ BuildHasher, Hash },
  mem
};

mod occupied;
mod vacant;

pub use self::occupied::OccupiedEntry;
pub use self::vacant::VacantEntry;

use self::Entry::*;

/// A view into a single entry in a map, which may either be
/// vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`HashMap`].
///
/// [`HashMap`]: ../struct.HashMap.html
/// [`entry`]: ../struct.HashMap.html#method.entry
pub enum Entry<'a, K: 'a, V: 'a> {
  /// An occupied entry.
  Occupied(OccupiedEntry<'a, K, V>),
  /// A vacant entry.
  Vacant(VacantEntry<'a, K, V>)
}

impl<K: Debug, V: Debug> Debug for Entry<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> Result<()> {
    match *self {
      Vacant(ref v) => f.debug_tuple("Entry").field(v).finish(),
      Occupied(ref o) => f.debug_tuple("Entry").field(o).finish()
    }
  }
}

impl<'a, K, V> Entry<'a, K, V> {
  /// Sets the value of the entry, and returns a OccupiedEntry.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// let entry = map.entry("horseyland").insert(37);
  ///
  /// assert_eq!(entry.key(), &"horseyland");
  /// ```
  pub fn insert(self, value: V) -> OccupiedEntry<'a, K, V> {
    match self {
      Vacant(entry) => entry.insert_entry(value),
      Occupied(mut entry) => {
        entry.insert(value);
        entry
      }
    }
  }

  /// Ensures a value is in the entry by inserting the
  /// default if empty, and returns
  /// a mutable reference to the value in the entry.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  ///
  /// map.rustc_entry("poneyland").or_insert(3);
  /// assert_eq!(map["poneyland"], 3);
  ///
  /// *map.rustc_entry("poneyland").or_insert(10) *= 2;
  /// assert_eq!(map["poneyland"], 6);
  /// ```
  pub fn or_insert(self, default: V) -> &'a mut V where K: Hash {
    match self {
      Occupied(entry) => entry.into_mut(),
      Vacant(entry) => entry.insert(default),
    }
  }

  /// Ensures a value is in the entry by inserting the result
  /// of the default function if empty,
  /// and returns a mutable reference to the value in the entry.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, String> = HashMap::new();
  /// let s = "hoho".to_string();
  ///
  /// map.rustc_entry("poneyland").or_insert_with(|| s);
  ///
  /// assert_eq!(map["poneyland"], "hoho".to_string());
  /// ```
  pub fn or_insert_with<F: FnOnce() -> V>(self, default: F)
    -> &'a mut V where K: Hash
  {
    match self {
      Occupied(entry) => entry.into_mut(),
      Vacant(entry) => entry.insert(default()),
    }
  }

  /// Returns a reference to this entry's key.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// assert_eq!(map.rustc_entry("poneyland").key(), &"poneyland");
  /// ```
  pub fn key(&self) -> &K {
    match *self {
      Occupied(ref entry) => entry.key(),
      Vacant(ref entry) => entry.key(),
    }
  }

  /// Provides in-place mutable access to an occupied entry before any
  /// potential inserts into the map.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  ///
  /// map.rustc_entry("poneyland")
  ///    .and_modify(|e| { *e += 1 })
  ///    .or_insert(42);
  /// assert_eq!(map["poneyland"], 42);
  ///
  /// map.rustc_entry("poneyland")
  ///    .and_modify(|e| { *e += 1 })
  ///    .or_insert(42);
  /// assert_eq!(map["poneyland"], 43);
  /// ```
  pub fn and_modify<F>(self, f: F) -> Self where F: FnOnce(&mut V) {
    match self {
      Occupied(mut entry) => {
        f(entry.get_mut());
        Occupied(entry)
      }
      Vacant(entry) => Vacant(entry),
    }
  }
}

impl<'a, K, V: Default> Entry<'a, K, V> {
  /// Ensures a value is in the entry by inserting the
  /// default value if empty,
  /// and returns a mutable reference to the value in the entry.
  ///
  /// # Examples
  ///
  /// ```
  /// # fn main() {
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, Option<u32>> = HashMap::new();
  /// map.rustc_entry("poneyland").or_default();
  ///
  /// assert_eq!(map["poneyland"], None);
  /// # }
  /// ```
  pub fn or_default(self) -> &'a mut V where K: Hash {
    match self {
      Occupied(entry) => entry.into_mut(),
      Vacant(entry) => entry.insert(Default::default()),
    }
  }
}

/// A builder for computing where in a HashMap a key-value pair would
/// be stored.
///
/// See the [`HashMap::raw_entry_mut`] docs for usage examples.
///
/// [`HashMap::raw_entry_mut`]: struct.HashMap.html#method.raw_entry_mut
pub struct EntryBuilderMut<'a, K: 'a, V: 'a, S: 'a> {
  map: &'a mut HashMap<K, V, S>
}

impl<'a, K, V, S> EntryBuilderMut<'a, K, V, S> where S: BuildHasher {
  /// Creates a `EntryMut` from the given key.
  pub fn from_key<Q: ?Sized>(self, k: &Q) -> EntryMut<'a, K, V, S>
    where K: Borrow<Q>, Q: Hash + Eq
  {
    map_raw_entry(self.map.base.raw_entry_mut().from_key(k))
  }

  /// Creates a `EntryMut` from the given key and its hash.
  pub fn from_key_hashed_nocheck<Q: ?Sized>(self, hash: u64, k: &Q)
    -> EntryMut<'a, K, V, S> where K: Borrow<Q>, Q: Eq
  {
    map_raw_entry(
      self.map
        .base
        .raw_entry_mut()
        .from_key_hashed_nocheck(hash, k)
    )
  }

  /// Creates a `EntryMut` from the given hash.
  pub fn from_hash<F>(self, hash: u64, is_match: F)
    -> EntryMut<'a, K, V, S> where for<'b> F: FnMut(&'b K) -> bool
  {
    map_raw_entry(
      self.map
        .base
        .raw_entry_mut()
        .from_hash(hash, is_match)
      )
  }
}

/// A view into a single entry in a map, which may either be vacant
/// or occupied.
///
/// This is a lower-level version of [`Entry`].
///
/// This `enum` is constructed through the [`raw_entry_mut`] method
/// on [`HashMap`], then calling one of the methods of that
/// [`EntryBuilderMut`].
///
/// [`HashMap`]: struct.HashMap.html
/// [`Entry`]: enum.Entry.html
/// [`raw_entry_mut`]: struct.HashMap.html#method.raw_entry_mut
/// [`EntryBuilderMut`]: struct.EntryBuilderMut.html
pub enum EntryMut<'a, K: 'a, V: 'a, S: 'a> {
  /// An occupied entry.
  Occupied(OccupiedEntryMut<'a, K, V>),
  /// A vacant entry.
  Vacant(VacantEntryMut<'a, K, V, S>),
}

impl<'a, K, V, S> EntryMut<'a, K, V, S> {
  /// Ensures a value is in the entry by inserting the default if empty, and returns
  /// mutable references to the key and value in the entry.
  ///
  /// # Examples
  ///
  /// ```
  /// #![feature(hash_raw_entry)]
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  ///
  /// map.raw_entry_mut().from_key("poneyland").or_insert("poneyland", 3);
  /// assert_eq!(map["poneyland"], 3);
  ///
  /// *map.raw_entry_mut().from_key("poneyland").or_insert("poneyland", 10).1 *= 2;
  /// assert_eq!(map["poneyland"], 6);
  /// ```
  pub fn or_insert(self, default_key: K, default_val: V)
    -> (&'a mut K, &'a mut V) where K: Hash, S: BuildHasher
  {
      match self {
          EntryMut::Occupied(entry) => entry.into_key_value(),
          EntryMut::Vacant(entry) => entry.insert(default_key, default_val),
      }
  }

  /// Ensures a value is in the entry by inserting the result of the default function if empty,
  /// and returns mutable references to the key and value in the entry.
  ///
  /// # Examples
  ///
  /// ```
  /// #![feature(hash_raw_entry)]
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, String> = HashMap::new();
  ///
  /// map.raw_entry_mut().from_key("poneyland").or_insert_with(|| {
  ///     ("poneyland", "hoho".to_string())
  /// });
  ///
  /// assert_eq!(map["poneyland"], "hoho".to_string());
  /// ```


  pub fn or_insert_with<F>(self, default: F) -> (&'a mut K, &'a mut V)
  where
      F: FnOnce() -> (K, V),
      K: Hash,
      S: BuildHasher,
  {
      match self {
          EntryMut::Occupied(entry) => entry.into_key_value(),
          EntryMut::Vacant(entry) => {
              let (k, v) = default();
              entry.insert(k, v)
          }
      }
  }

  /// Provides in-place mutable access to an occupied entry before any
  /// potential inserts into the map.
  ///
  /// # Examples
  ///
  /// ```
  /// #![feature(hash_raw_entry)]
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  ///
  /// map.raw_entry_mut()
  ///    .from_key("poneyland")
  ///    .and_modify(|_k, v| { *v += 1 })
  ///    .or_insert("poneyland", 42);
  /// assert_eq!(map["poneyland"], 42);
  ///
  /// map.raw_entry_mut()
  ///    .from_key("poneyland")
  ///    .and_modify(|_k, v| { *v += 1 })
  ///    .or_insert("poneyland", 0);
  /// assert_eq!(map["poneyland"], 43);
  /// ```
  pub fn and_modify<F>(self, f: F) -> Self
  where
      F: FnOnce(&mut K, &mut V),
  {
      match self {
          EntryMut::Occupied(mut entry) => {
              {
                  let (k, v) = entry.get_key_value_mut();
                  f(k, v);
              }
              EntryMut::Occupied(entry)
          }
          EntryMut::Vacant(entry) => EntryMut::Vacant(entry),
      }
  }
}

/// A builder for computing where in a HashMap a key-value pair
/// would be stored.
///
/// See the [`HashMap::raw_entry`] docs for usage examples.
///
/// [`HashMap::raw_entry`]: ../struct.HashMap.html#method.raw_entry
pub struct RawEntryBuilder<'a, K: 'a, V: 'a, S: 'a> {
  map: &'a HashMap<K, V, S>
}

impl<K, V, S> Debug for EntryBuilderMut<'_, K, V, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<()> {
        f.debug_struct("RawEntryBuilder").finish()
    }
}

impl<'a, K, V, S> RawEntryBuilder<'a, K, V, S> where S: BuildHasher {
  /// Access an entry by key.
  pub fn from_key<Q: ?Sized>(self, k: &Q) -> Option<(&'a K, &'a V)>
    where K: Borrow<Q>, Q: Hash + Eq
  {
    self.map.base.raw_entry().from_key(k)
  }

  /// Access an entry by a key and its hash.


  pub fn from_key_hashed_nocheck<Q: ?Sized>(self, hash: u64, k: &Q) -> Option<(&'a K, &'a V)>
  where
      K: Borrow<Q>,
      Q: Hash + Eq,
  {
      self.map.base.raw_entry().from_key_hashed_nocheck(hash, k)
  }

  /// Access an entry by hash.


  pub fn from_hash<F>(self, hash: u64, is_match: F) -> Option<(&'a K, &'a V)>
  where
      F: FnMut(&K) -> bool,
  {
      self.map.base.raw_entry().from_hash(hash, is_match)
  }
}
