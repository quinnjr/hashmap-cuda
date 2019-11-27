// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use crate::{
  raw::Table,
  result::Result
};

use core::{
  fmt::{ Debug, Formatter },
  mem
};

use super::OccupiedEntry;

/// A view into a vacant entry in a `HashMap`.
/// It is part of the [`RustcEntry`] enum.
///
/// [`Entry`]: enum.Entry.html
pub struct VacantEntry<'a, K, V> {
  hash: u64,
  key: K,
  table: &'a mut Table<(K, V)>,
}

impl<K: Debug, V> Debug for VacantEntry<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> Result<()> {
    f.debug_tuple("VacantEntry").field(self.key()).finish()
  }
}

impl<'a, K, V> VacantEntry<'a, K, V> {
  /// Gets a reference to the key that would be used when inserting a value
  /// through the `RustcVacantEntry`.
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
    &self.key
  }

  /// Take ownership of the key.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::RustcEntry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  ///
  /// if let RustcEntry::Vacant(v) = map.rustc_entry("poneyland") {
  ///     v.into_key();
  /// }
  /// ```
  pub fn into_key(self) -> K {
    self.key
  }

  /// Sets the value of the entry with the RustcVacantEntry's key,
  /// and returns a mutable reference to it.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::RustcEntry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  ///
  /// if let RustcEntry::Vacant(o) = map.rustc_entry("poneyland") {
  ///   o.insert(37);
  /// }
  /// assert_eq!(map["poneyland"], 37);
  /// ```
  pub fn insert(self, value: V) -> &'a mut V {
    let bucket = self.table.insert_no_grow(self.hash, (self.key, value));
    unsafe { &mut bucket.as_mut().1 }
  }

  /// Sets the value of the entry with the RustcVacantEntry's key,
  /// and returns a OccupiedEntry.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::{ HashMap, RustcEntry };
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  ///
  /// if let RustcEntry::Vacant(v) = map.rustc_entry("poneyland") {
  ///   let o = v.insert_entry(37);
  ///   assert_eq!(o.get(), &37);
  /// }
  /// ```
  pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
    let bucket = self.table.insert_no_grow(self.hash, (self.key, value));
    OccupiedEntry {
      key: None,
      elem: bucket,
      table: self.table,
    }
  }
}
