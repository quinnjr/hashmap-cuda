// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use crate::{
  raw::{ Table, Bucket },
  result::Result
};

use core::{
  fmt::{ Debug, Formatter },
  mem
};

/// A view into an occupied entry in a `HashMap`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
pub struct OccupiedEntry<'a, K, V> {
  key: Option<K>,
  elem: Bucket<(K, V)>,
  table: &'a mut Table<(K, V)>
}

unsafe impl<K, V> Send for OccupiedEntry<'_, K, V> where K: Send, V: Send {}

unsafe impl<K, V> Sync for OccupiedEntry<'_, K, V> where K: Sync, V: Sync {}

impl<K: Debug, V: Debug> Debug for OccupiedEntry<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> Result<()> {
    f.debug_struct("OccupiedEntry")
      .field("key", self.key())
      .field("value", self.get())
      .finish()
  }
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
  /// Gets a reference to the key in the entry.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  /// assert_eq!(map.rustc_entry("poneyland").key(), &"poneyland");
  /// ```
  pub fn key(&self) -> &K {
    unsafe { &self.elem.as_ref().0 }
  }

  /// Take the ownership of the key and value from the map.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::{ HashMap, RustcEntry };
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// if let RustcEntry::Occupied(o) = map.rustc_entry("poneyland") {
  ///     // We delete the entry from the map.
  ///     o.remove_entry();
  /// }
  ///
  /// assert_eq!(map.contains_key("poneyland"), false);
  /// ```
  pub fn remove_entry(self) -> (K, V) {
    unsafe {
      self.table.erase_no_drop(&self.elem);
      self.elem.read()
    }
  }

  /// Gets a reference to the value in the entry.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::RustcEntry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// if let RustcEntry::Occupied(o) = map.rustc_entry("poneyland") {
  ///     assert_eq!(o.get(), &12);
  /// }
  /// ```
  pub fn get(&self) -> &V {
    unsafe { &self.elem.as_ref().1 }
  }

  /// Gets a mutable reference to the value in the entry.
  ///
  /// If you need a reference to the `OccupiedEntry`
  /// which may outlive the
  /// destruction of the `RustcEntry` value, see [`into_mut`].
  ///
  /// [`into_mut`]: #method.into_mut
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::RustcEntry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// assert_eq!(map["poneyland"], 12);
  /// if let RustcEntry::Occupied(mut o) = map.rustc_entry("poneyland") {
  ///     *o.get_mut() += 10;
  ///     assert_eq!(*o.get(), 22);
  ///
  ///     // We can use the same RustcEntry multiple times.
  ///     *o.get_mut() += 2;
  /// }
  ///
  /// assert_eq!(map["poneyland"], 24);
  /// ```
  pub fn get_mut(&mut self) -> &mut V {
    unsafe { &mut self.elem.as_mut().1 }
  }

  /// Converts the OccupiedEntry into a mutable reference
  /// to the value in the entry
  /// with a lifetime bound to the map itself.
  ///
  /// If you need multiple references to the `OccupiedEntry`,
  /// see [`get_mut`].
  ///
  /// [`get_mut`]: #method.get_mut
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::RustcEntry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// assert_eq!(map["poneyland"], 12);
  /// if let RustcEntry::Occupied(o) = map.rustc_entry("poneyland") {
  ///     *o.into_mut() += 10;
  /// }
  ///
  /// assert_eq!(map["poneyland"], 22);
  /// ```
  pub fn into_mut(self) -> &'a mut V {
    unsafe { &mut self.elem.as_mut().1 }
  }

  /// Sets the value of the entry, and returns the entry's old value.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::RustcEntry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// if let RustcEntry::Occupied(mut o) = map.rustc_entry("poneyland") {
  ///     assert_eq!(o.insert(15), 12);
  /// }
  ///
  /// assert_eq!(map["poneyland"], 15);
  /// ```
  pub fn insert(&mut self, mut value: V) -> V {
    let old_value = self.get_mut();
    mem::swap(&mut value, old_value);
    value
  }

  /// Takes the value out of the entry, and returns it.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::RustcEntry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// if let RustcEntry::Occupied(o) = map.rustc_entry("poneyland") {
  ///   assert_eq!(o.remove(), 12);
  /// }
  ///
  /// assert_eq!(map.contains_key("poneyland"), false);
  /// ```
  pub fn remove(self) -> V {
    self.remove_entry().1
  }

  /// Replaces the entry, returning the old key and value.
  /// The new key in the hash map will be
  /// the key used to create this entry.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::{ RustcEntry, HashMap };
  /// use std::rc::Rc;
  ///
  /// let mut map: HashMap<Rc<String>, u32> = HashMap::new();
  /// map.insert(Rc::new("Stringthing".to_string()), 15);
  ///
  /// let my_key = Rc::new("Stringthing".to_string());
  ///
  /// if let RustcEntry::Occupied(entry) = map.rustc_entry(my_key) {
  ///   // Also replace the key with a handle to our other key.
  ///   let (old_key, old_value): (Rc<String>, u32) = entry.replace_entry(16);
  /// }
  ///
  /// ```
  pub fn replace_entry(self, value: V) -> (K, V) {
    let entry = unsafe { self.elem.as_mut() };
    let old_key = mem::replace(&mut entry.0, self.key.unwrap());
    let old_value = mem::replace(&mut entry.1, value);
    (old_key, old_value)
  }

  /// Replaces the key in the hash map with the key used to
  /// create this entry.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::hash_map::{RustcEntry, HashMap};
  /// use std::rc::Rc;
  ///
  /// let mut map: HashMap<Rc<String>, u32> = HashMap::new();
  /// let mut known_strings: Vec<Rc<String>> = Vec::new();
  ///
  /// // Initialise known strings, run program, etc.
  ///
  /// reclaim_memory(&mut map, &known_strings);
  ///
  /// fn reclaim_memory(map: &mut HashMap<Rc<String>, u32>, known_strings: &[Rc<String>] ) {
  ///   for s in known_strings {
  ///     if let RustcEntry::Occupied(entry) = map.rustc_entry(s.clone()) {
  ///        // Replaces the entry's key with our version of it in `known_strings`.
  ///        entry.replace_key();
  ///     }
  ///   }
  /// }
  /// ```
  pub fn replace_key(self) -> K {
    let entry = unsafe { self.elem.as_mut() };
    mem::replace(&mut entry.0, self.key.unwrap())
  }
}
