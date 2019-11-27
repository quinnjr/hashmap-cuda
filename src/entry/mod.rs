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

impl<'a, K, V> Entry<'a, K, V> {

    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashmap_cuda::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// map.entry("poneyland").or_insert(3);
    /// assert_eq!(map["poneyland"], 3);
    ///
    /// *map.entry("poneyland").or_insert(10) *= 2;
    /// assert_eq!(map["poneyland"], 6);
    /// ```

    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default),
        }
    }


    /// Ensures a value is in the entry by inserting the result of the default function if empty,
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
    /// map.entry("poneyland").or_insert_with(|| s);
    ///
    /// assert_eq!(map["poneyland"], "hoho".to_string());
    /// ```

    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
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
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
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
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 42);
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 43);
    /// ```


    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
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

    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() {
    /// use hashmap_cuda::HashMap;
    ///
    /// let mut map: HashMap<&str, Option<u32>> = HashMap::new();
    /// map.entry("poneyland").or_default();
    ///
    /// assert_eq!(map["poneyland"], None);
    /// # }
    /// ```

    pub fn or_default(self) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(Default::default()),
        }
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
    /// map.entry("poneyland").or_insert(12);
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```


    pub fn key(&self) -> &K {
        todo!()
    }

    /// Take the ownership of the key and value from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashmap_cuda::HashMap;
    /// use hashmap_cude::Entry
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     // We delete the entry from the map.
    ///     o.remove_entry();
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// ```


    pub fn remove_entry(self) -> (K, V) {
        todo!()
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashmap_cuda::HashMap;
    /// use hashmap_cude::Entry
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.get(), &12);
    /// }
    /// ```


    pub fn get(&self) -> &V {
        todo!()
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: #method.into_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use hashmap_cuda::HashMap;
    /// use hashmap_cude::Entry
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(*o.get(), 22);
    ///
    ///     // We can use the same Entry multiple times.
    ///     *o.get_mut() += 2;
    /// }
    ///
    /// assert_eq!(map["poneyland"], 24);
    /// ```


    pub fn get_mut(&mut self) -> &mut V {
        todo!()
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: #method.get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use hashmap_cuda::HashMap;
    /// use hashmap_cude::Entry
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     *o.into_mut() += 10;
    /// }
    ///
    /// assert_eq!(map["poneyland"], 22);
    /// ```


    pub fn into_mut(self) -> &'a mut V {
        todo!()
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashmap_cuda::HashMap;
    /// use hashmap_cude::Entry
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     assert_eq!(o.insert(15), 12);
    /// }
    ///
    /// assert_eq!(map["poneyland"], 15);
    /// ```


    pub fn insert(&mut self, value: V) -> V {
        todo!()
    }

    /// Takes the value out of the entry, and returns it.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashmap_cuda::HashMap;
    /// use hashmap_cude::Entry
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.remove(), 12);
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// ```


    pub fn remove(self) -> V {
        todo!()
    }

    /// Replaces the entry, returning the old key and value. The new key in the hash map will be
    /// the key used to create this entry.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(map_entry_replace)]
    /// use hashmap_cude::{ Entry, HashMap };
    /// use std::rc::Rc;
    ///
    /// let mut map: HashMap<Rc<String>, u32> = HashMap::new();
    /// map.insert(Rc::new("Stringthing".to_string()), 15);
    ///
    /// let my_key = Rc::new("Stringthing".to_string());
    ///
    /// if let Entry::Occupied(entry) = map.entry(my_key) {
    ///     // Also replace the key with a handle to our other key.
    ///     let (old_key, old_value): (Rc<String>, u32) = entry.replace_entry(16);
    /// }
    ///
    /// ```


    pub fn replace_entry(self, value: V) -> (K, V) {
        todo!()
    }

    /// Replaces the key in the hash map with the key used to create this entry.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(map_entry_replace)]
    /// use hashmap_cude::{ Entry, HashMap };
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
    ///     for s in known_strings {
    ///         if let Entry::Occupied(entry) = map.entry(s.clone()) {
    ///             // Replaces the entry's key with our version of it in `known_strings`.
    ///             entry.replace_key();
    ///         }
    ///     }
    /// }
    /// ```


    pub fn replace_key(self) -> K {
        todo!()
    }
}

impl<'a, K: 'a, V: 'a> VacantEntry<'a, K, V> {
    /// Gets a reference to the key that would be used when inserting a value
    /// through the `VacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashmap_cuda::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```


    pub fn key(&self) -> &K {
        todo!()
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashmap_cuda::HashMap;
    /// use hashmap_cude::Entry
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// if let Entry::Vacant(v) = map.entry("poneyland") {
    ///     v.into_key();
    /// }
    /// ```


    pub fn into_key(self) -> K {
        todo!()
    }

    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashmap_cuda::HashMap;
    /// use hashmap_cude::Entry
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// if let Entry::Vacant(o) = map.entry("poneyland") {
    ///     o.insert(37);
    /// }
    /// assert_eq!(map["poneyland"], 37);
    /// ```


    pub fn insert(self, value: V) -> &'a mut V {
        todo!()
    }
}
