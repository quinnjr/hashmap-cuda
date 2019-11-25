// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use crate::prelude::*;
use crate::HashMap;

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
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    match *self {
      Vacant(ref v) => f.debug_tuple("Entry").field(v).finish(),
      Occupied(ref o) => f.debug_tuple("Entry").field(o).finish()
    }
  }
}

/// A view into an occupied entry in a `HashMap`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
pub struct OccupiedEntry<'a, K: 'a, V: 'a> {
  // TODO: reimplement RustcOccupiedEntry in the library proper.
  base: base::RustcOccupiedEntry<'a, K, V>
}

impl<K: Debug, V: Debug> Debug for OccupiedEntry<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_struct("OccupiedEntry")
      .field("key", self.key())
      .field("value", self.get())
      .finish()
  }
}

/// A view into a vacant entry in a `HashMap`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
pub struct VacantEntry<'a, K: 'a, V: 'a> {
  // TODO: reimplement RustcVacantEntry in the library proper.
  base: base::RustcVacantEntry<'a, K, V>,
}

impl<K: Debug, V> Debug for VacantEntry<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_tuple("VacantEntry").field(self.key()).finish()
  }
}

/// A builder for computing where in a HashMap a key-value pair would
/// be stored.
///
/// See the [`HashMap::raw_entry_mut`] docs for usage examples.
///
/// [`HashMap::raw_entry_mut`]: ../struct.HashMap.html#method.raw_entry_mut
pub struct RawEntryBuilderMut<'a, K: 'a, V: 'a, S: 'a> {
  map: &'a mut HashMap<K, V, S>
}

/// A view into a single entry in a map, which may either
/// be vacant or occupied.
///
/// This is a lower-level version of [`Entry`].
///
/// This `enum` is constructed through the [`raw_entry_mut`]
/// method on [`HashMap`],
/// then calling one of the methods of that [`RawEntryBuilderMut`].
///
/// [`HashMap`]: ../struct.HashMap.html
/// [`Entry`]: enum.Entry.html
/// [`raw_entry_mut`]: ../struct.HashMap.html#method.raw_entry_mut
/// [`RawEntryBuilderMut`]: struct.RawEntryBuilderMut.html
pub enum RawEntryMut<'a, K: 'a, V: 'a, S: 'a> {
  /// An occupied entry.
  Occupied(RawOccupiedEntryMut<'a, K, V>),
  /// A vacant entry.
  Vacant(RawVacantEntryMut<'a, K, V, S>)
}

/// A view into an occupied entry in a `HashMap`.
/// It is part of the [`RawEntryMut`] enum.
///
/// [`RawEntryMut`]: enum.RawEntryMut.html
pub struct RawOccupiedEntryMut<'a, K: 'a, V: 'a> {
  // TODO: reimplement RawOccupiedEntryMut in the library proper.
  base: base::RawOccupiedEntryMut<'a, K, V>
}

/// A view into a vacant entry in a `HashMap`.
/// It is part of the [`RawEntryMut`] enum.
///
/// [`RawEntryMut`]: enum.RawEntryMut.html
pub struct RawVacantEntryMut<'a, K: 'a, V: 'a, S: 'a> {
  // TODO: reimplement RawVacantEntryMut in the library proper.
  base: base::RawVacantEntryMut<'a, K, V, S>
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

impl<'a, K, V, S> RawEntryBuilderMut<'a, K, V, S> where S: BuildHasher
{
  /// Creates a `RawEntryMut` from the given key.
  pub fn from_key<Q: ?Sized>(self, k: &Q) -> RawEntryMut<'a, K, V, S>
    where K: Borrow<Q>, Q: Hash + Eq
  {
    map_raw_entry(self.map.base.raw_entry_mut().from_key(k))
  }

  /// Creates a `RawEntryMut` from the given key and its hash.
  pub fn from_key_hashed_nocheck<Q: ?Sized>(self,
    hash: u64, k: &Q) -> RawEntryMut<'a, K, V, S>  where
    K: Borrow<Q>, Q: Eq
  {
    map_raw_entry(
      self.map
        .base
        .raw_entry_mut()
        .from_key_hashed_nocheck(hash, k)
    )
  }

  /// Creates a `RawEntryMut` from the given hash.
  pub fn from_hash<F>(self, hash: u64, is_match: F)
    -> RawEntryMut<'a, K, V, S> where for<'b> F: FnMut(&'b K) -> bool
  {
    map_raw_entry(
      self.map
        .base
        .raw_entry_mut()
        .from_hash(hash, is_match)
      )
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

impl<'a, K, V, S> RawEntryMut<'a, K, V, S> {
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


  pub fn or_insert(self, default_key: K, default_val: V) -> (&'a mut K, &'a mut V)
  where
      K: Hash,
      S: BuildHasher,
  {
      match self {
          RawEntryMut::Occupied(entry) => entry.into_key_value(),
          RawEntryMut::Vacant(entry) => entry.insert(default_key, default_val),
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
          RawEntryMut::Occupied(entry) => entry.into_key_value(),
          RawEntryMut::Vacant(entry) => {
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
          RawEntryMut::Occupied(mut entry) => {
              {
                  let (k, v) = entry.get_key_value_mut();
                  f(k, v);
              }
              RawEntryMut::Occupied(entry)
          }
          RawEntryMut::Vacant(entry) => RawEntryMut::Vacant(entry),
      }
  }
}

impl<'a, K, V> RawOccupiedEntryMut<'a, K, V> {
    /// Gets a reference to the key in the entry.


    pub fn key(&self) -> &K {
        todo!()
    }

    /// Gets a mutable reference to the key in the entry.


    pub fn key_mut(&mut self) -> &mut K {
        todo!()
    }

    /// Converts the entry into a mutable reference to the key in the entry
    /// with a lifetime bound to the map itself.


    pub fn into_key(self) -> &'a mut K {
        todo!()
    }

    /// Gets a reference to the value in the entry.


    pub fn get(&self) -> &V {
        todo!()
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.


    pub fn into_mut(self) -> &'a mut V {
        todo!()
    }

    /// Gets a mutable reference to the value in the entry.


    pub fn get_mut(&mut self) -> &mut V {
        todo!()
    }

    /// Gets a reference to the key and value in the entry.


    pub fn get_key_value(&mut self) -> (&K, &V) {
        todo!()
    }

    /// Gets a mutable reference to the key and value in the entry.


    pub fn get_key_value_mut(&mut self) -> (&mut K, &mut V) {
        todo!()
    }

    /// Converts the OccupiedEntry into a mutable reference to the key and value in the entry
    /// with a lifetime bound to the map itself.


    pub fn into_key_value(self) -> (&'a mut K, &'a mut V) {
        todo!()
    }

    /// Sets the value of the entry, and returns the entry's old value.


    pub fn insert(&mut self, value: V) -> V {
        todo!()
    }

    /// Sets the value of the entry, and returns the entry's old value.


    pub fn insert_key(&mut self, key: K) -> K {
        todo!()
    }

    /// Takes the value out of the entry, and returns it.


    pub fn remove(self) -> V {
        todo!()
    }

    /// Take the ownership of the key and value from the map.


    pub fn remove_entry(self) -> (K, V) {
        todo!()
    }
}

impl<'a, K, V, S> RawVacantEntryMut<'a, K, V, S> {
    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it.


    pub fn insert(self, key: K, value: V) -> (&'a mut K, &'a mut V)
    where
        K: Hash,
        S: BuildHasher,
    {
        todo!()
    }

    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it.


    pub fn insert_hashed_nocheck(self, hash: u64, key: K, value: V) -> (&'a mut K, &'a mut V)
    where
        K: Hash,
        S: BuildHasher,
    {
        todo!()
    }
}


impl<K, V, S> Debug for RawEntryBuilderMut<'_, K, V, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("RawEntryBuilder").finish()
    }
}


impl<K: Debug, V: Debug, S> Debug for RawEntryMut<'_, K, V, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match *self {
            RawEntryMut::Vacant(ref v) => f.debug_tuple("RawEntry").field(v).finish(),
            RawEntryMut::Occupied(ref o) => f.debug_tuple("RawEntry").field(o).finish(),
        }
    }
}


impl<K: Debug, V: Debug> Debug for RawOccupiedEntryMut<'_, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("RawOccupiedEntryMut")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}


impl<K, V, S> Debug for RawVacantEntryMut<'_, K, V, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("RawVacantEntryMut").finish()
    }
}


impl<K, V, S> Debug for RawEntryBuilder<'_, K, V, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("RawEntryBuilder").finish()
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
