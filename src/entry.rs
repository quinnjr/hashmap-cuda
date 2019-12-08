// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use core::{
  borrow::Borrow,
  fmt::{ Debug, Formatter, Result as FmtResult },
  hash::{ BuildHasher, Hash, Hasher },
  mem
};

use crate::{
  HashMap,
  raw::{ Bucket, RawTable },
  make_hash
};

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
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
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
  /// ```ignore
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// let entry = map.entry("horseyland").insert(37);
  ///
  /// assert_eq!(entry.key(), &"horseyland");
  /// ```
  #[inline]
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
  /// ```ignore
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
  #[inline]
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
  /// ```ignore
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, String> = HashMap::new();
  /// let s = "hoho".to_string();
  ///
  /// map.rustc_entry("poneyland").or_insert_with(|| s);
  ///
  /// assert_eq!(map["poneyland"], "hoho".to_string());
  /// ```
  #[inline]
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
  #[inline]
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
  /// ```ignore
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
  #[inline]
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
  /// ```ignore
  /// # fn main() {
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<&str, Option<u32>> = HashMap::new();
  /// map.rustc_entry("poneyland").or_default();
  ///
  /// assert_eq!(map["poneyland"], None);
  /// # }
  /// ```
  #[inline]
  pub fn or_default(self) -> &'a mut V where K: Hash {
    match self {
      Occupied(entry) => entry.into_mut(),
      Vacant(entry) => entry.insert(Default::default()),
    }
  }
}

/// A builder for computing where in a HashMap a key-value pair would be stored.
///
/// See the [`HashMap::raw_entry`] docs for usage examples.
///
/// [`HashMap::raw_entry`]: struct.HashMap.html#method.raw_entry
pub struct EntryBuilder<'a, K: 'a, V: 'a, S: 'a> {
  pub(crate) map: &'a HashMap<K, V, S>
}

impl<'a, K, V, S> EntryBuilder<'a, K, V, S>
  where K: Eq + Hash, S: BuildHasher {
  /// Access an entry by key.
  #[inline]
  pub fn from_key<Q: ?Sized>(self, k: &Q) -> Option<(&'a K, &'a V)> where
    K: Borrow<Q>, Q: Hash + Eq, S: BuildHasher
  {
    let mut hasher = self.map.hash_builder.build_hasher();
    k.hash(&mut hasher);
    self.from_key_hashed_nocheck(hasher.finish(), k)
  }

  /// Access an entry by a key and its hash.
  #[inline]
  pub fn from_key_hashed_nocheck<Q: ?Sized>(self, hash: u64, k: &Q)
    -> Option<(&'a K, &'a V)> where K: Borrow<Q>, Q: Hash + Eq
  {
    self.from_hash(hash, |q| q.borrow().eq(k))
  }

  /// Access an entry by hash.
  #[inline]
  pub fn from_hash<F>(self, hash: u64, is_match: F)
    -> Option<(&'a K, &'a V)> where F: FnMut(&K) -> bool
  {
    self.search(hash, is_match)
  }

  #[inline]
  fn search<F>(self, hash: u64, mut is_match: F)
    -> Option<(&'a K, &'a V)> where F: FnMut(&K) -> bool
  {
    self.map.table
      .find(hash, |(k, _)| is_match(k))
      .map(|item| unsafe {
        let &(ref key, ref value) = item.as_ref();
        (key, value)
      })
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
  /// ```ignore
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
  #[inline]
  pub fn or_insert(self, default_key: K, default_val: V)-> (&'a mut K, &'a mut V)
    where K: Hash, S: BuildHasher
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
  /// ```ignore
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
  #[inline]
  pub fn or_insert_with<F>(self, default: F) -> (&'a mut K, &'a mut V)
    where F: FnOnce() -> (K, V), K: Hash, S: BuildHasher
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
  /// ```ignore
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
  #[inline]
  pub fn and_modify<F>(self, f: F) -> Self where F: FnOnce(&mut K, &mut V) {
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
pub struct EntryBuilderMut<'a, K: 'a, V: 'a, S: 'a> {
  pub(crate) map: &'a HashMap<K, V, S>
}

impl<K, V, S> Debug for EntryBuilderMut<'_, K, V, S> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_struct("EntryBuilderMut").finish()
  }
}

impl<'a, K, V, S> EntryBuilderMut<'a, K, V, S> {
  /// Access an entry by key.
  #[inline]
  #[allow(clippy::wrong_self_convention)]
  pub fn from_key<Q: ?Sized>(self, k: &Q) -> EntryMut<'a, K, V, S>
    where  K: Borrow<Q>, S: BuildHasher, Q: Hash + Eq
  {
    let mut hasher = self.map.hash_builder.build_hasher();
    k.hash(&mut hasher);
    self.from_key_hashed_nocheck(hasher.finish(), k)
  }

  /// Access an entry by a key and its hash.
  #[inline]
  #[allow(clippy::wrong_self_convention)]
  pub fn from_key_hashed_nocheck<Q: ?Sized>(self, hash: u64, k: &Q)
    -> EntryMut<'a, K, V, S> where K: Borrow<Q>, Q: Hash + Eq
  {
    self.from_hash(hash, |q| q.borrow().eq(k))
  }

  /// Access an entry by hash.
  #[inline]
  #[allow(clippy::wrong_self_convention)]
  pub fn from_hash<F>(self, hash: u64, is_match: F)
    -> EntryMut<'a, K, V, S> where for<'b> F: FnMut(&'b K) -> bool
  {
    self.search(hash, is_match)
  }

  #[inline]
  fn search<F>(self, _hash: u64, mut _is_match: F)
    -> EntryMut<'a, K, V, S> where for<'b> F: FnMut(&'b K) -> bool
  {
    todo!()
    // match self.map.table.find(hash, |(k, _)| is_match(k)) {
    //   Some(elem) => EntryMut::Occupied(OccupiedEntryMut {
    //     elem,
    //     table: &mut self.map.table
    //   }),
    //   None => EntryMut::Vacant(VacantEntryMut {
    //     table: &mut self.map.table,
    //     hash_builder: &self.map.hash_builder
    //   })
    // }
  }
}

/// A view into an occupied entry in a `HashMap`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
pub struct OccupiedEntry<'a, K, V> {
  pub(crate) key: Option<K>,
  pub(crate) elem: Bucket<(K, V)>,
  pub(crate) table: &'a mut RawTable<(K, V)>
}

unsafe impl<K, V> Send for OccupiedEntry<'_, K, V> where K: Send, V: Send {}

unsafe impl<K, V> Sync for OccupiedEntry<'_, K, V> where K: Sync, V: Sync {}

impl<K: Debug, V: Debug> Debug for OccupiedEntry<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
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
  /// ```ignore
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
  /// ```ignore
  /// use hashmap_cuda::{ HashMap, Entry };
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// if let Entry::Occupied(o) = map.rustc_entry("poneyland") {
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
  /// ```ignore
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::Entry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// if let Entry::Occupied(o) = map.rustc_entry("poneyland") {
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
  /// destruction of the `Entry` value, see [`into_mut`].
  ///
  /// [`into_mut`]: #method.into_mut
  ///
  /// # Examples
  ///
  /// ```ignore
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::Entry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// assert_eq!(map["poneyland"], 12);
  /// if let Entry::Occupied(mut o) = map.rustc_entry("poneyland") {
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
  /// ```ignore
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::Entry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// assert_eq!(map["poneyland"], 12);
  /// if let Entry::Occupied(o) = map.rustc_entry("poneyland") {
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
  /// ```ignore
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::Entry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// if let Entry::Occupied(mut o) = map.rustc_entry("poneyland") {
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
  /// ```ignore
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::Entry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  /// map.rustc_entry("poneyland").or_insert(12);
  ///
  /// if let Entry::Occupied(o) = map.rustc_entry("poneyland") {
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
  /// ```ignore
  /// use hashmap_cuda::{ Entry, HashMap };
  /// use std::rc::Rc;
  ///
  /// let mut map: HashMap<Rc<String>, u32> = HashMap::new();
  /// map.insert(Rc::new("Stringthing".to_string()), 15);
  ///
  /// let my_key = Rc::new("Stringthing".to_string());
  ///
  /// if let Entry::Occupied(entry) = map.rustc_entry(my_key) {
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
  /// ```ignore
  /// use hashmap_cuda::hash_map::{Entry, HashMap};
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
  ///     if let Entry::Occupied(entry) = map.rustc_entry(s.clone()) {
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

/// A view into an occupied entry in a `HashMap`.
/// It is part of the [`RawEntryMut`] enum.
///
/// [`RawEntryMut`]: enum.RawEntryMut.html
pub struct OccupiedEntryMut<'a, K, V> {
  pub(crate) elem: Bucket<(K, V)>,
  pub(crate) table: &'a mut RawTable<(K, V)>,
}

impl<'a, K, V> OccupiedEntryMut<'a, K, V> {
  /// Gets a reference to the key in the entry.
  #[inline]
  pub fn key(&self) -> &K {
    unsafe { &self.elem.as_ref().0 }
  }

  /// Gets a mutable reference to the key in the entry.
  #[inline]
  pub fn key_mut(&mut self) -> &mut K {
    unsafe { &mut self.elem.as_mut().0 }
  }

  /// Converts the entry into a mutable reference to the key in the entry
  /// with a lifetime bound to the map itself.
  #[inline]
  pub fn into_key(self) -> &'a mut K {
    unsafe { &mut self.elem.as_mut().0 }
  }

  /// Gets a reference to the value in the entry.
  #[inline]
  pub fn get(&self) -> &V {
    unsafe { &self.elem.as_ref().1 }
  }

  /// Converts the OccupiedEntry into a mutable reference to the value in the entry
  /// with a lifetime bound to the map itself.
  #[inline]
  pub fn into_mut(self) -> &'a mut V {
    unsafe { &mut self.elem.as_mut().1 }
  }

  /// Gets a mutable reference to the value in the entry.
  #[inline]
  pub fn get_mut(&mut self) -> &mut V {
    unsafe { &mut self.elem.as_mut().1 }
  }

  /// Gets a reference to the key and value in the entry.
  #[inline]
  pub fn get_key_value(&mut self) -> (&K, &V) {
    unsafe {
      let &(ref key, ref value) = self.elem.as_ref();
      (key, value)
    }
  }

  /// Gets a mutable reference to the key and value in the entry.
  #[inline]
  pub fn get_key_value_mut(&mut self) -> (&mut K, &mut V) {
    unsafe {
      let &mut (ref mut key, ref mut value) = self.elem.as_mut();
      (key, value)
    }
  }

  /// Converts the OccupiedEntry into a mutable reference to the key and value
  // in the entry with a lifetime bound to the map itself.
  #[inline]
  pub fn into_key_value(self) -> (&'a mut K, &'a mut V) {
    unsafe {
      let &mut (ref mut key, ref mut value) = self.elem.as_mut();
      (key, value)
    }
  }

  /// Sets the value of the entry, and returns the entry's old value.
  #[inline]
  pub fn insert(&mut self, value: V) -> V {
    mem::replace(self.get_mut(), value)
  }

  /// Sets the value of the entry, and returns the entry's old value.
  #[inline]
  pub fn insert_key(&mut self, key: K) -> K {
    mem::replace(self.key_mut(), key)
  }

  /// Takes the value out of the entry, and returns it.
  #[inline]
  pub fn remove(self) -> V {
    self.remove_entry().1
  }

  /// Take the ownership of the key and value from the map.
  #[inline]
  pub fn remove_entry(self) -> (K, V) {
    unsafe {
      self.table.erase_no_drop(&self.elem);
      self.elem.read()
    }
  }
}

unsafe impl<K, V> Send for OccupiedEntryMut<'_, K, V>
  where K: Send, V: Send {}

unsafe impl<K, V> Sync for OccupiedEntryMut<'_, K, V>
  where K: Sync, V: Sync {}

impl<K: Debug, V: Debug> Debug for OccupiedEntryMut<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_struct("OccupiedEntryMut")
      .field("key", self.key())
      .field("value", self.get())
      .finish()
  }
}

/// A view into a vacant entry in a `HashMap`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
pub struct VacantEntry<'a, K, V> {
  pub(crate) hash: u64,
  pub(crate) key: K,
  pub(crate) table: &'a mut RawTable<(K, V)>,
}

impl<K: Debug, V> Debug for VacantEntry<'_, K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
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
  /// ```ignore
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::Entry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  ///
  /// if let Entry::Vacant(v) = map.rustc_entry("poneyland") {
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
  /// ```ignore
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cuda::Entry;
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  ///
  /// if let Entry::Vacant(o) = map.rustc_entry("poneyland") {
  ///   o.insert(37);
  /// }
  /// assert_eq!(map["poneyland"], 37);
  /// ```
  pub fn insert(self, value: V) -> &'a mut V {
    debug_assert!(self.hash != 0);
    let bucket = self.table.insert_no_grow(self.hash, (self.key, value));
    unsafe { &mut bucket.as_mut().1 }
  }

  /// Sets the value of the entry with the RustcVacantEntry's key,
  /// and returns a OccupiedEntry.
  ///
  /// # Examples
  ///
  /// ```ignore
  /// use hashmap_cuda::{ HashMap, Entry };
  ///
  /// let mut map: HashMap<&str, u32> = HashMap::new();
  ///
  /// if let Entry::Vacant(v) = map.rustc_entry("poneyland") {
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

/// A view into a vacant entry in a `HashMap`.
/// It is part of the [`RawEntryMut`] enum.
///
/// [`RawEntryMut`]: enum.RawEntryMut.html
pub struct VacantEntryMut<'a, K, V, S> {
  pub(crate) table: &'a mut RawTable<(K, V)>,
  pub(crate) hash_builder: &'a S,
}

impl<'a, K, V, S> VacantEntryMut<'a, K, V, S> {
  /// Sets the value of the entry with the VacantEntry's key,
  /// and returns a mutable reference to it.
  #[inline]
  pub fn insert(self, key: K, value: V) -> (&'a mut K, &'a mut V)
    where K: Hash, S: BuildHasher
  {
    let mut hasher = self.hash_builder.build_hasher();
    key.hash(&mut hasher);
    self.insert_hashed_nocheck(hasher.finish(), key, value)
  }

  /// Sets the value of the entry with the VacantEntry's key,
  /// and returns a mutable reference to it.
  #[inline]
  #[allow(clippy::shadow_unrelated)]
  pub fn insert_hashed_nocheck(self, hash: u64, key: K, value: V)
    -> (&'a mut K, &'a mut V) where K: Hash, S: BuildHasher
  {
    let hash_builder = self.hash_builder;
    self.insert_with_hasher(hash, key, value, |k| make_hash(hash_builder, k))
  }

  /// Set the value of an entry with a custom hasher function.
  #[inline]
  pub fn insert_with_hasher<H>(
    self,
    hash: u64,
    key: K,
    value: V,
    hasher: H,
  ) -> (&'a mut K, &'a mut V) where H: Fn(&K) -> u64
  {
    unsafe {
      let elem = self.table.insert(hash, (key, value), |x| hasher(&x.0));
      let &mut (ref mut k, ref mut v) = elem.as_mut();
      (k, v)
    }
  }

  #[inline]
  fn insert_entry(self, key: K, value: V) -> OccupiedEntryMut<'a, K, V>
    where K: Hash, S: BuildHasher
  {
    let hash_builder = self.hash_builder;
    let mut hasher = self.hash_builder.build_hasher();
    key.hash(&mut hasher);

    let elem = self.table.insert(hasher.finish(), (key, value), |k| {
      make_hash(hash_builder, &k.0)
    });
    OccupiedEntryMut {
      elem,
      table: self.table,
    }
  }
}

impl<K: Debug, V: Debug, S> Debug for VacantEntryMut<'_, K, V, S> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_struct("VacantEntryMut").finish()
  }
}
