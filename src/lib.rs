// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

// ignore-tidy-filelength

//! # hashmap-cuda
//!
//! `hashmap-cuda` is a re-implementation of [`std::collections::HashMap`][1]
//! and [`hashbrown::HashMap`][2] which utilizes GPU-powered
//! parallelization in place of the SIMD implementation from [hashbrown][3].
//!
//! `hashmap-cuda` attempts to maintain the same API as
//! [`std::collections::HashMap`][1] to allow for it's use as a drop-in
//! replacement.
//!
//! Presently, `hashmap-cuda` depends on `std` and is not usable as a
//! replacement for [`hashbrown`][3] in `#![no_std]` applications.
//!
//! `hashmap-cuda` was initially conceived as a final project for students
//! at [Florida International University's Department of Computing and
//! Information Science](https://www.cis.fiu.edu/) for their CDA-4101
//! Structured Computer Organization final project.
//!
//! `hashmap-cuda` is released under the permissive ISC license.
//! See: [LICENSE](./LICENSE)
//!
//! [1]: https://doc.rust-lang.org/src/std/collections/hash/map.rs.html
//! [2]: https://docs.rs/hashbrown/0.6.3/hashbrown/struct.HashMap.html
//! [3]: https://docs.rs/hashbrown/0.6.3/hashbrown/struct.HashMap.html

#![feature(try_reserve, hashmap_internals, todo_macro)]

#![cfg_attr(
  debug_assertions,
  allow(dead_code, unused_variables, unused_imports)
)]

#![cfg_attr(
  debug_assertions,
  warn(missing_docs)
)]

#![cfg_attr(
  not(debug_assertions),
  deny(missing_docs, unused_variables, unused_imports)
)]

#![cfg_attr(
  feature = "nightly",
  feature(
    alloc_layout_extra,
    allocator_api,
    ptr_offset_from,
    core_intrinsics,
    dropck_eyepatch
  )
)]

#![allow(
  clippy::doc_markdown,
  clippy::module_name_repitions,
  clippy::must_use_candidate
)]

#![deny(clippy::correctness, clippy::complexity, clippy::perf)]

mod default_hasher;
mod entry;
mod error;
mod iterator;
mod keys;
// mod macro;
mod random_state;
mod result;
mod swiss_table;
mod values;

pub use crate::{
  default_hasher::*,
  entry::*,
  error::Error,
  iterator::*,
  keys::*,
  // macro::hashmap,
  random_state::*,
  result::Result,
  swiss_table::*,
  values::*
};

pub mod prelude;

#[derive(Clone, Debug)]
pub struct HashMap<K, V, S = RandomState> {
  capacity: usize
}

impl<K: Hash + Eq, V> HashMap<K, V, RandomState> {
  /// Creates an empty `Hashmap`.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap-cuda::HashMap;
  /// let mut map: HashMap<&str, i64> = HashMap::new();
  /// ```
  pub fn new() -> Self {
    Self::default()
  }

  /// Creates an empty `Hashmap` with a specified initial capacity.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap-cuda::HashMap;
  /// let mut map: HashMap<&str, i64> = HashMap::with_capacity(100);
  /// ```
  pub fn with_capacity(capacity: usize) -> Self {
    Self {
      capacity: capacity
    }
  }
}

impl <K, V, S> HashMap<K, V, S> where K: Eq + Hash, S: BuildHasher {
  /// Creates an empty `HashMap` which will use the given hash builder to hash
  /// keys.
  ///
  /// The created map has the default initial capacity.
  ///
  /// Warning: `hash_builder` is normally randomly generated, and
  /// is designed to allow HashMaps to be resistant to attacks that
  /// cause many collisions and very poor performance. Setting it
  /// manually using this function can expose a DoS attack vector.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::{HashMap, RandomState};
  ///
  /// let s = RandomState::new();
  /// let mut map = HashMap::with_hasher(s);
  /// map.insert(1, 2);
  /// ```
  pub fn with_hasher(hash_builder: S) -> Self {
    Self {
      capacity: 0
    }
  }

  /// Creates an empty `HashMap` with the specified capacity,
  /// using `hash_builder`
  /// to hash the keys.
  ///
  /// The hash map will be able to hold at least `capacity`
  /// elements without reallocating.
  /// If `capacity` is 0, the hash map will not allocate.
  ///
  /// Warning: `hash_builder` is normally randomly generated, and
  /// is designed to allow HashMaps to be resistant to attacks that
  /// cause many collisions and very poor performance. Setting it
  /// manually using this function can expose a DoS attack vector.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  /// use hashmap_cude::RandomState;
  ///
  /// let s = RandomState::new();
  /// let mut map = HashMap::with_capacity_and_hasher(10, s);
  /// map.insert(1, 2);
  /// ```
  pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S)
    -> Self
  {
    todo!()
  }

  /// Returns a reference to the map's [`BuildHasher`].
  ///
  /// [`BuildHasher`]&#x3A; ../../std/hash/trait.BuildHasher.html
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  /// use hashmap_cude::RandomState;
  ///
  /// let hasher = RandomState::new();
  /// let map: HashMap<i32, i32> = HashMap::with_hasher(hasher);
  /// let hasher: &RandomState = map.hasher();
  ///`
  pub fn hasher(&self) -> &S {
    todo!()
  }

  /// Reserves capacity for at least `additional` more elements to be inserted
  /// in the `HashMap`. The collection may reserve more space to avoid
  /// frequent reallocations.
  ///
  /// # Panics
  ///
  /// Panics if the new allocation size overflows [`usize`].
  ///
  /// [`usize`]&#x3A; ../../std/primitive.usize.html
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  /// let mut map: HashMap<&str, i32> = HashMap::new();
  /// map.reserve(10);
  ///`
  pub fn reserve(&mut self, additional: usize) {
    todo!()
  }

  /// Tries to reserve capacity for at least `additional` more elements to be inserted
  /// in the given `HashMap<K,V>`. The collection may reserve more space to avoid
  /// frequent reallocations.
  ///
  /// # Errors
  ///
  /// If the capacity overflows, or the allocator reports a failure, then an error
  /// is returned.
  ///
  /// # Examples
  ///
  /// `/// #![feature(try_reserve)]
  /// use hashmap_cuda::HashMap;
  /// let mut map: HashMap<&str, isize> = HashMap::new();
  /// map.try_reserve(10).expect("why is the test harness OOMing on 10 bytes?");
  ///`
  pub fn try_reserve(&mut self, additional: usize) -> Result<()>
  {
      // self.try_reserve(additional)
      //     .map_err(map_collection_alloc_err)
    todo!()
  }

  /// Shrinks the capacity of the map as much as possible. It will drop
  /// down as much as possible while maintaining the internal rules
  /// and possibly leaving some space in accordance with the resize policy.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<i32, i32> = HashMap::with_capacity(100);
  /// map.insert(1, 2);
  /// map.insert(3, 4);
  /// assert!(map.capacity() >= 100);
  /// map.shrink_to_fit();
  /// assert!(map.capacity() >= 2);
  ///`
  pub fn shrink_to_fit(&mut self) {
    todo!()
  }

  /// Shrinks the capacity of the map with a lower limit. It will drop
  /// down no lower than the supplied limit while maintaining the internal rules
  /// and possibly leaving some space in accordance with the resize policy.
  ///
  /// Panics if the current capacity is smaller than the supplied
  /// minimum capacity.
  ///
  /// # Examples
  ///
  /// `/// #![feature(shrink_to)]
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<i32, i32> = HashMap::with_capacity(100);
  /// map.insert(1, 2);
  /// map.insert(3, 4);
  /// assert!(map.capacity() >= 100);
  /// map.shrink_to(10);
  /// assert!(map.capacity() >= 10);
  /// map.shrink_to(0);
  /// assert!(map.capacity() >= 2);
  ///`
  pub fn shrink_to(&mut self, min_capacity: usize) {
    assert!(
      self.capacity() >= min_capacity,
      "Tried to shrink to a larger capacity"
    );
    todo!()
  }

  /// Gets the given key's corresponding entry in the map for in-place manipulation.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut letters = HashMap::new();
  ///
  /// for ch in "a short treatise on fungi".chars() {
  ///     let counter = letters.entry(ch).or_insert(0);
  ///     *counter += 1;
  /// }
  ///
  /// assert_eq!(letters[&'s'], 2);
  /// assert_eq!(letters[&'t'], 3);
  /// assert_eq!(letters[&'u'], 1);
  /// assert_eq!(letters.get(&'y'), None);
  ///`
  pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
    todo!()
  }

  /// Returns a reference to the value corresponding to the key.
  ///
  /// The key may be any borrowed form of the map's key type, but
  /// [`Hash`] and [`Eq`] on the borrowed form _must_ match those for
  /// the key type.
  ///
  /// [`Eq`]&#x3A; ../../std/cmp/trait.Eq.html
  /// [`Hash`]&#x3A; ../../std/hash/trait.Hash.html
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  /// map.insert(1, "a");
  /// assert_eq!(map.get(&1), Some(&"a"));
  /// assert_eq!(map.get(&2), None);
  ///`
  pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where K: Borrow<Q>, Q: Hash + Eq,
  {
    todo!()
  }

  /// Returns the key-value pair corresponding to the supplied key.
  ///
  /// The supplied key may be any borrowed form of the map's key type, but
  /// [`Hash`] and [`Eq`] on the borrowed form _must_ match those for
  /// the key type.
  ///
  /// [`Eq`]&#x3A; ../../std/cmp/trait.Eq.html
  /// [`Hash`]&#x3A; ../../std/hash/trait.Hash.html
  ///
  /// # Examples
  ///
  /// `/// #![feature(map_get_key_value)]
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  /// map.insert(1, "a");
  /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
  /// assert_eq!(map.get_key_value(&2), None);
  ///`
  pub fn get_key_value<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &V)>
    where K: Borrow<Q>, Q: Hash + Eq,
  {
    todo!()
  }

  /// Returns `true` if the map contains a value for the specified key.
  ///
  /// The key may be any borrowed form of the map's key type, but
  /// [`Hash`] and [`Eq`] on the borrowed form _must_ match those for
  /// the key type.
  ///
  /// [`Eq`]&#x3A; ../../std/cmp/trait.Eq.html
  /// [`Hash`]&#x3A; ../../std/hash/trait.Hash.html
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  /// map.insert(1, "a");
  /// assert_eq!(map.contains_key(&1), true);
  /// assert_eq!(map.contains_key(&2), false);
  ///`
  pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
    where K: Borrow<Q>, Q: Hash + Eq,
  {
    todo!()
  }

  /// Returns a mutable reference to the value corresponding to the key.
  ///
  /// The key may be any borrowed form of the map's key type, but
  /// [`Hash`] and [`Eq`] on the borrowed form _must_ match those for
  /// the key type.
  ///
  /// [`Eq`]&#x3A; ../../std/cmp/trait.Eq.html
  /// [`Hash`]&#x3A; ../../std/hash/trait.Hash.html
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  /// map.insert(1, "a");
  /// if let Some(x) = map.get_mut(&1) {
  ///     *x = "b";
  /// }
  /// assert_eq!(map[&1], "b");
  ///`
  pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where K: Borrow<Q>, Q: Hash + Eq,
  {
    todo!()
  }

  /// Inserts a key-value pair into the map.
  ///
  /// If the map did not have this key present, [`None`] is returned.
  ///
  /// If the map did have this key present, the value is updated, and the old
  /// value is returned. The key is not updated, though; this matters for
  /// types that can be `==` without being identical. See the [module-level
  /// documentation] for more.
  ///
  /// [`None`]&#x3A; ../../std/option/enum.Option.html#variant.None
  /// [module-level documentation]&#x3A; index.html#insert-and-complex-keys
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  /// assert_eq!(map.insert(37, "a"), None);
  /// assert_eq!(map.is_empty(), false);
  ///
  /// map.insert(37, "b");
  /// assert_eq!(map.insert(37, "c"), Some("b"));
  /// assert_eq!(map[&37], "c");
  ///`
  pub fn insert(&mut self, k: K, v: V) -> Option<V> {
    todo!()
  }

  /// Removes a key from the map, returning the value at the key if the key
  /// was previously in the map.
  ///
  /// The key may be any borrowed form of the map's key type, but
  /// [`Hash`] and [`Eq`] on the borrowed form _must_ match those for
  /// the key type.
  ///
  /// [`Eq`]&#x3A; ../../std/cmp/trait.Eq.html
  /// [`Hash`]&#x3A; ../../std/hash/trait.Hash.html
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  /// map.insert(1, "a");
  /// assert_eq!(map.remove(&1), Some("a"));
  /// assert_eq!(map.remove(&1), None);
  ///`
  pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where K: Borrow<Q>, Q: Hash + Eq,
  {
    todo!()
  }

  /// Removes a key from the map, returning the stored key and value if the
  /// key was previously in the map.
  ///
  /// The key may be any borrowed form of the map's key type, but
  /// [`Hash`] and [`Eq`] on the borrowed form _must_ match those for
  /// the key type.
  ///
  /// [`Eq`]&#x3A; ../../std/cmp/trait.Eq.html
  /// [`Hash`]&#x3A; ../../std/hash/trait.Hash.html
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// # fn main() {
  /// let mut map = HashMap::new();
  /// map.insert(1, "a");
  /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
  /// assert_eq!(map.remove(&1), None);
  /// # }
  ///`
  pub fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, V)>
    where K: Borrow<Q>, Q: Hash + Eq
  {
    todo!()
  }

  /// Retains only the elements specified by the predicate.
  ///
  /// In other words, remove all pairs `(k, v)` such that `f(&k,&mut v)` returns `false`.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map: HashMap<i32, i32> = (0..8).map(|x|(x, x*10)).collect();
  /// map.retain(|&k, _| k % 2 == 0);
  /// assert_eq!(map.len(), 4);
  ///`
  pub fn retain<F>(&mut self, f: F)
    where F: FnMut(&K, &mut V) -> bool
  {
    todo!()
  }
}

impl<K, V, S> HashMap<K, V, S> {
  /// Returns the number of elements the map can hold without reallocating.
  ///
  /// This number is a lower bound; the `HashMap<K, V>` might be able to hold
  /// more, but is guaranteed to be able to hold at least this many.
  ///
  /// `/// use hashmap-cuda::HashMap;
  /// let mut map: HashMap<&str, i64> = HashMap::with_capacity(100);
  /// assert!(map.capacity() >= 100);
  ///`
  pub fn capacity(&self) -> usize {
    self.capacity
  }

  /// An iterator visiting all keys in arbitrary order.
  /// The iterator element type is `&'a K`.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  /// map.insert("a", 1);
  /// map.insert("b", 2);
  /// map.insert("c", 3);
  ///
  /// for key in map.keys() {
  ///     println!("{}", key);
  /// }
  ///`
  pub fn keys(&self) -> Keys<'_, K, V> {
    todo!()
  }

  /// An iterator visiting all values in arbitrary order.
  /// The iterator element type is `&'a V`.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  /// map.insert("a", 1);
  /// map.insert("b", 2);
  /// map.insert("c", 3);
  ///
  /// for val in map.values() {
  ///     println!("{}", val);
  /// }
  ///`
  pub fn values(&self) -> Values<'_, K, V> {
    todo!()
  }

  /// An iterator visiting all values mutably in arbitrary order.
  /// The iterator element type is `&'a mut V`.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  ///
  /// map.insert("a", 1);
  /// map.insert("b", 2);
  /// map.insert("c", 3);
  ///
  /// for val in map.values_mut() {
  ///     *val = *val + 10;
  /// }
  ///
  /// for val in map.values() {
  ///     println!("{}", val);
  /// }
  ///`
  pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
    todo!()
  }

  /// An iterator visiting all key-value pairs in arbitrary order.
  /// The iterator element type is `(&'a K, &'a V)`.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  /// map.insert("a", 1);
  /// map.insert("b", 2);
  /// map.insert("c", 3);
  ///
  /// for (key, val) in map.iter() {
  ///     println!("key: {} val: {}", key, val);
  /// }
  ///`
  pub fn iter(&self) -> Iter<'_, K, V> {
    todo!()
  }

  /// An iterator visiting all key-value pairs in arbitrary order,
  /// with mutable references to the values.
  /// The iterator element type is `(&'a K, &'a mut V)`.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  /// map.insert("a", 1);
  /// map.insert("b", 2);
  /// map.insert("c", 3);
  ///
  /// // Update all values
  /// for (_, val) in map.iter_mut() {
  ///     *val *= 2;
  /// }
  ///
  /// for (key, val) in &map {
  ///     println!("key: {} val: {}", key, val);
  /// }
  ///`
  pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
    todo!()
  }

  /// Returns the number of elements in the map.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut a = HashMap::new();
  /// assert_eq!(a.len(), 0);
  /// a.insert(1, "a");
  /// assert_eq!(a.len(), 1);
  ///`
  pub fn len(&self) -> usize {
    todo!()
  }

  /// Returns `true` if the map contains no elements.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut a = HashMap::new();
  /// assert!(a.is_empty());
  /// a.insert(1, "a");
  /// assert!(!a.is_empty());
  ///`
  pub fn is_empty(&self) -> bool {
    todo!()
  }

  /// Clears the map, returning all key-value pairs as an iterator. Keeps the
  /// allocated memory for reuse.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut a = HashMap::new();
  /// a.insert(1, "a");
  /// a.insert(2, "b");
  ///
  /// for (k, v) in a.drain().take(1) {
  ///     assert!(k == 1 || k == 2);
  ///     assert!(v == "a" || v == "b");
  /// }
  ///
  /// assert!(a.is_empty());
  ///`
  pub fn drain(&mut self) -> Drain<'_, K, V> {
    todo!()
  }

  /// Clears the map, removing all key-value pairs. Keeps the allocated memory
  /// for reuse.
  ///
  /// # Examples
  ///
  /// `/// use hashmap_cuda::HashMap;
  ///
  /// let mut a = HashMap::new();
  /// a.insert(1, "a");
  /// a.clear();
  /// assert!(a.is_empty());
  ///`
  pub fn clear(&mut self) {
    todo!()
  }
}

impl<K, V, S> HashMap<K, V, S> where S: BuildHasher {
  /// Creates a raw entry builder for the HashMap.
  ///
  /// Raw entries provide the lowest level of control for searching and
  /// manipulating a map. They must be manually initialized with a hash and
  /// then manually searched. After this, insertions into a vacant entry
  /// still require an owned key to be provided.
  ///
  /// Raw entries are useful for such exotic situations as:
  ///
  /// * Hash memoization
  /// * Deferring the creation of an owned key until it is known to be required
  /// * Using a search key that doesn't work with the Borrow trait
  /// * Using custom comparison logic without newtype wrappers
  ///
  /// Because raw entries provide much more low-level control, it's much easier
  /// to put the HashMap into an inconsistent state which, while memory-safe,
  /// will cause the map to produce seemingly random results. Higher-level and
  /// more foolproof APIs like `entry` should be preferred when possible.
  ///
  /// In particular, the hash used to initialized the raw entry must still be
  /// consistent with the hash of the key that is ultimately stored in the entry.
  /// This is because implementations of HashMap may need to recompute hashes
  /// when resizing, at which point only the keys are available.
  ///
  /// Raw entries give mutable access to the keys. This must not be used
  /// to modify how the key would compare or hash, as the map will not re-evaluate
  /// where the key should go, meaning the keys may become "lost" if their
  /// location does not reflect their state. For instance, if you change a key
  /// so that the map now contains keys which compare equal, search may start
  /// acting erratically, with two keys randomly masking each other. Implementations
  /// are free to assume this doesn't happen (within the limits of memory-safety).
  pub fn raw_entry_mut(&mut self) -> RawEntryBuilderMut<'_, K, V, S> {
    todo!()
  }

  /// Creates a raw immutable entry builder for the HashMap.
  ///
  /// Raw entries provide the lowest level of control for searching and
  /// manipulating a map. They must be manually initialized with a hash and
  /// then manually searched.
  ///
  /// This is useful for
  /// * Hash memoization
  /// * Using a search key that doesn't work with the Borrow trait
  /// * Using custom comparison logic without newtype wrappers
  ///
  /// Unless you are in such a situation, higher-level and more foolproof APIs like
  /// `get` should be preferred.
  ///
  /// Immutable raw entries have very limited use; you might instead want `raw_entry_mut`.
  pub fn raw_entry(&self) -> RawEntryBuilder<'_, K, V, S> {
    todo!()
  }
}

impl<K, V, S> PartialEq for HashMap<K, V, S>
  where K: Eq + Hash, V: PartialEq, S: BuildHasher
{
  fn eq(&self, other: &Self<K, V, S>) -> bool {
    if self.len() != other.len() {
      return false;
    }

    self.iter()
      .all(|(key, value)| {
        other.get(key).map_or(false, |v| *value == *v)
      })
  }
}

impl<K, V, S> Eq for HashMap<K, V, S>
  where K: Eq + Hash, V: Eq, S: BuildHasher
{
  // Intentionally Blank
}

impl<K, V, S> Debug for HashMap<K, V, S>
  where K: Eq + Hash + Debug, V: Debug, S: BuildHasher
{
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    f.debug_map().entries(self.iter()).finish()
  }
}

impl<K, V, S> Default for HashMap<K, V, S>
  where K: Eq + Hash, S: BuilderHash + Default
{
  fn default() -> Self {
    todo!()
  }
}

impl<K, Q: ?Sized, V, S> Index<&Q> for HashMap<K, V, S>
  where K: Eq + Hash + Borrow<Q>, Q: Eq + Hash, S: BuildHasher
{
  type Output = V;

  /// Returns a reference to the value corresponding to the supplied key.
  ///
  /// # Panics
  ///
  /// Panics if the key is not present in the `HashMap`.
  fn index(&self, key: &Q) -> &V {
    self.get(key).expect("no entry found for key")
  }
}

impl <K, V, S> Display for HashMap<K, V, S> {
  fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
    todo!()
  }
}

impl<'a, K, V, S> IntoIterator for &'a HashMap<K, V, S> {
  type Item = (&'a K, &'a V);
  type IntoIter = Iter<'a, K, V>;

  fn into_iter(self) -> Iter<'a, K, V> {
    self.iter()
  }
}

impl<'a, K, V, S> IntoIterator for &'a mut HashMap<K, V, S> {
  type Item = (&'a K, &'a mut V);
  type IntoIter = IterMut<'a, K, V>;

  fn into_iter(self) -> IterMut<'a, K, V> {
    self.iter_mut()
  }
}

impl<K, V, S> IntoIterator for HashMap<K, V, S> {
  type Item = (K, V);
  type IntoIter = IntoIter<K, V>;

  /// Creates a consuming iterator, that is, one that moves each key-value
  /// pair out of the map in arbitrary order. The map cannot be used after
  /// calling this.
  ///
  /// # Examples
  ///
  /// ```
  /// use hashmap_cuda::HashMap;
  ///
  /// let mut map = HashMap::new();
  /// map.insert("a", 1);
  /// map.insert("b", 2);
  /// map.insert("c", 3);
  ///
  /// // Not possible with .iter()
  /// let vec: Vec<(&str, i32)> = map.into_iter().collect();
  /// ```

  fn into_iter(self) -> IntoIter<K, V> {
    todo!()
  }
}

impl<K, V, S> FromIterator<(K, V)> for HashMap<K, V, S>
  where K: Eq + Hash, S: BuildHasher + Default
{
  fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T)
    -> HashMap<K, V, S>
  {
    let mut map = Self::with_hasher(Default::default());
    map.extend(iter);
    map
  }
}

impl<K, V, S> Extend<(K, V)> for HashMap<K, V, S>
  where K: Eq + Hash, S: BuildHasher
{
  fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
    todo!()
  }
}

impl<'a, K, V, S> Extend<(&'a K, &'a V)> for HashMap<K, V, S>
  where K: Eq + Hash + Copy, V: Copy, S: BuildHasher
{
  fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
    todo!()
  }
}

//
// fn map_entry<'a, K: 'a, V: 'a>(raw: base::RustcEntry<'a, K, V>) -> Entry<'a, K, V> {
//     match raw {
//         base::RustcEntry::Occupied(base) => Entry::Occupied(OccupiedEntry { base }),
//         base::RustcEntry::Vacant(base) => Entry::Vacant(VacantEntry { base }),
//     }
// }
//
//
// fn map_collection_alloc_err(err: hashbrown::CollectionAllocErr) -> TryReserveError {
//     match err {
//         hashbrown::CollectionAllocErr::CapacityOverflow => TryReserveError::CapacityOverflow,
//         hashbrown::CollectionAllocErr::AllocErr { layout } => TryReserveError::AllocError {
//             layout,
//             non_exhaustive: (),
//         },
//     }
// }
//
//
// fn map_raw_entry<'a, K: 'a, V: 'a, S: 'a>(
//     raw: base::RawEntryMut<'a, K, V, S>,
// ) -> RawEntryMut<'a, K, V, S> {
//     match raw {
//         base::RawEntryMut::Occupied(base) => RawEntryMut::Occupied(RawOccupiedEntryMut { base }),
//         base::RawEntryMut::Vacant(base) => RawEntryMut::Vacant(RawVacantEntryMut { base }),
//     }
// }
//
// #[allow(dead_code)]
// fn assert_covariance() {
//     fn map_key<'new>(v: HashMap<&'static str, u8>) -> HashMap<&'new str, u8> {
//         v
//     }
//     fn map_val<'new>(v: HashMap<u8, &'static str>) -> HashMap<u8, &'new str> {
//         v
//     }
//     fn iter_key<'a, 'new>(v: Iter<'a, &'static str, u8>) -> Iter<'a, &'new str, u8> {
//         v
//     }
//     fn iter_val<'a, 'new>(v: Iter<'a, u8, &'static str>) -> Iter<'a, u8, &'new str> {
//         v
//     }
//     fn into_iter_key<'new>(v: IntoIter<&'static str, u8>) -> IntoIter<&'new str, u8> {
//         v
//     }
//     fn into_iter_val<'new>(v: IntoIter<u8, &'static str>) -> IntoIter<u8, &'new str> {
//         v
//     }
//     fn keys_key<'a, 'new>(v: Keys<'a, &'static str, u8>) -> Keys<'a, &'new str, u8> {
//         v
//     }
//     fn keys_val<'a, 'new>(v: Keys<'a, u8, &'static str>) -> Keys<'a, u8, &'new str> {
//         v
//     }
//     fn values_key<'a, 'new>(v: Values<'a, &'static str, u8>) -> Values<'a, &'new str, u8> {
//         v
//     }
//     fn values_val<'a, 'new>(v: Values<'a, u8, &'static str>) -> Values<'a, u8, &'new str> {
//         v
//     }
//     fn drain<'new>(
//         d: Drain<'static, &'static str, &'static str>,
//     ) -> Drain<'new, &'new str, &'new str> {
//         d
//     }
// }

#[cfg(test)]
/// Testing module
/// See: [`std::collections::HashMap` tests](https://doc.rust-lang.org/src/std/collections/hash/map.rs.html#2605)
mod test {
  use super::*;

  use rand::{ thread_rng, Rng };

  #[cfg(feature = "std")]
  use std::{
    cell::RefCell,
    collections::TryReserveError::*
  };

  // https://github.com/rust-lang/rust/issues/62301
  fn _assert_hashmap_is_unwind_safe() {
    fn assert_unwind_safe<T: crate::panic::UnwindSafe>() {}
    assert_unwind_safe::<HashMap<(), crate::cell::UnsafeCell<()>>>();
  }

  #[test]
  fn test_zero_capacities() {
    type HM = HashMap<i32, i32>;

    let m = HM::new();
    assert_eq!(m.capacity(), 0);

    let m = HM::default();
    assert_eq!(m.capacity(), 0);

    let m = HM::with_hasher(RandomState::new());
    assert_eq!(m.capacity(), 0);

    let m = HM::with_capacity(0);
    assert_eq!(m.capacity(), 0);

    let m = HM::with_capacity_and_hasher(0, RandomState::new());
    assert_eq!(m.capacity(), 0);

    let mut m = HM::new();
    m.insert(1, 1);
    m.insert(2, 2);
    m.remove(&1);
    m.remove(&2);
    m.shrink_to_fit();
    assert_eq!(m.capacity(), 0);

    let mut m = HM::new();
    m.reserve(0);
    assert_eq!(m.capacity(), 0);
  }

  #[test]
  fn test_create_capacity_zero() {
    let mut m = HashMap::with_capacity(0);

    assert!(m.insert(1, 1).is_none());

    assert!(m.contains_key(&1));
    assert!(!m.contains_key(&0));
  }

  #[test]
  fn test_insert() {
    let mut m = HashMap::new();
    assert_eq!(m.len(), 0);
    assert!(m.insert(1, 2).is_none());
    assert_eq!(m.len(), 1);
    assert!(m.insert(2, 4).is_none());
    assert_eq!(m.len(), 2);
    assert_eq!(*m.get(&1).unwrap(), 2);
    assert_eq!(*m.get(&2).unwrap(), 4);
  }

  #[test]
  fn test_clone() {
    let mut m = HashMap::new();
    assert_eq!(m.len(), 0);
    assert!(m.insert(1, 2).is_none());
    assert_eq!(m.len(), 1);
    assert!(m.insert(2, 4).is_none());
    assert_eq!(m.len(), 2);
    let m2 = m.clone();
    assert_eq!(*m2.get(&1).unwrap(), 2);
    assert_eq!(*m2.get(&2).unwrap(), 4);
    assert_eq!(m2.len(), 2);
  }

  thread_local! {
    static DROP_VECTOR: RefCell<Vec<i32>> = RefCell::new(Vec::new())
  }

  #[derive(Hash, PartialEq, Eq)]
  struct Droppable {
    k: usize,
  }

  impl Droppable {
    fn new(k: usize) -> Droppable {
      DROP_VECTOR.with(|slot| {
      slot.borrow_mut()[k] += 1;
    });

      Droppable { k }
    }
  }

  impl Drop for Droppable {
    fn drop(&mut self) {
      DROP_VECTOR.with(|slot| {
        slot.borrow_mut()[self.k] -= 1;
      });
    }
  }

  impl Clone for Droppable {
    fn clone(&self) -> Droppable {
      Droppable::new(self.k)
    }
  }

  #[test]
  fn test_drops() {
    DROP_VECTOR.with(|slot| {
      *slot.borrow_mut() = vec![0; 200];
    });

    {
      let mut m = HashMap::new();

      DROP_VECTOR.with(|v| {
        for i in 0..200 {
          assert_eq!(v.borrow()[i], 0);
        }
      });

      for i in 0..100 {
        let d1 = Droppable::new(i);
        let d2 = Droppable::new(i + 100);
        m.insert(d1, d2);
      }

      DROP_VECTOR.with(|v| {
        for i in 0..200 {
          assert_eq!(v.borrow()[i], 1);
        }
      });

      for i in 0..50 {
        let k = Droppable::new(i);
        let v = m.remove(&k);

        assert!(v.is_some());

        DROP_VECTOR.with(|v| {
          assert_eq!(v.borrow()[i], 1);
          assert_eq!(v.borrow()[i + 100], 1);
        });
      }

      DROP_VECTOR.with(|v| {
        for i in 0..50 {
          assert_eq!(v.borrow()[i], 0);
          assert_eq!(v.borrow()[i + 100], 0);
        }

        for i in 50..100 {
          assert_eq!(v.borrow()[i], 1);
          assert_eq!(v.borrow()[i + 100], 1);
        }
      });
    }

    DROP_VECTOR.with(|v| {
      for i in 0..200 {
        assert_eq!(v.borrow()[i], 0);
      }
    });
  }

  #[test]
  fn test_into_iter_drops() {
    DROP_VECTOR.with(|v| {
      *v.borrow_mut() = vec![0; 200];
    });

    let hm = {
      let mut hm = HashMap::new();
      DROP_VECTOR.with(|v| {
        for i in 0..200 {
          assert_eq!(v.borrow()[i], 0);
        }
      });

      for i in 0..100 {
        let d1 = Droppable::new(i);
        let d2 = Droppable::new(i + 100);
        hm.insert(d1, d2);
      }

      DROP_VECTOR.with(|v| {
        for i in 0..200 {
          assert_eq!(v.borrow()[i], 1);
        }
      });

      hm
    };

    // By the way, ensure that cloning doesn't screw up the dropping.
    drop(hm.clone());

    {
      let mut half = hm.into_iter().take(50);
      DROP_VECTOR.with(|v| {
        for i in 0..200 {
          assert_eq!(v.borrow()[i], 1);
        }
      });

      for _ in half.by_ref() {}

      DROP_VECTOR.with(|v| {
        let nk = (0..100).filter(|&i| v.borrow()[i] == 1).count();

        let nv = (0..100).filter(|&i| v.borrow()[i + 100] == 1).count();

        assert_eq!(nk, 50);
        assert_eq!(nv, 50);
      });
    };

    DROP_VECTOR.with(|v| {
      for i in 0..200 {
        assert_eq!(v.borrow()[i], 0);
      }
    });
  }

  #[test]
  fn test_empty_remove() {
    let mut m: HashMap<i32, bool> = HashMap::new();
    assert_eq!(m.remove(&0), None);
  }

  #[test]
  fn test_empty_entry() {
    let mut m: HashMap<i32, bool> = HashMap::new();
    match m.entry(0) {
      Occupied(_) => panic!(),
      Vacant(_) => {}
    }
    assert!(*m.entry(0).or_insert(true));
    assert_eq!(m.len(), 1);
  }

  #[test]
  fn test_empty_iter() {
    let mut m: HashMap<i32, bool> = HashMap::new();
    assert_eq!(m.drain().next(), None);
    assert_eq!(m.keys().next(), None);
    assert_eq!(m.values().next(), None);
    assert_eq!(m.values_mut().next(), None);
    assert_eq!(m.iter().next(), None);
    assert_eq!(m.iter_mut().next(), None);
    assert_eq!(m.len(), 0);
    assert!(m.is_empty());
    assert_eq!(m.into_iter().next(), None);
  }

  #[test]
  fn test_lots_of_insertions() {
    let mut m = HashMap::new();

    // Try this a few times to make sure we never screw up the hashmap's
    // internal state.
    for _ in 0..10 {
      assert!(m.is_empty());
      for i in 1..1001 {
        assert!(m.insert(i, i).is_none());

        for j in 1..=i {
          let r = m.get(&j);
          assert_eq!(r, Some(&j));
        }

        for j in i + 1..1001 {
          let r = m.get(&j);
          assert_eq!(r, None);
        }
      }

      for i in 1001..2001 {
        assert!(!m.contains_key(&i));
      }

      // remove forwards
      for i in 1..1001 {
        assert!(m.remove(&i).is_some());
        for j in 1..=i {
        assert!(!m.contains_key(&j));
      }

      for j in i + 1..1001 {
        assert!(m.contains_key(&j));
      }
    }

      for i in 1..1001 {
        assert!(!m.contains_key(&i));
      }

      for i in 1..1001 {
        assert!(m.insert(i, i).is_none());
      }

      // remove backwards
      for i in (1..1001).rev() {
        assert!(m.remove(&i).is_some());

        for j in i..1001 {
          assert!(!m.contains_key(&j));
        }

        for j in 1..i {
          assert!(m.contains_key(&j));
        }
      }
    }
  }

  #[test]
  fn test_find_mut() {
    let mut m = HashMap::new();
    assert!(m.insert(1, 12).is_none());
    assert!(m.insert(2, 8).is_none());
    assert!(m.insert(5, 14).is_none());
    let new = 100;
    match m.get_mut(&5) {
      None => panic!(),
      Some(x) => *x = new,
    }
    assert_eq!(m.get(&5), Some(&new));
  }

  #[test]
  fn test_insert_overwrite() {
    let mut m = HashMap::new();
    assert!(m.insert(1, 2).is_none());
    assert_eq!(*m.get(&1).unwrap(), 2);
    assert!(!m.insert(1, 3).is_none());
    assert_eq!(*m.get(&1).unwrap(), 3);
  }

  #[test]
  fn test_insert_conflicts() {
    let mut m = HashMap::with_capacity(4);
    assert!(m.insert(1, 2).is_none());
    assert!(m.insert(5, 3).is_none());
    assert!(m.insert(9, 4).is_none());
    assert_eq!(*m.get(&9).unwrap(), 4);
    assert_eq!(*m.get(&5).unwrap(), 3);
    assert_eq!(*m.get(&1).unwrap(), 2);
  }

  #[test]
  fn test_conflict_remove() {
    let mut m = HashMap::with_capacity(4);
    assert!(m.insert(1, 2).is_none());
    assert_eq!(*m.get(&1).unwrap(), 2);
    assert!(m.insert(5, 3).is_none());
    assert_eq!(*m.get(&1).unwrap(), 2);
    assert_eq!(*m.get(&5).unwrap(), 3);
    assert!(m.insert(9, 4).is_none());
    assert_eq!(*m.get(&1).unwrap(), 2);
    assert_eq!(*m.get(&5).unwrap(), 3);
    assert_eq!(*m.get(&9).unwrap(), 4);
    assert!(m.remove(&1).is_some());
    assert_eq!(*m.get(&9).unwrap(), 4);
    assert_eq!(*m.get(&5).unwrap(), 3);
  }

  #[test]
  fn test_is_empty() {
    let mut m = HashMap::with_capacity(4);
    assert!(m.insert(1, 2).is_none());
    assert!(!m.is_empty());
    assert!(m.remove(&1).is_some());
    assert!(m.is_empty());
  }

  #[test]
  fn test_remove() {
    let mut m = HashMap::new();
    m.insert(1, 2);
    assert_eq!(m.remove(&1), Some(2));
    assert_eq!(m.remove(&1), None);
  }

  #[test]
  fn test_remove_entry() {
    let mut m = HashMap::new();
    m.insert(1, 2);
    assert_eq!(m.remove_entry(&1), Some((1, 2)));
    assert_eq!(m.remove(&1), None);
  }

  #[test]
  fn test_iterate() {
    let mut m = HashMap::with_capacity(4);
    for i in 0..32 {
      assert!(m.insert(i, i * 2).is_none());
    }
    assert_eq!(m.len(), 32);

    let mut observed: u32 = 0;

    for (k, v) in &m {
      assert_eq!(*v, *k * 2);
      observed |= 1 << *k;
    }
    assert_eq!(observed, 0xFFFF_FFFF);
  }

  #[test]
  fn test_keys() {
    let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
    let map: HashMap<_, _> = vec.into_iter().collect();
    let keys: Vec<_> = map.keys().cloned().collect();
    assert_eq!(keys.len(), 3);
    assert!(keys.contains(&1));
    assert!(keys.contains(&2));
    assert!(keys.contains(&3));
  }

  #[test]
  fn test_values() {
    let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
    let map: HashMap<_, _> = vec.into_iter().collect();
    let values: Vec<_> = map.values().cloned().collect();
    assert_eq!(values.len(), 3);
    assert!(values.contains(&'a'));
    assert!(values.contains(&'b'));
    assert!(values.contains(&'c'));
  }

  #[test]
  fn test_values_mut() {
    let vec = vec![(1, 1), (2, 2), (3, 3)];
    let mut map: HashMap<_, _> = vec.into_iter().collect();
    for value in map.values_mut() {
      *value = (*value) * 2
    }
    let values: Vec<_> = map.values().cloned().collect();
    assert_eq!(values.len(), 3);
    assert!(values.contains(&2));
    assert!(values.contains(&4));
    assert!(values.contains(&6));
  }

  #[test]
  fn test_find() {
    let mut m = HashMap::new();
    assert!(m.get(&1).is_none());
    m.insert(1, 2);
    match m.get(&1) {
      None => panic!(),
      Some(v) => assert_eq!(*v, 2),
    }
  }

  #[test]
  fn test_eq() {
    let mut m1 = HashMap::new();
    m1.insert(1, 2);
    m1.insert(2, 3);
    m1.insert(3, 4);

    let mut m2 = HashMap::new();
    m2.insert(1, 2);
    m2.insert(2, 3);

    assert!(m1 != m2);

    m2.insert(3, 4);

    assert_eq!(m1, m2);
  }

  #[test]
  fn test_show() {
    let mut map = HashMap::new();
    let empty: HashMap<i32, i32> = HashMap::new();

    map.insert(1, 2);
    map.insert(3, 4);

    let map_str = format!("{:?}", map);

    assert!(map_str == "{1: 2, 3: 4}" || map_str == "{3: 4, 1: 2}");
    assert_eq!(format!("{:?}", empty), "{}");
  }

  #[test]
  fn test_reserve_shrink_to_fit() {
    let mut m = HashMap::new();
    m.insert(0, 0);
    m.remove(&0);
    assert!(m.capacity() >= m.len());
    for i in 0..128 {
      m.insert(i, i);
    }
    m.reserve(256);

    let usable_cap = m.capacity();
    for i in 128..(128 + 256) {
      m.insert(i, i);
      assert_eq!(m.capacity(), usable_cap);
    }

    for i in 100..(128 + 256) {
      assert_eq!(m.remove(&i), Some(i));
    }
    m.shrink_to_fit();

    assert_eq!(m.len(), 100);
    assert!(!m.is_empty());
    assert!(m.capacity() >= m.len());

    for i in 0..100 {
      assert_eq!(m.remove(&i), Some(i));
    }
    m.shrink_to_fit();
    m.insert(0, 0);

    assert_eq!(m.len(), 1);
    assert!(m.capacity() >= m.len());
    assert_eq!(m.remove(&0), Some(0));
  }

  #[test]
  fn test_from_iter() {
    let xs = [(1, 1), (2, 2), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

    let map: HashMap<_, _> = xs.iter().cloned().collect();

    for &(k, v) in &xs {
      assert_eq!(map.get(&k), Some(&v));
    }

    assert_eq!(map.iter().len(), xs.len() - 1);
  }

  #[test]
  fn test_size_hint() {
    let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

    let map: HashMap<_, _> = xs.iter().cloned().collect();

    let mut iter = map.iter();

    for _ in iter.by_ref().take(3) {}

    assert_eq!(iter.size_hint(), (3, Some(3)));
  }

  #[test]
  fn test_iter_len() {
    let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

    let map: HashMap<_, _> = xs.iter().cloned().collect();

    let mut iter = map.iter();

    for _ in iter.by_ref().take(3) {}

    assert_eq!(iter.len(), 3);
  }

  #[test]
  fn test_mut_size_hint() {
    let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

    let mut map: HashMap<_, _> = xs.iter().cloned().collect();

    let mut iter = map.iter_mut();

    for _ in iter.by_ref().take(3) {}

    assert_eq!(iter.size_hint(), (3, Some(3)));
  }

  #[test]
  fn test_iter_mut_len() {
    let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

    let mut map: HashMap<_, _> = xs.iter().cloned().collect();

    let mut iter = map.iter_mut();

    for _ in iter.by_ref().take(3) {}

    assert_eq!(iter.len(), 3);
  }

  #[test]
  fn test_index() {
    let mut map = HashMap::new();

    map.insert(1, 2);
    map.insert(2, 1);
    map.insert(3, 4);

    assert_eq!(map[&2], 1);
  }

  #[test]
  #[should_panic]
  fn test_index_nonexistent() {
    let mut map = HashMap::new();

    map.insert(1, 2);
    map.insert(2, 1);
    map.insert(3, 4);

    map[&4];
  }

  #[test]
  fn test_entry() {
    let xs = [(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)];

    let mut map: HashMap<_, _> = xs.iter().cloned().collect();

    // Existing key (insert)
    match map.entry(1) {
      Vacant(_) => unreachable!(),
      Occupied(mut view) => {
        assert_eq!(view.get(), &10);
        assert_eq!(view.insert(100), 10);
      }
    }
    assert_eq!(map.get(&1).unwrap(), &100);
    assert_eq!(map.len(), 6);

    // Existing key (update)
    match map.entry(2) {
      Vacant(_) => unreachable!(),
      Occupied(mut view) => {
        let v = view.get_mut();
        let new_v = (*v) * 10;
        *v = new_v;
      }
    }
    assert_eq!(map.get(&2).unwrap(), &200);
    assert_eq!(map.len(), 6);

    // Existing key (take)
    match map.entry(3) {
      Vacant(_) => unreachable!(),
      Occupied(view) => {
        assert_eq!(view.remove(), 30);
      }
    }
    assert_eq!(map.get(&3), None);
    assert_eq!(map.len(), 5);

    // Inexistent key (insert)
    match map.entry(10) {
      Occupied(_) => unreachable!(),
      Vacant(view) => {
        assert_eq!(*view.insert(1000), 1000);
      }
    }
    assert_eq!(map.get(&10).unwrap(), &1000);
    assert_eq!(map.len(), 6);
  }

  #[test]
  fn test_entry_take_doesnt_corrupt() {
    #![allow(deprecated)] //rand
    // Test for #19292
    fn check(m: &HashMap<i32, ()>) {
      for k in m.keys() {
        assert!(m.contains_key(k), "{} is in keys() but not in the map?", k);
      }
    }

    let mut m = HashMap::new();
    let mut rng = thread_rng();

    // Populate the map with some items.
    for _ in 0..50 {
      let x = rng.gen_range(-10, 10);
      m.insert(x, ());
    }

    for _ in 0..1000 {
      let x = rng.gen_range(-10, 10);
      match m.entry(x) {
        Vacant(_) => {}
        Occupied(e) => {
          e.remove();
        }
      }

      check(&m);
    }
  }

  #[test]
  fn test_extend_ref() {
    let mut a = HashMap::new();
    a.insert(1, "one");
    let mut b = HashMap::new();
    b.insert(2, "two");
    b.insert(3, "three");

    a.extend(&b);

    assert_eq!(a.len(), 3);
    assert_eq!(a[&1], "one");
    assert_eq!(a[&2], "two");
    assert_eq!(a[&3], "three");
  }

  #[test]
  fn test_capacity_not_less_than_len() {
    let mut a = HashMap::new();
    let mut item = 0;

    for _ in 0..116 {
      a.insert(item, 0);
      item += 1;
    }

    assert!(a.capacity() > a.len());

    let free = a.capacity() - a.len();
    for _ in 0..free {
      a.insert(item, 0);
      item += 1;
    }

    assert_eq!(a.len(), a.capacity());

    // Insert at capacity should cause allocation.
    a.insert(item, 0);
    assert!(a.capacity() > a.len());
  }

  #[test]
  fn test_occupied_entry_key() {
    let mut a = HashMap::new();
    let key = "hello there";
    let value = "value goes here";
    assert!(a.is_empty());
    a.insert(key.clone(), value.clone());
    assert_eq!(a.len(), 1);
    assert_eq!(a[key], value);

    match a.entry(key.clone()) {
      Vacant(_) => panic!(),
      Occupied(e) => assert_eq!(key, *e.key()),
    }
    assert_eq!(a.len(), 1);
    assert_eq!(a[key], value);
  }

  #[test]
  fn test_vacant_entry_key() {
    let mut a = HashMap::new();
    let key = "hello there";
    let value = "value goes here";

    assert!(a.is_empty());
    match a.entry(key.clone()) {
      Occupied(_) => panic!(),
      Vacant(e) => {
        assert_eq!(key, *e.key());
        e.insert(value.clone());
      }
    }
    assert_eq!(a.len(), 1);
    assert_eq!(a[key], value);
  }

  #[test]
  fn test_retain() {
    let mut map: HashMap<i32, i32> = (0..100).map(|x| {
      (x, x * 10)
    })
      .collect();

    map.retain(|&k, _| k % 2 == 0);
    assert_eq!(map.len(), 50);
    assert_eq!(map[&2], 20);
    assert_eq!(map[&4], 40);
    assert_eq!(map[&6], 60);
  }

  #[test]
  fn test_try_reserve() {
    let mut empty_bytes: HashMap<u8, u8> = HashMap::new();

    const MAX_USIZE: usize = usize::MAX;

    if let Err(CapacityOverflow) = empty_bytes.try_reserve(MAX_USIZE) {
    } else {
      panic!("usize::MAX should trigger an overflow!");
    }

    if let Err(AllocError { .. }) = empty_bytes.try_reserve(MAX_USIZE / 8) {
    } else {
      panic!("usize::MAX / 8 should trigger an OOM!")
    }
  }

  #[test]
  fn test_raw_entry() {
    use super::RawEntryMut::{Occupied, Vacant};

    let xs = [(1i32, 10i32), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)];

    let mut map: HashMap<_, _> = xs.iter().cloned().collect();

    let compute_hash = |map: &HashMap<i32, i32>, k: i32| -> u64 {
      use core::hash::{BuildHasher, Hash, Hasher};

      let mut hasher = map.hasher().build_hasher();
      k.hash(&mut hasher);
      hasher.finish()
    };

    // Existing key (insert)
    match map.raw_entry_mut().from_key(&1) {
      Vacant(_) => unreachable!(),
      Occupied(mut view) => {
        assert_eq!(view.get(), &10);
        assert_eq!(view.insert(100), 10);
      }
    }
    let hash1 = compute_hash(&map, 1);
    assert_eq!(map.raw_entry().from_key(&1).unwrap(), (&1, &100));
    assert_eq!(
      map.raw_entry().from_hash(hash1, |k| *k == 1).unwrap(),
      (&1, &100)
    );
    assert_eq!(
      map.raw_entry().from_key_hashed_nocheck(hash1, &1).unwrap(),
      (&1, &100)
    );
    assert_eq!(map.len(), 6);

    // Existing key (update)
    match map.raw_entry_mut().from_key(&2) {
      Vacant(_) => unreachable!(),
      Occupied(mut view) => {
        let v = view.get_mut();
        let new_v = (*v) * 10;
        *v = new_v;
      }
    }
    let hash2 = compute_hash(&map, 2);
    assert_eq!(map.raw_entry().from_key(&2).unwrap(), (&2, &200));
    assert_eq!(
      map.raw_entry().from_hash(hash2, |k| *k == 2).unwrap(),
      (&2, &200)
    );
    assert_eq!(
      map.raw_entry().from_key_hashed_nocheck(hash2, &2).unwrap(),
      (&2, &200)
    );
    assert_eq!(map.len(), 6);

    // Existing key (take)
    let hash3 = compute_hash(&map, 3);
    match map.raw_entry_mut().from_key_hashed_nocheck(hash3, &3) {
      Vacant(_) => unreachable!(),
      Occupied(view) => {
        assert_eq!(view.remove_entry(), (3, 30));
      }
    }
    assert_eq!(map.raw_entry().from_key(&3), None);
    assert_eq!(map.raw_entry().from_hash(hash3, |k| *k == 3), None);
    assert_eq!(map.raw_entry().from_key_hashed_nocheck(hash3, &3), None);
    assert_eq!(map.len(), 5);

    // Nonexistent key (insert)
    match map.raw_entry_mut().from_key(&10) {
      Occupied(_) => unreachable!(),
      Vacant(view) => {
        assert_eq!(view.insert(10, 1000), (&mut 10, &mut 1000));
      }
    }
    assert_eq!(map.raw_entry().from_key(&10).unwrap(), (&10, &1000));
    assert_eq!(map.len(), 6);

    // Ensure all lookup methods produce equivalent results.
    for k in 0..12 {
      let hash = compute_hash(&map, k);
      let v = map.get(&k).cloned();
      let kv = v.as_ref().map(|v| (&k, v));

      assert_eq!(map.raw_entry().from_key(&k), kv);
      assert_eq!(map.raw_entry().from_hash(hash, |q| *q == k), kv);
      assert_eq!(map.raw_entry().from_key_hashed_nocheck(hash, &k), kv);

      match map.raw_entry_mut().from_key(&k) {
        Occupied(mut o) => assert_eq!(Some(o.get_key_value()), kv),
        Vacant(_) => assert_eq!(v, None),
      }
      match map.raw_entry_mut().from_key_hashed_nocheck(hash, &k) {
        Occupied(mut o) => assert_eq!(Some(o.get_key_value()), kv),
        Vacant(_) => assert_eq!(v, None),
      }
      match map.raw_entry_mut().from_hash(hash, |q| *q == k) {
        Occupied(mut o) => assert_eq!(Some(o.get_key_value()), kv),
        Vacant(_) => assert_eq!(v, None),
      }
    }
  }
}
