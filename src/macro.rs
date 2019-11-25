// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

/// A simplistic `hashmap!` macro for easily creating a `HashMap` like
/// a `Vector` from `std::vec`.
///
/// # Examples
///
/// ```
/// let book_reviews = hashmap![(
///   "Adventures of Huckleberry Finn".to_string()
///   "My favorite book.".to_string()
/// ), (
///   "Grimms' Fairy Tales".to_string(),
///   "Masterpiece.".to_string()
/// )];
///
/// assert_eq!(book_reviews.len() == 2);
/// assert!(book_reviews.contains_key("Grimms' Fairy Tales"));
/// ```
#[macro_export]
macro_rules! hashmap {
  ($($key:expr, $val:expr),*) => {{
      let mut hm = $crate::HashMap::new();
      $(
        hm.insert($key, $val);
      )*
      hm
  }};

  ($size:expr, $($key:expr, $val:expr),*) => {{
    let size = match usize::try_from($size) {
      Ok(sz) => sz,
      Err(e) => panic!(e)
    };
    let mut hm = $crate::HashMap::with_capacity(size);
    #(
      hm.insert($key, $val);
    )*
    hm
  }}
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn new_hashmap() {
    let book_reviews = hashmap![(
      "Adventures of Huckleberry Finn".to_string()
      "My favorite book.".to_string()
    ), (
      "Grimms' Fairy Tales".to_string(),
      "Masterpiece.".to_string()
    )];

    assert_eq!(book_reviews.len() == 2);
    assert!(book_reviews.contains_key("Grimms' Fairy Tales"));
  }

  #[test]
  fn new_hashmap_with_capacity() {
    let book_reviews = hashmap![2, (
      "Adventures of Huckleberry Finn".to_string()
      "My favorite book.".to_string()
    ), (
      "Grimms' Fairy Tales".to_string(),
      "Masterpiece.".to_string()
    )];
    assert_eq!(book_reviews.len() == 2);
    assert!(book_reviews.contains_key("Grimms' Fairy Tales"));
  }

  #[test]
  #[should_panic]
  fn new_hashmap_with_overcapacity() {
    let book_reviews = hashmap![1, (
      "Adventures of Huckleberry Finn".to_string()
      "My favorite book.".to_string()
    ), (
      "Grimms' Fairy Tales".to_string(),
      "Masterpiece.".to_string()
    )];
  }
}
