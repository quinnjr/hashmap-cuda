// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use core::{
  cmp,
  hash::{ BuildHasher, Hasher },
  mem,
  ptr
};

#[cfg(feature = "ahash")]
pub type DefaultHashBuilder = ahash::ABuildHasher;

#[cfg(not(feature = "ahash"))]
pub enum DefaultHashBuilder {}

/// The default [`Hasher`] used by [`RandomState`].
///
/// TODO: Consider reimplementing hasher with CUDA-specific logic.
///
/// [`RandomState`]: struct.RandomState.html
/// [`Hasher`]: ../../hash/trait.Hasher.html
#[derive(Clone, Debug)]
pub struct DefaultHasher(pub SipHasher13);

impl DefaultHasher {
  /// Creates a new `DefaultHasher`.
  ///
  /// This hasher is not guaranteed to be the same as all other
  /// `DefaultHasher` instances, but is the same as all
  /// other `DefaultHasher` instances created
  /// through `new` or `default`.
  #[allow(deprecated)]
  pub fn new() -> Self {
    DefaultHasher(SipHasher13::new_with_keys(0, 0))
  }
}

impl Default for DefaultHasher {
  /// Creates a new `DefaultHasher` using `new`.
  /// See its documentation for more.
  fn default() -> Self {
    DefaultHasher::new()
  }
}

impl Hasher for DefaultHasher {
  fn write(&mut self, msg: &[u8]) {
    self.0.write(msg)
  }

  fn finish(&self) -> u64 {
    self.0.finish()
  }
}

impl BuildHasher for SipHasher13 {
  #[inline]
  fn build_hasher(&self) -> Self {
    Self::new_with_keys(self.k0, self.k1)
  }
}

impl BuildHasher for DefaultHasher {
  #[inline]
  fn build_hasher(&self) -> Self {
    Self::new_with_keys(self.k0, self.k1)
  }
}


/// An implementation of SipHash 1-3.
///
/// This is currently the default hashing function used by standard library
/// (e.g., `collections::HashMap` uses it by default).
///
/// See: <https://131002.net/siphash>
#[derive(Clone, Copy, Debug)]
pub struct SipHasher13 {
  k0: u64,
  k1: u64,
  length: usize, // how many bytes have been processed.
  state: State, // hash State,
  tail: u64, // unprocessed bytes le
  ntail: usize, // how many bytes in the tail are valid
}

#[derive(Clone, Copy, Debug)]
#[repr(C)]
struct State {
  v0: u64,
  v1: u64,
  v2: u64,
  v3: u64
}

// See: https://doc.rust-lang.org/src/core/hash/sip.rs.html#78
macro_rules! compress {
  ($state:expr) => ({
    compress!($state.v0, $state.v1, $state.v2, $state.v3)
  });
  ($v0:expr, $v1:expr, $v2:expr, $v3:expr) => ({
    $v0 = $v0.wrapping_add($v1); $v1 = $v1.rotate_left(13); $v1 ^= $v0;
    $v0 = $v0.rotate_left(32);
    $v2 = $v2.wrapping_add($v3); $v3 = $v3.rotate_left(16); $v3 ^= $v2;
    $v0 = $v0.wrapping_add($v3); $v3 = $v3.rotate_left(21); $v3 ^= $v0;
    $v2 = $v2.wrapping_add($v1); $v1 = $v1.rotate_left(17); $v1 ^= $v2;
    $v2 = $v2.rotate_left(32);
  });
}

/// Loads an integer of the desired type from a byte stream, in LE order. Uses
/// `copy_nonoverlapping` to let the compiler generate the most efficient way
/// to load it from a possibly unaligned address.
///
/// Unsafe because: unchecked indexing at i..i+size_of(int_ty)
macro_rules! load_int_le {
  ($buf:expr, $i:expr, $int_ty:ident) => ({
    debug_assert!($i + mem::size_of::<$int_ty>() <= $buf.len());
    let mut data = 0 as $int_ty;
    ptr::copy_nonoverlapping(
      $buf.get_unchecked($i),
      &mut data as *mut _ as *mut u8,
      mem::size_of::<$int_ty>()
    );
    data.to_le()
  });
}

/// Loads an u64 using up to 7 bytes of a byte slice.
///
/// Unsafe because: unchecked indexing at start..start+len
#[inline]
unsafe fn u8to64_le(buf: &[u8], start: usize, len: usize) -> u64 {
  debug_assert!(len < 8);
  let mut i = 0; // current byte index (from LSB) in the output u64
  let mut out = 0;
  if i + 3 < len {
    out = load_int_le!(buf, start + i, u32) as u64;
    i += 4;
  }
  if i + 1 < len {
    out |= (load_int_le!(buf, start + i, u16) as u64) << (i * 8);
    i += 2
  }
  if i < len {
    out |= (*buf.get_unchecked(start + i) as u64) << (i * 8);
    i += 1;
  }
  debug_assert_eq!(i, len);
  out
}

impl SipHasher13 {
  /// Creates a new `SipHasher13` with the two initial keys set to 0.
  #[inline]
  pub fn new() -> SipHasher13 {
    SipHasher13::new_with_keys(0, 0)
  }

  /// Creates a `SipHasher13` that is keyed off the provided keys.
  #[inline]
  pub fn new_with_keys(key0: u64, key1: u64) -> SipHasher13 {
    let mut state = SipHasher13 {
      k0: key0,
      k1: key1,
      length: 0,
      state: State {
        v0: 0,
        v1: 0,
        v2: 0,
        v3: 0
      },
      tail: 0,
      ntail: 0
    };
    state.reset();
    state
  }

  #[inline]
  fn reset(&mut self) {
    self.length = 0;
    self.state.v0 = self.k0 ^ 0x736f6d6570736575;
    self.state.v1 = self.k1 ^ 0x646f72616e646f6d;
    self.state.v2 = self.k0 ^ 0x6c7967656e657261;
    self.state.v3 = self.k1 ^ 0x7465646279746573;
    self.ntail = 0;
  }

  #[inline]
  fn short_write(&mut self, msg: &[u8]) {
    debug_assert!(msg.len() <= 8);
    let length = msg.len();
    self.length += length;

    let needed = 8 - self.ntail;
    let fill = cmp::min(length, needed);
    if fill == 8 {
      self.tail = unsafe { load_int_le!(msg, 0, u64) };
    } else {
      self.tail |= unsafe { u8to64_le(msg, 0, fill) } << (8 * self.ntail);
      if length < needed {
        self.ntail += length;
        return;
      }
    }
    self.state.v3 ^= self.tail;
    self.c_rounds(&mut self.state);
    self.state.v0 ^= self.tail;
    // Buffered tail is now flushed, process new input.
    self.ntail = length - needed;
    self.tail = unsafe { u8to64_le(msg, needed, self.ntail) };
  }

  #[inline]
  fn c_rounds(state: &mut State) {
    compress!(state);
  }

  #[inline]
  fn d_rounds(state: &mut State) {
    compress!(state);
    compress!(state);
    compress!(state);
  }
}

impl Hasher for SipHasher13 {
  #[inline]
  fn write_usize(&mut self, i: usize) {
    let bytes = unsafe {
      core::slice::from_raw_parts(&i as *const usize as *const u8,
        mem::size_of::<usize>())
    };
    self.short_write(bytes)
  }

  #[inline]
  fn write_u8(&mut self, i: u8) {
    self.short_write(&[i]);
  }

  #[inline]
  fn write(&mut self, msg: &[u8]) {
    let length = msg.len();
    self.length += length;

    let mut needed = 0;

    if self.ntail != 0 {
      needed = 8 - self.ntail;
      self.tail |= unsafe { u8to64_le(msg, 0, cmp::min(length, needed)) } << 8 * self.ntail;
      if length < needed {
        self.ntail += length;
        return
      } else {
        self.state.v3 ^= self.tail;
        self.c_rounds(&mut self.state);
        self.state.v0 ^= self.tail;
        self.ntail = 0;
      }
    }

    // Buffered tail is now flushed, process new input.
    let len = length - needed;
    let left = len & 0x7;

    let mut i = needed;
    while i < len - left {
      let mi = unsafe { load_int_le!(msg, i, u64) };

      self.state.v3 ^= mi;
      self.c_rounds(&mut self.state);
      self.state.v0 ^= mi;
      i += 8;
    }

    self.tail = unsafe { u8to64_le(msg, i, left) };
    self.ntail = left;
  }

  #[inline]
  fn finish(&self) -> u64 {
    let mut state = self.state;
    let b: u64 = ((self.length as u64 & 0xff) << 56) | self.tail;

    state.v3 ^= b;
    self.c_rounds(&mut state);
    state.v0 ^= b;
    state.v2 ^= 0xff;
    self.d_rounds(&mut state);
    state.v0 ^ state.v1 ^ state.v2 ^ state.v3
  }
}

impl Default for SipHasher13 {
  #[inline]
  fn default() -> SipHasher13 {
    Self::new_with_keys(0, 0)
  }
}
