// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use super::bitmask::BitMask;
use super::EMPTY;

use crate::result::Result;

use cuda::{
  driver::cuda_initialized,
  rand::CurandDefaultRng,
  runtime::{
    cuda_alloc_device,
    cuda_memcpy,
    CudaDevice,
    CudaMemcpyKind
  }
};

use core::{
  mem,
  ptr,
  slice
};

/// Number of random keys to consume.
const N: usize = 2;
/// Number of random keys to generate.
const GENCOUNT: usize = 30;
/// Add some additional randomness to the generated keys.
const RANDOMIZER: u64 = 65535;

/// Generate a tuple of u64 values to use as hashmap keys.
///
/// Utilizes the Curand library to generate `GENCOUNT` unsigned 32-bit
/// values on the GPU from with a psuedorandom seed of the raw 64-bit
/// value of the pointer to an empty array of `GENCOUNT` 32-bit
/// values.
///
/// Arbitrarily, values from the randomly generated array at indexes
/// 4 and 12 are returned to the consuming hasher.
///
/// # Panic
/// Problems in the CUDA driver will cause the program to panic early.
///
/// Improper randomization of keys will cause a panic. We want randomization!
///
/// # TODO
/// More psuedorandom selection of the final two hash keys.
/// More optimizations.
/// Convert to raw C and use ffi??
///
/// Frankly, Jospeh believes the hashmap key randomomization might
/// benefit from being written in C and the returned values then
/// being consumed in the Rust library.
///
/// The current `cuda` crate documentation made this function
/// feel very hack-y. Additional optimizations may definitely
/// be done here.
#[must_use]
#[inline]
pub fn hashmap_random_keys() -> Result<(u64, u64)> {
  // Ensure that CUDA is loaded.
  match cuda_initialized() {
    Ok(b) => assert_ne!(b, false),
    Err(e) => panic!("{:?}", e)
  }
  // Ensure we have a CUDA device ready.
  assert!(CudaDevice::count()? > 0);

  // Keys generation inside an unsafe block
  // TODO: Change to a compile-time sized array.
  // TODO: Change to using `Result` type for error propegation.
  // TODO: Triple-check for memory leaks.
  let keys: &[u32] = unsafe {
    // Allocate the internal block keys to a compile-time sized array of `GENCOUNT`.
    let mut keys: [u32; GENCOUNT] = [0u32; GENCOUNT];
    // Create a pointer to the key array.
    let keys_ptr: *mut [u32; GENCOUNT] = &mut keys;
    // Allocate `GENCOUNT` u32's on the GPU.
    let keys_cuda_ptr = cuda_alloc_device(GENCOUNT * mem::size_of::<u32>())
      .expect("Failed to allocate memory on the CUDA device");

    // Initialize a `cuda::rand::CurandDefaultRng` generator.
    let mut generator = match CurandDefaultRng::create() {
      Ok(g) => g,
      Err(e) => panic!("Failed to initialize CURAND generator: {} {}", e.get_code(), e.get_name().unwrap_or(""))
    };

    // Seed the generator from the u64 representation of the keys pointer.
    generator.set_seed_from_u64(keys_ptr as u64)
      .expect("Failed to set number of quasirandom dims");
    // Generate the random keys.
    generator.gen_u32(keys_cuda_ptr.cast::<u32>(), GENCOUNT)
      .expect("Failed to generate random numbers.");

    //TODO: assert_ne! here.

    // Copy the CUDA memory to system memory.
    cuda_memcpy(
      keys_ptr as *mut u32,
      keys_cuda_ptr as *const u32,
      GENCOUNT,
      CudaMemcpyKind::DeviceToHost
    )
      .expect("Failed to copy CUDA device memory");

    // Convert the keys pointer in to a Rust slice.
    slice::from_raw_parts(keys_ptr as *mut u32, N)
  };

  // Convert keys into valid u64s and multiplied by
  // a little more randomness (arbitrarily, the maximum
  // value of a usize).
  let keys: &[u64; 2] = &[
    (keys[0] as u64).wrapping_div(mem::size_of::<usize>() as u64),
    (keys[1] as u64).wrapping_div(mem::size_of::<usize>() as u64)
  ];

  assert!(keys[0] > 0);
  assert!(keys[1] > 0);
  // Ensure the keys are not the same value.
  // Panic if they are.
  // TODO: move assert_ne! inside the key generation block
  assert_ne!(keys[0], keys[1],
    "The psuedorandom generator returned two keys of the same value. That really isn't very random!");

  // Return a `Result::Ok` with our random keys.
  //
  // Returned tuple is conformant with prior implementation.
  // TODO: Use a sized u64 array instead.
  Ok((keys[0], keys[1]))
}

// Below, SwissTable implementation.
//
// TODO: Optimize for CUDA use.
// The below was mostly copied as-is from `hashbrown` with a
// minimum of understanding of optimizing the hash table.
//
// TODO: Optimization for use with CUDA.

// Use the native word size as the group size. Using a 64-bit group size on
// a 32-bit architecture will just end up being more expensive because
// shifts and multiplies will need to be emulated.
#[cfg(any(
    target_pointer_width = "64",
    target_arch = "aarch64",
    target_arch = "x86_64",
))]
type GroupWord = u64;
#[cfg(all(
    target_pointer_width = "32",
    not(target_arch = "aarch64"),
    not(target_arch = "x86_64"),
))]
type GroupWord = u32;

pub type BitMaskWord = GroupWord;
pub const BITMASK_STRIDE: usize = 8;
#[allow(clippy::cast_possible_truncation, clippy::unnecessary_cast)]
pub const BITMASK_MASK: BitMaskWord = 0x8080_8080_8080_8080_u64 as GroupWord;

/// Helper function to replicate a byte across a `GroupWord`.
#[inline]
fn repeat(byte: u8) -> GroupWord {
  let repeat = GroupWord::from(byte);
  let repeat = repeat | repeat.wrapping_shl(8);
  let repeat = repeat | repeat.wrapping_shl(16);
  // This last line is a no-op with a 32-bit GroupWord
  repeat | repeat.wrapping_shl(32)
}

/// Abstraction over a group of control bytes which can be scanned in
/// parallel.
///
/// This implementation uses a word-sized integer.
#[derive(Copy, Clone)]
pub struct Group(GroupWord);

// We perform all operations in the native endianess, and convert to
// little-endian just before creating a BitMask. The can potentially
// enable the compiler to eliminate unnecessary byte swaps if we are
// only checking whether a BitMask is empty.
#[allow(clippy::use_self)]
impl Group {
  /// Number of bytes in the group.
  pub const WIDTH: usize = mem::size_of::<Self>();

  /// Returns a full group of empty bytes, suitable for use as the
  /// initial value for an empty hash table.
  /// This value is explicitly declared as
  /// a static variable to ensure the address is consistent across
  /// dylibs.
  ///
  /// This is guaranteed to be aligned to the group size.
  #[inline]
  pub fn static_empty() -> &'static [u8] {
    union AlignedBytes {
      _align: Group,
      bytes: [u8; Group::WIDTH],
    };
    static ALIGNED_BYTES: AlignedBytes = AlignedBytes {
      bytes: [EMPTY; Group::WIDTH],
    };
    unsafe { &ALIGNED_BYTES.bytes }
  }

  /// Loads a group of bytes starting at the given address.
  #[inline]
  #[allow(clippy::cast_ptr_alignment)] // unaligned load
  pub unsafe fn load(ptr: *const u8) -> Self {
    Group(ptr::read_unaligned(ptr as *const _))
  }

  /// Loads a group of bytes starting at the given address,
  /// which must be aligned to `mem::align_of::<Group>()`.
  #[inline]
  #[allow(clippy::cast_ptr_alignment)]
  pub unsafe fn load_aligned(ptr: *const u8) -> Self {
    debug_assert_eq!(ptr as usize & (mem::align_of::<Self>() - 1), 0);
    Group(ptr::read(ptr as *const _))
  }

  /// Stores the group of bytes to the given address, which must be
  /// aligned to `mem::align_of::<Group>()`.
  #[inline]
  #[allow(clippy::cast_ptr_alignment)]
  pub unsafe fn store_aligned(self, ptr: *mut u8) {
    debug_assert_eq!(ptr as usize & (mem::align_of::<Self>() - 1), 0);
    ptr::write(ptr as *mut _, self.0);
  }

  /// Returns a `BitMask` indicating all bytes in the group which
  /// *may* have the given value.
  ///
  /// This function may return a false positive in certain cases where
  /// the byte in the group differs from the searched value only in
  /// its lowest bit. This is fine because:
  /// - This never happens for `EMPTY` and `DELETED`, only full entries.
  /// - The check for key equality will catch these.
  /// - This only happens if there is at least 1 true match.
  /// - The chance of this happening is very low (< 1% chance per byte).
  #[inline]
  pub fn match_byte(self, byte: u8) -> BitMask {
    // This algorithm is derived from
    // http://graphics.stanford.edu/~seander/bithacks.html##ValueInWord
    let cmp = self.0 ^ repeat(byte);
    BitMask((cmp.wrapping_sub(repeat(0x01)) & !cmp & repeat(0x80)).to_le())
  }

  /// Returns a `BitMask` indicating all bytes in the group which are
  /// `EMPTY`.
  #[inline]
  pub fn match_empty(self) -> BitMask {
    // If the high bit is set, then the byte must be either:
    // 1111_1111 (EMPTY) or 1000_0000 (DELETED).
    // So we can just check if the top two bits are 1 by ANDing them.
    BitMask((self.0 & (self.0 << 1) & repeat(0x80)).to_le())
  }

  /// Returns a `BitMask` indicating all bytes in the group which are
  /// `EMPTY` or `DELETED`.
  #[inline]
  pub fn match_empty_or_deleted(self) -> BitMask {
    // A byte is EMPTY or DELETED iff the high bit is set
    BitMask((self.0 & repeat(0x80)).to_le())
  }

  /// Returns a `BitMask` indicating all bytes in the group which are full.
  #[inline]
  pub fn match_full(&self) -> BitMask {
    self.match_empty_or_deleted().invert()
  }

  /// Performs the following transformation on all bytes in the group:
  /// - `EMPTY => EMPTY`
  /// - `DELETED => EMPTY`
  /// - `FULL => DELETED`
  #[inline]
  pub fn convert_special_to_empty_and_full_to_deleted(self) -> Self {
    // Map high_bit = 1 (EMPTY or DELETED) to 1111_1111
    // and high_bit = 0 (FULL) to 1000_0000
    //
    // Here's this logic expanded to concrete values:
    //   let full = 1000_0000 (true) or 0000_0000 (false)
    //   !1000_0000 + 1 = 0111_1111 + 1 = 1000_0000 (no carry)
    //   !0000_0000 + 0 = 1111_1111 + 0 = 1111_1111 (no carry)
    let full = !self.0 & repeat(0x80);
    Group(!full + (full >> 7))
  }
}
