// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

//! `sys` implements [`hashmap_random_keys`] as a drop-in replacement
//! for [`sys`] in the standard library

use core::{
  mem,
  slice
};

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

/// Number of random keys to consume.
const N: usize = 2;
/// Number of random keys to generate.
const GENCOUNT: usize = 30;

/// Generate a tuple of u64 values to use as hashmap keys.
///
/// Utilizes the Curand library to generate `GENCOUNT` unsigned 32-bit
/// values on the GPU from with a psuedorandom seed of the raw 64-bit
/// value of the pointer to an empty array of `GENCOUNT` 32-bit values.
///
/// Arbitrarily, values from the randomly generated array at indexes 4 and 12 are
/// returned to the consuming hasher.
///
/// # TODO:
/// More psuedorandom selection of the final two hash keys.
pub fn hashmap_random_keys() -> (u64, u64) {
  // Ensure that CUDA is loaded.
  assert!(cuda_initialized()? == true);
  // Ensure we have a CUDA device ready.
  assert!(CudaDevice::count()? > 0);

  // Keys generation inside an unsafe block
  let keys: [u64; N] = unsafe {
    // Allocate the internal block keys to a compile-time sized array of `GENCOUNT`.
    let keys: [u32; GENCOUNT] = [0u32; GENCOUNT];
    // Create a pointer to the key array.
    let keys_ptr: *mut [u32; GENCOUNT] = &mut k;
    // Allocate `GENCOUNT` u32's on the GPU.
    let keys_cuda_ptr = cuda_alloc_device(GENCOUNT * mem::size_of::<u32>());

    // Initialize a `cuda::rand::CurandDefaultRng` generator.
    let mut generator = match CurandDefaultRng::create() {
      Ok(g) => g,
      Err(e) => panic!("Failed to initialize CURAND generator: {}", e)
    };

    // Seed the generator from the u64 representation of the keys pointer.
    generator.set_seed_from_u64(keys_ptr as u64)
      .expect("Failed to set number of quasirandom dims");
    // Generate the random keys.
    generator.gen_u32(keys_cuda_ptr.cast::<u32>(), GENCOUNT)
      .expect("Failed to generate random numbers.");

    // Copy the CUDA memory to system memory.
    cuda_memcp(
      keys_ptr as *mut u32,
      keys_cuda_ptr as *const u32,
      GENCOUNT,
      CudaMemcpyKind::DeviceToHost
    )
      .expect("Failed to copy CUDA device memory");

    // Convert the keys pointer in to a Rust slice.
    let s: &[u32] = slice::from_raw_parts(keys_ptr as *mut u32, N);

    // Convert the values of the keys slice at indexes 4 as 12
    // into a u64 array with compile-time size known as `N`.
    let arr: [u64; N] = [s[4] as u64, s[12] as u64];

    arr
  };

  // Ensure the keys are not the same value.
  if keys[0] == keys[1] {
    panic!("The psuedorandom generator returned two keys of the same value. That really isn't very random!");
  }

  (keys[0], keys[1])
}
