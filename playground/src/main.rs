// Copyright (c) 2018-2019 Joseph R. Quinn <quinn.josephr@protonmail.com>
// SPDX-License-Identifier: ISC

use cuda::{
  driver::{ cuda_initialized, cuda_init },
  rand::CurandDefaultRng,
  runtime::{
    cuda_alloc_device,
    cuda_memcpy,
    get_driver_version,
    get_runtime_version,
    CudaDevice,
    CudaMemcpyKind
  }
};

use core::slice;
use core::mem;

const N: usize = 2;
const COUNT: usize = 20;
const SIZEOF_U64: usize = 8;

fn main() -> Result<()> {
  println!("Checking for CUDA platform...");

  if !cuda_initialized().unwrap_or(false) {
    println!("CUDA platform not initialized. Attempting to initialize...");
    cuda_init()?;
    assert!(cuda_initialized()? == true);
  };

  match CudaDevice::count() {
    Ok(count) => {
      assert!(count > 0);
      println!("Number of CUDA devices available: {}", count)
    },
    Err(_) => panic!("No CUDA devices detected")
  }

  assert!(get_driver_version()? > 0);
  assert!(get_runtime_version()? > 0);

  let keys: [u64; N] = unsafe {
    let mut k: [u32; COUNT] = [0u32; COUNT];
    // let keys_ptr: *mut u32 = libc::calloc(COUNT, mem::size_of::<u32>());
    //   // .cast::<u32>();
    let keys_ptr: *mut [u32; COUNT] = &mut k;

    let keys_cuda_ptr = cuda_alloc_device(
      COUNT * mem::size_of::<u32>()
    )?;

    let mut generator = CurandDefaultRng::create()?;

    generator.set_seed_from_u64(keys_ptr as u64)?;
    generator.gen_u32(keys_cuda_ptr.cast::<u32>(), COUNT)?;

    cuda_memcpy(
      keys_ptr as *mut u32,
      keys_cuda_ptr as *const u32,
      COUNT,
      CudaMemcpyKind::DeviceToHost
    )?;

    let s: &[u32] = slice::from_raw_parts(keys_ptr as *mut u32, COUNT);

    // libc::free(keys_ptr as *mut libc::c_void);

    let mut arr: [u64; N] = [s[2] as u64, s[12] as u64];

    for i in 0..s.len() {
      println!("{}", s[i]);
    }
    arr
  };

  for n in 0..keys.len() {
    println!("Key {}: {}", n, keys[n]);
  }

  Ok(())
}

mod error {
  use cuda::{
    driver,
    rand,
    runtime
  };

  use failure::Fail;

  type BoxedThing = std::boxed::Box<dyn std::any::Any + std::marker::Send + std::marker::Sync>;

  #[derive(Debug, Fail)]
  pub enum ErrorKind {
    #[fail(display = "{:?}", _0)]
    Driver(driver::CuError),
    #[fail(display = "{:?}", _0)]
    Runtime(runtime::CudaError),
    #[fail(display = "{:?}", _0)]
    Random(rand::CurandError),
    #[fail(display = "{:?}", _0)]
    Boxed(BoxedThing)
  }

  impl From<driver::CuError> for ErrorKind {
    fn from(err: driver::CuError) -> Self {
      Self::Driver(err)
    }
  }

  impl From<runtime::CudaError> for ErrorKind {
    fn from(err: runtime::CudaError) -> Self {
      Self::Runtime(err)
    }
  }

  impl From<rand::CurandError> for ErrorKind {
    fn from(err: rand::CurandError) -> Self {
      Self::Random(err)
    }
  }

  impl From<BoxedThing> for ErrorKind {
    fn from(err: BoxedThing) -> Self {
          Self::Boxed(err)
        }
  }
}

pub type Result<T> = std::result::Result<T, crate::error::ErrorKind>;
