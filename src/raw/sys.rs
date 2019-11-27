// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

//! `sys` implements [`hashmap_random_keys`] as a drop-in replacement
//! for [`sys`] in the standard library

use core::{
  mem,
  ptr,
  slice
};

pub fn hashmap_random_keys() -> (u64, u64) {
  let mut v = (0, 0);
  unsafe {
    let view = slice::from_raw_parts_mut(&mut v as *mut _ as *mut u8,
      mem::size_of_val(&v));
    //TODO: cuRAND (https://docs.nvidia.com/cuda/curand/host-api-overview.html)
  }
  v
}
