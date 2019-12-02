// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

// See: https://github.com/rust-lang/hashbrown/blob/master/benches/bench.rs

#[feature(test)]

extern crate test;

use test::Bencher;

use hashmap_cuda::{ DefaultHashBuilder, HashMap };

const SIZE: usize = 1000;

type AHashMap<K, V> = HashMap<K, V, DefaultHashBuilder>;

#[derive(Clone, Copy, Debug)]
struct RandomKeys {
  state: usize
}

impl RandomKeys {
  fn new() -> Self {
    RandomKeys { state: 0 }
  }
}

impl Iterator for RandomKeys {
  type Item = usize;

  fn next(&mut self) -> Option<usize> {
    self.state = self.state.wrapping_add(1).wrapping_mul(3787392781);
    Some(self.state)
  }
}

macro_rules! bench_suite {
  ($bench_macro: ident, $bench_ahash_serial:ident,
    $bench_ahash_highbits:ident, $bench_ahash_random:ident) =>
  {
    $bench_macro!($bench_ahash_serial, AHashMap, 0..);
    $bench_macro!(
      $bench_ahash_highbits, AHashMap, (0..).map(usize::swap_bytes)
    );
    $bench_macro!($bench_ahash_random, AHashMap, RandomKeys::new());
  }
}

// TODO: implement benchmark suites

bench_suite!(
  bench_insert,
  insert_ahash_serial,
  insert_ahash_highbits,
  insert_ahash_random
);

bench_suite!(
  bench_insert_erase,
  insert_erase_ahash_serial,
  insert_erase_ahash_highbits,
  insert_erase_ahash_random
);

bench_suite!(
  bench_lookup,
  lookup_ahash_serial,
  lookup_ahash_highbits,
  lookup_ahash_random
);

bench_suite!(
  bench_lookup_fail,
  lookup_fail_ahash_serial,
  lookup_fail_ahash_highbits,
  lookup_fail_ahash_random
);

bench_suite!(
  bench_iter,
  iter_ahash_serial,
  iter_ahash_highbits,
  iter_ahash_random
);
