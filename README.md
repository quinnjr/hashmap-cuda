# hashmap-cuda
`hashmap-cuda` is a reimplementation of [`std::collections::HashMap`]
and [`hashbrown`] which utilizes GPU-powered
parallelization in place of the SIMD implementation from [`hashbrown`].

`hashmap-cuda` attempts to maintain the same API as
[`std::collections::HashMap`] to allow for it's use as a drop-in
replacement.

Presently, `hashmap-cuda` is not guaranteed to not depend on `std` and is not usable as a
complete replacement for [`hashbrown`] in [`no_std`] applications.
Guaranteed [`no_std`] compatibility is a long-term goal for the project.

`hashmap-cuda` was initially conceived as a final project for students
at [Florida International University's Department of Computing and
Information Science](https://www.cis.fiu.edu/) for their CDA-4101
Structured Computer Organization final project.

`hashmap-cuda` is released under the permissive [ISC license](./LICENSE).

## Differences with `std::collections::HashMap` and `hashbrown::HashMap`
  1. Direct dependence on CUDA for use. `hashmap-cuda` does not fall back on [`std::collections::HashMap`] or [`hashbrown`] if CUDA is not available.
  2. Due to time constraints, implementation of [`SwissTable`] in the library is minimal, naïve, and could certainly be improved on.
  3. More `#[inline]` use instead of the `more-inline` feature of [`hashbown`] with the understanding that runtime performance benefits from proper `#[inline]` use is desirable when compiling for use with a system using at least one CUDA GPU over the compilation time concerns of embedded or limited resource systems.
  4. Less abstraction above raw bindings than [`std::collections::HashMap`].

## Notes
  1. Docbloc testing is not guaranteed to succeed due to the number of comments that need to be rewritten.

---
`CUDA` is Copyright © 2019 [NVIDIA Corporation](https://developer.nvidia.com/).

[`std::collections::HashMap`]: https://doc.rust-lang.org/src/std/collections/hash/map.rs.html
[`hashbrown`]: https://docs.rs/hashbrown
[`no_std`]: https://doc.rust-lang.org/1.7.0/book/no-stdlib.html
[`SwissTable`]: https://abseil.io/blog/20180927-swisstables
