# hashmap-cuda
`hashmap-cuda` is a reimplementation of [`std::collections::HashMap`][1]
and [`hashbrown::HashMap`][2] which utilizes GPU-powered
parallelization in place of the SIMD implementation from [hashbrown][3].

`hashmap-cuda` attempts to maintain the same API as
[`std::collections::HashMap`][1] to allow for it's use as a drop-in
replacement.

Presently, `hashmap-cuda` depends on `std` and is not usable as a
replacement for [`hashbrown`][3] in `#![no_std]` applications.
Adoption for use in a fully `#![no_std]` environment may be done eventually.

`hashmap-cuda` was initially conceived as a final project for students
at [Florida International University's Department of Computing and
Information Science](https://www.cis.fiu.edu/) for their CDA-4101
Structured Computer Organization final project.

`hashmap-cuda` is released under the permissive ISC license.

See: [LICENSE](./LICENSE)

## Differences with `std::collections::HashMap` and `hashbrown::HashMap`
  1. Fewer `#[inline]` hints as of pre-v1.0.0. Additional `inline` hints will
     be added as the library stabilizes for increased compatibility.
  2. Less abstraction above raw FFI bindings that `std::collections`.

[1]: https://doc.rust-lang.org/src/std/collections/hash/map.rs.html
[2]: https://docs.rs/hashbrown/0.6.3/hashbrown/struct.HashMap.html
[3]: https://docs.rs/hashbrown/0.6.3/hashbrown/struct.HashMap.html
