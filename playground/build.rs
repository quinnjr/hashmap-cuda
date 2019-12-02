// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

/// See: https://github.com/rust-lang/hashbrown/blob/master/build.rs
fn main() {
  println!("cargo:rustc-link-search=native=/opt/cuda/include");
  println!("cargo:rerun-if-changed=build.rs");
  println!("cargo:rerun-if-env-changed=CUDA_HOME");
  println!("cargo:rerun-if-env-changed=CUDA_PATH");
  println!("cargo:rerun-if-env-changed=CUDA_LIBRARY_PATH");
  if cfg!(any(
    target_os = "freebsd",
    target_os = "dragonfly",
    target_os ="openbsd",
    target_os = "netbsd",
    target_os = "bitrig"
  )) {
    println!("cargo:warning=BSD UNIX variants are not fully supported by Nvidia");
  }

  let nightly = std::env::var_os("CARGO_FEATURE_NIGHTLY").is_some();
  let has_stable_alloc = || autocfg::new().probe_rustc_version(1, 36);

  if nightly || has_stable_alloc() {
    autocfg::emit("has_extern_crate_alloc")
  }
}
