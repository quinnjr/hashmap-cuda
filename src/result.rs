// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use crate::error::Error;

cfg_if::cfg_if! {
  if #[feature(std)] {
    use std::convert::Into;

    /// `Result` type for the `hashmap-cuda` crate.
    ///
    /// Converts all Errors raised into the custom [`Error`] enum.
    ///
    /// [`Error`]: enum.Error.html
    pub type Result<T> = ::core::result::Result<T, impl Into<Error>>;
  } else {
    use core::convert::Into;

    /// `Result` type for the `hashmap-cuda` crate.
    ///
    /// Converts all Errors raised into the custom [`Error`] enum.
    ///
    /// [`Error`]: enum.Error.html
    pub type Result<T> = ::std::result::Result<T, impl Into<Error>>;
  }
}
