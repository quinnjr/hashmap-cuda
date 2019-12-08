// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use crate::error::ErrorKind;

/// `Result` type for the `hashmap-cuda` crate.
///
/// Values returned from a function using `Result` will be of type T.
/// If no T is specified, T is a unit type.
///
/// Converts all Errors returned by `Result::Err` into the
/// crate [`ErrorKind`] enum.
///
/// [`ErrorKind`]: enum.ErrorKind.html
pub type Result<T=()> = ::core::result::Result<T, ErrorKind>;
