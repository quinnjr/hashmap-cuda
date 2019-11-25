// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

#![feature(try_reserve)]

use failure::Fail;

use core::{
  convert::From,
  fmt::{ Debug, Display, Formatter, Result as FmtResult },
};

macro_rules! error_enumeration {
  (
    $(
      $( #[$meta:meta] )?
      $name:ident => $cause:path
    ),*
  ) => {
    #[derive(Clone, Debug, Fail)]
    pub enum Error {
      $(
        $(#[$meta])?
        $name(#[fail(cause)] $cause),
      )*
    }

    $(
      $(#[$meta])?
      impl From<$cause> for Error {
        fn from(err: $cause) -> Self { Self::$name(err) }
      }
    )*
  };
}

error_enumeration! {
  AllocLayout => ::core::alloc::LayoutErr,
  #[feature(std)] BoxedError => ::std::boxed::Box<dyn ::std::error::Error>,
  CellBorrow => ::core::cell::BorrowError,
  Fail => failure::Error,
  Format => ::core::fmt::Error,
  ParseInt => ::core::num::ParseIntError,
  ParseFloat => ::core::num::ParseFloatError,
  #[feature(std)] StringError => ::std::string::String,
  TryFromInt => ::core::num::TryFromIntError,
  TryReserve => ::core::alloc::TryReserveError
}
