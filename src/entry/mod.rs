// Copyright (c) 2019 Maia Duschatzky, Michael McCarthy, and Joseph Quinn.
// SPDX-License-Identifier: ISC

use std::fmt::{ Debug, Formatter, Result as FmtResult };

use crate::HashMap;

mod entry;
mod rustc_entry;

pub use self::{
  entry::*,
  rustc_entry::*
};
