// Copyright (C) 2017 cripes-source Project Contributors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-Apache
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>,
// at your option. This file may not be copied, modified, or
// distributed except according to those terms.
//! Source-tracking utilities for use by diagnostics tools.
#![feature(str_internals)]
#![feature(conservative_impl_trait)]

extern crate unicode_width;
extern crate core;

pub mod pos;
pub mod io;
//pub mod render;
pub mod storage;
pub mod diagnostic;

pub use pos::{span, Span, Index, Offset, Contains};
pub use storage::{FileMap, SourceMap, Mapper};
