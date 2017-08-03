// Copyright (C) 2017 cripes-source Project Contributors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-Apache
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>,
// at your option. This file may not be copied, modified, or
// distributed except according to those terms.
//! IO utilities for reading source code into a SourceMap.

use std::io;
use std::cmp::min;
use std::str;
use core::str::utf8_char_width;

use unicode_width::UnicodeWidthChar;

use pos::{Index, Loc};
use storage::FileMap;
use storage::Grid;

// ----------------------------------------------------------------

/// Utility for handling partial UTF-8 characters gracefully
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct CharBuf {
    buf: [u8; 4],
    offset: u8,
}

impl CharBuf {
    fn process<'a>(&'a mut self, slice: &'a [u8]) -> Chars<'a> {
        Chars{buf: self, slice, index: 0}
    }

    /// Fetch the next character from `self` and/or the given IO object.
    pub fn next_from_stream<R: io::Read>(&mut self, mut r: R) -> io::Result<char> {
        let ofs = self.offset as usize;
        let w = { if self.offset == 0 { r.read_exact(&mut self.buf[0..1])?; }
                  utf8_char_width(self.buf[0]) };

        if w > 1 {
            r.read_exact(&mut self.buf[ofs..w])?;
        }

        str::from_utf8(&self.buf[..w])
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "Non-UTF-8 char encountered"))
            .and_then(|s| Ok(s.chars().next().unwrap()))
    }

    /// Fetch the next character from `self` and/or the given slice.
    pub fn next_from_slice(&mut self, slice: &[u8]) -> io::Result<Option<char>> {
        let ofs = self.offset as usize;

        if slice.is_empty() { Ok(None) }
        else {
            let mut i = 0;
            if self.offset == 0 {
                self.buf[0] = slice[i];
                i += 1;
            }
            let w = utf8_char_width(self.buf[0]);
            let m = min(slice.len() - i, w - ofs);

            self.buf[ofs..(ofs + m)].copy_from_slice(&slice[i..(i + m)]);
            self.offset += m as u8;

            assert!(self.offset <= w as u8);
            if self.offset == w as u8 {
                self.offset = 0; // reset for next time
                match str::from_utf8(&self.buf[..w]).ok() {
                    Some(s) => Ok(Some(s.chars().next().unwrap())),
                    None => Err(io::Error::new(io::ErrorKind::InvalidData, "Non-UTF-8 char encountered"))
                }
            } else {
                Ok(None)
            }
        }
    }
}
    
/// Iterator over the 
struct Chars<'a> {
    buf: &'a mut CharBuf,
    slice: &'a [u8],
    index: usize
}

impl<'a> Iterator for Chars<'a> {
    type Item = io::Result<char>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.slice.len() {
            None
        } else {
            match self.buf.next_from_slice(&self.slice[self.index..]) {
                Ok(Some(c)) => { self.index += c.len_utf8(); Some(Ok(c)) },
                Ok(None) => { self.index = self.slice.len(); None },
                Err(e) => Some(Err(e))
            }
        }
    }
}

// ----------------------------------------------------------------
// Reader

#[derive(Debug)]
pub struct Reader<'a, R> {
    /// Underlying `Read`er object.
    stream: R,
    /// FileMap to update with line endings and multibyte-char positions.
    file_map: &'a mut FileMap,
    /// Current offset in the stream.
    index: Index,
    /// Partial-character handler
    char_buf: CharBuf
}

impl<'a, R> Reader<'a, R> {
    pub fn new(file_map: &'a mut FileMap, stream: R) -> Self {
        Reader{stream, file_map, index: Index(0), char_buf: Default::default()}
    }

    fn update(&mut self, input: &[u8]) -> io::Result<usize> {
        for chr in self.char_buf.process(input) {
            match chr {
                Ok(c) => {
                    let byte_width = c.len_utf8() as u8;
                    let display_width = c.width().unwrap_or(0) as u8;

                    if c == '\n' {
                        self.file_map.line_indices.push(self.index);
                    }
                    if display_width != 1 {
                        self.file_map.non_monospaced_sequences.push((self.index, c).into());
                    }

                    self.index += byte_width as u32;
                },
                Err(e) => return Err(e),
            }
        }
        Ok(input.len())
    }

    pub fn loc(&self) -> Loc {
        self.file_map.loc_at(self.file_map.index_to_offset(self.index)).unwrap()
    }
}



impl<'a, R> io::Read for Reader<'a, R>
    where R: io::Read
{
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.stream.read(buf)
            .and_then(|n| self.update(&buf[0..n]))
    }
}

