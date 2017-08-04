// Copyright (C) 2017 cripes-source Project Contributors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-Apache
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>,
// at your option. This file may not be copied, modified, or
// distributed except according to those terms.
//! Utilities for storage and retrieval of text.
//!
use std;
use std::fs;
use std::ops::Range;
use std::path::Path;
use std::io::Read;

use core::fmt::Display;

use unicode_width::UnicodeWidthChar;

use io;
use pos::{span, Contains,  RangeLike, RelativeTo};
use pos::{Offset, Index, Span, Line, Column, Loc};

// ----------------------------------------------------------------
// LookupError

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub enum LookupError {
    /// [Offset](../pos/struct.Offset.html) does not correspond to anything in
    /// the mapper.
    InvalidOffset,

    /// [Location](../pos/struct.Loc.html) does not correspond to a valid
    /// file offset.
    ///
    /// This error occurs when e.g. requesting the offset that corresponds to
    /// a line/column where that particular line has fewer columns
    /// than requested.
    InvalidLocation,


    /// Requested span crosses a file boundary.
    FileBoundaryViolation,

    /// Requested span starts or ends in the middle of a codepoint.
    CodepointBoundaryViolation,

    /// Source code for the requested span is unavailable.
    SourceUnavailable
}

// ----------------------------------------------------------------
pub trait TryConvert<T, U> {
    type Error;

    fn try_convert(&self, t: T) -> Result<U, Self::Error>;
}

// ----------------------------------------------------------------
// Mapper

/// Common methods for types that can be indexed by span and offset.
pub trait Mapper<P> {
    /// Fetch the string slice that corresponds to the given span.
    fn fetch_snippet(&self, sp: Span<P>) -> Result<&str, LookupError>;

    /// Determine the span for the line that contains the given offset.
    fn fetch_line_span(&self, pos: P) -> Result<Span<P>, LookupError>;

    /// Determine the span for the lines that contain the given span.
    fn fetch_lines_span(&self, span: Span<P>) -> Result<Span<P>, LookupError>;

    /// Fetch the string slice that corresponds to the full line around the
    /// given offset.
    ///
    /// The returned slice _includes_ any line endings!
    fn fetch_line(&self, pos: P) -> Result<&str, LookupError> {
        self.fetch_line_span(pos)
            .and_then(|sp| self.fetch_snippet(sp))
    }

    /// Fetch the string slice for the range of full lines _around_ the given
    /// span.
    fn fetch_lines(&self, span: Span<P>) -> Result<&str, LookupError> {
        self.fetch_lines_span(span)
            .and_then(|sp| self.fetch_snippet(sp))
    }
}

// ----------------------------------------------------------------

/// Methods for translating between linear positions and
/// line-and-column-based locations.
pub trait Grid<P: Copy> {
    /// Translate a position into a line/column location.
    fn loc_at(&self, pos: P) -> Result<Loc, LookupError> {
        self.line_at(pos).and_then(|line| {
            self.column_at(pos).map(|column| Loc::at(line, column))
        })
    }

    /// Translate a line/column location into a linear position.
    fn position_at(&self, loc: Loc) -> Result<P, LookupError>;
    fn line_at(&self, pos: P) -> Result<Line, LookupError>;
    fn column_at(&self, pos: P) -> Result<Column, LookupError>;
}


// ----------------------------------------------------------------

/// Information on some sequence of bytes that, when decoded as UTF-8 and
/// rendered, occupies a column width different from its length.
#[derive(Copy, Clone, Debug, PartialEq, Hash)]
pub(crate) struct NonMonospacedSequence {
    index: Index,
    byte_width: u8,
    display_width: u8,
}

impl RangeLike for NonMonospacedSequence {
    type Position = Index;

    fn start(&self) -> Self::Position {
        self.index
    }

    fn end(&self) -> Self::Position {
        self.index + self.byte_width
    }
}

impl From<(Index, char)> for NonMonospacedSequence {
    fn from((index, c): (Index, char)) -> Self {
        NonMonospacedSequence{index,
                              byte_width: c.len_utf8() as u8,
                              display_width: c.width().unwrap_or(0) as u8}
    }
}

impl Contains<Index> for NonMonospacedSequence {
    fn contains(&self, idx: Index) -> bool {
        idx >= self.index && idx < self.index + self.byte_width
    }
}

// ----------------------------------------------------------------
// FileMap

/// information on a single file in the source map.
#[derive(Clone, Debug, PartialEq, Hash)]
pub struct FileMap {
    /// Name to display when presenting parts of this file in
    /// diagnostic output.
    name: String,

    source: Option<String>,

    /// (Byte) indices corresponding to the _beginnings_ of lines (index of
    /// first byte following a newline character) in `source`.
    ///
    /// The first entry in `line_indices` marks the start of the _second_ line
    /// in the source.
    pub(crate) line_indices: Vec<Index>,

    /// Locations of byte-sequences that occupy a number of columns that is not
    /// strictly equal to their length.
    pub(crate) non_monospaced_sequences: Vec<NonMonospacedSequence>,

    /// Region in the source map covered by this file.
    pub(crate) span: Span<Offset>,
}

impl FileMap {
    /// Initialize a FileMap from the given name and source buffer.
    pub fn from_source<S: AsRef<str>>(name: &str, source: S) -> Self {
        let source = source.as_ref();

        let line_indices = source.lines()
            .skip(1)
            .map(|s| s.as_ptr() as usize - source.as_ptr() as usize)
            .map(|d| Index(d as u32))
            .collect();

        let nmseqs = source
            .char_indices()
            .filter_map(move |(idx, c)| {
                let w = c.width().unwrap_or(0);
                if w != 1 {
                    Some(NonMonospacedSequence{index: Index(idx as u32),
                                               byte_width: c.len_utf8() as u8,
                                               display_width: w as u8})
                } else {
                    None
                }
            }).collect();


        FileMap{name: name.to_string(),
                source: Some(source.to_string()),
                line_indices: line_indices,
                non_monospaced_sequences: nmseqs,
                span: span(Offset(0), Offset(source.len() as u32))}
    }

    /// Fetch a [`Reader`](struct.Reader.html) for the filemap, reading from
    /// the given stream.
    pub fn read_from<R: Read>(&mut self, stream: R) -> io::Reader<R> {
        io::Reader::new(self, stream)
    }

    /// Convert a `self`-relative `Index` to an absolute `Offset`.
    pub fn index_to_offset(&self, idx: Index) -> Offset {
        self.span.start + idx
    }

    /// Convert an absolute `Offset` to a `self`-relative `Index`
    pub fn offset_to_index(&self, ofs: Offset) -> Index {
        ofs - self.span.start
    }


    /// Determine the (global) offset for the beginning of the line containing
    /// the given offset.
    fn line_start_offset(&self, ofs: Offset) -> Result<Offset, LookupError> {
        if ! self.span.contains(ofs) {
            Err(LookupError::InvalidOffset)
        } else {
            let idx = self.offset_to_index(ofs);
            match self.line_indices.binary_search(&idx) {
                Ok(n)  => Ok(self.index_to_offset(self.line_indices[n])),
                Err(0) => Ok(self.span.start),
                Err(n) => Ok(self.index_to_offset(self.line_indices[n - 1])),
            }
        }
    }

    /// Determine the (global) end offset for a span corresponding to the line
    /// containing the given offset.  If successful, the returned offset will
    /// point at the start of the _next_ line.
    fn line_end_offset(&self, ofs: Offset) -> Result<Offset, LookupError> {
        if ! self.span.contains(ofs) {
            Err(LookupError::InvalidOffset)
        } else {
            let idx = ofs - self.span.start;
            let m = self.line_indices.len();
            match self.line_indices.binary_search(&idx) {
                // `Ok(n)` => the line containing this index _starts_ at `self.line_indices[n]`
                Ok(n) =>
                    if m > n + 1 { Ok(self.index_to_offset(self.line_indices[n + 1])) }
                    else { Ok(self.span.end) },

                // `Err(n)` => the line containing this index _starts_ at `self.line_indices[n - 1]`
                Err(n) =>
                    if m == n { Ok(self.span.end) }
                    else { Ok(self.index_to_offset(Index(self.line_indices[n].0))) }
            }
        }
    }


    /// Get the total columnar width of the given span.  If the span crosses
    /// line boundaries,
    fn column_width(&self, sp: Span<Offset>) -> Result<u32, LookupError> {
        if ! self.span.intersects(sp) {
            Err(LookupError::InvalidOffset)
        } else if ! self.span.contains(sp) {
            Err(LookupError::FileBoundaryViolation)
        } else {
            let mut w = 0;
            let mut idx = self.offset_to_index(sp.start);
            let end_idx = self.offset_to_index(sp.end);
            while idx < end_idx {
                let n =
                    self.non_monospaced_sequences.binary_search_by_key(&idx, |nms| nms.index)
                    .unwrap_or_else(|n| n);
                match self.non_monospaced_sequences.get(n) {
                    Some(nms) =>
                        if nms.contains(end_idx) {
                            return Err(LookupError::CodepointBoundaryViolation);
                        } else if end_idx > *nms {
                            w += nms.index - idx + nms.display_width as u32;
                            idx = nms.range().end;
                        } else /* end_idx < *nms */ {
                            w += end_idx - idx;
                            break;
                        },
                    _ => { w += end_idx - idx;
                           break; }
                }
            }

            Ok(w)
        }
    }
}

impl Mapper<Offset> for FileMap {
    fn fetch_snippet(&self, sp: Span<Offset>) -> Result<&str, LookupError> {
        if self.source.is_none() {
            Err(LookupError::SourceUnavailable)
        } else if ! self.span.intersects(sp) {
            Err(LookupError::InvalidOffset)
        } else if ! self.span.contains(sp) {
            Err(LookupError::FileBoundaryViolation)
        } else {
            let rel: Range<usize> = sp.relative_to(self.span.start).into();
            Ok(&self.source.as_ref().unwrap()[rel])
        }
    }

    fn fetch_line_span(&self, ofs: Offset) -> Result<Span<Offset>, LookupError> {
        self.line_start_offset(ofs)
            .and_then(|s| self.line_end_offset(ofs)
                              .map(|e| span(s, e)))
    }

    fn fetch_lines_span(&self, sp: Span<Offset>) -> Result<Span<Offset>, LookupError> {
        self.line_start_offset(sp.start)
            .and_then(|s| self.line_end_offset(Offset(sp.end.0 - 1))
                              .map(|e| span(s, e)))
    }
}

impl TryConvert<Line, Index> for FileMap {
    type Error = LookupError;
    fn try_convert(&self, line: Line) -> Result<Index, Self::Error> {
        let li = line.index();
        if li == 0 {
            Ok(Index(0))
        } else if self.line_indices.len() < li - 1 {
            return Err(LookupError::InvalidOffset)
        } else {
            Ok(*unsafe { self.line_indices.get_unchecked(li - 1) })
        }
    }
}


struct ColumnSearch {
    index: Index,
    column: Column,
    target_column: Column
}
enum ColumnSearchStatus {
    TargetReached(Index),
    Overshot(Index, u16),
    Continue,
}


impl ColumnSearch {
    fn target_reached(&self) -> bool {
        self.column >= self.target_column
    }

    fn next(&mut self, fm: &FileMap) -> Result<ColumnSearchStatus, LookupError> {
        let next_line_index = fm.line_end_offset(self.index + fm.span.start)?.relative_to(fm.span.start);
        let remaining_columns = self.target_column - self.column;

        let nmso = fm.non_monospaced_sequences.get(fm.non_monospaced_sequences
                                                   .binary_search_by_key(&self.index, |nms| nms.index)
                                                   .unwrap_or_else(|n| n + 1));

        match nmso {
            Some(nms) if nms.index < next_line_index
                => Ok(self.update(nms)),
            _ =>
                if next_line_index - self.index >= remaining_columns as u32 {
                    self.index += remaining_columns;
                    self.column = self.target_column;
                    Ok(ColumnSearchStatus::TargetReached(self.index))
                } else {
                    Err(LookupError::InvalidLocation)
                }
        }
    }

    fn update(&mut self, nms: &NonMonospacedSequence) -> ColumnSearchStatus {
        let mut remaining_columns = self.target_column - self.column;
        if remaining_columns == 0 {
            ColumnSearchStatus::TargetReached(self.index)
        } else {
            // the "gap" between current index and the next non-monospaced
            // sequence _is_ monospaced.
            let buffer_gap = self.index - nms.index;
            if buffer_gap >= remaining_columns as u32 {
                self.column += buffer_gap as u16;
                self.index += buffer_gap;
                remaining_columns -= buffer_gap as u16;
            }
            if remaining_columns > 0 {
                self.column += nms.display_width as u16;
                self.index += nms.byte_width;
            }

            if self.target_reached() {
                ColumnSearchStatus::TargetReached(self.index)
            } else if self.column > self.target_column {
                ColumnSearchStatus::Overshot(self.index, self.column - self.target_column)
            } else {
                ColumnSearchStatus::Continue
            }
        }
    }
}


impl Grid<Offset> for FileMap {
    fn line_at(&self, ofs: Offset) -> Result<Line, LookupError> {
        if ! self.span.contains(ofs) {
            Err(LookupError::InvalidOffset)
        } else {
            let idx = self.offset_to_index(ofs);
            match self.line_indices.binary_search(&idx) {
                // Err(0) => anywhere in first line (first line does not have
                // an entry because it _always_ starts at index 0)
                Err(0) => Ok(Line::from_index(0)),

                // Ok(n) => offset is at the beginning of the line
                Ok(n) => Ok(Line::from_index(n + 1)),

                // Err(n) => offset is somewhere in middle of the line
                // (Remember that `binary_search` already adds 1 to the index!)
                Err(n) => Ok(Line::from_index(n)),
            }
        }
    }

    fn column_at(&self, ofs: Offset) -> Result<Column, LookupError> {
        self.line_start_offset(ofs)
            .and_then(|st| self.column_width(span(st, ofs)))
            .map(|n| Column::from_index(n as usize))
    }

    fn position_at(&self, loc: Loc) -> Result<Offset, LookupError> {
        use self::ColumnSearchStatus::*;

        if self.line_indices.len() < loc.line().index() {
            // Check for an invalid line (trivially done) and do an early
            // return if the line is out of bounds.
            Err(LookupError::InvalidLocation)
        } else {

            // determine the buffer index for the character at the start of the line
            let index = TryConvert::<_, Index>::try_convert(self, loc.line())?;
            let mut cs = ColumnSearch{index, column: Column::from_index(0),
                                      target_column: loc.column()};
            loop {
                match cs.next(&self) {
                    Ok(TargetReached(idx)) |
                    // FIXME: [bug?] we can't help it if we overshot the target
                    // column because of
                    Ok(Overshot(idx, _))
                        => break Ok(self.index_to_offset(idx)),
                    Ok(Continue) => {},
                    Err(e) => break Err(e)
                }
            }
        }
    }
}


// ----------------------------------------------------------------
// SourceMap

/// A collection of source code addressable by `Span`s.
#[derive(Clone, Debug, Hash, Default)]
pub struct SourceMap {
    files: Vec<FileMap>
}

impl SourceMap {
    pub fn new() -> Self {
        Default::default()
    }

    /// Fetch a Reader for
    pub fn read_from_file<'a, P: Display + AsRef<Path>>(&'a mut self, path: P) -> std::io::Result<io::Reader<'a, impl Read>> {
        let path = path.as_ref();
        let md = fs::metadata(path)?;
        let fm = FileMap{name: format!("{}", path.display()),
                         source: Some(String::new()),
                         line_indices: vec![],
                         non_monospaced_sequences: vec![],
                         span: self.new_entry_span(md.len() as usize)};
        self.files.push(fm);
        let mut fm = self.files.last_mut().unwrap();
        fs::File::open(path).map(move |f| fm.read_from(f))
    }

    pub fn read_from_buffer<'a, B: ?Sized + 'a + AsRef<str>>(&'a mut self, name: &str, buf: &'a B) -> io::Reader<'a, impl Read + 'a> {
        let fm = FileMap{name: name.to_string(),
                         source: Some(buf.as_ref().to_string()),
                         line_indices: vec![],
                         non_monospaced_sequences: vec![],
                         span: self.new_entry_span(buf.as_ref().len())};

        self.files.push(fm);
        let mut fm = self.files.last_mut().unwrap();
        fm.read_from(std::io::Cursor::new(buf.as_ref()))
    }

    /// Determine the offset span for a new entry in the source map.
    fn new_entry_span(&self, len: usize) -> Span<Offset> {
        self.files.last().map_or_else(|| span(Offset(0), Offset(len as u32)),
                                      |f| span(f.span.end, f.span.end + Index(len as u32)))
    }

    /// Determine the index of the FileMap in `self.files` that contains the
    /// given offset.
    fn file_map_index(&self, ofs: Offset) -> Result<usize, LookupError> {
        match self.files.binary_search_by_key(&ofs, |f| f.span.start) {
            Ok(n)
                => Ok(n),
            Err(n) if n > 0 && unsafe { self.files.get_unchecked(n - 1) }.span.contains(ofs)
                =>  Ok(n - 1),
            _ => Err(LookupError::InvalidOffset)
        }
    }
}

impl Mapper<Offset> for SourceMap {
    fn fetch_snippet(&self, sp: Span<Offset>) -> Result<&str, LookupError> {
        self.file_map_index(sp.start)
            .map(|i| unsafe { self.files.get_unchecked(i) })
            .and_then(|fm| fm.fetch_snippet(sp))
    }

    fn fetch_line_span(&self, ofs: Offset) -> Result<Span<Offset>, LookupError> {
        self.file_map_index(ofs)
            .map(|i| unsafe { self.files.get_unchecked(i) })
            .and_then(|fm| fm.fetch_line_span(ofs))
    }

    fn fetch_lines_span(&self, sp: Span<Offset>) -> Result<Span<Offset>, LookupError> {
        self.file_map_index(sp.start)
            .map(|i| unsafe { self.files.get_unchecked(i) })
            .and_then(|fm| fm.fetch_lines_span(sp))
    }
}

// ----------------------------------------------------------------
// Tests

#[cfg(test)]
mod tests {
    use super::{span, FileMap, LookupError, Index, Offset, Loc, Line, Column};
    use super::{Grid, Mapper};


    macro_rules! loc { ($l: expr, $c: expr) => { Loc::at(Line::from_number($l), Column::from_number($c)) }; }
    macro_rules! line_number { ($l: expr) => { Line::from_number($l) }; }

    const ALPHABET_LINES: &'static str = concat!("abcd\n",
                                                 "efgh\n",
                                                 "hijk\n",
                                                 "lmno\n",
                                                 "pqrs\n",
                                                 "tuvw\n",
                                                 "xyz\n");
    #[test]
    fn test_file_map_from_source() {
        let fm = FileMap::from_source("", ALPHABET_LINES);

        assert_eq!(34, ALPHABET_LINES.len());
        assert_eq!(34, fm.span.len());
        assert_eq!(34, fm.source.as_ref().unwrap().len());

        assert_eq!(vec![Index(5), Index(10), Index(15), Index(20),
                        Index(25), Index(30)],
                   fm.line_indices);
    }

    #[test]
    fn test_file_map_snippet() {
        let fm = FileMap::from_source("", "xyzabc");

        assert_eq!(Ok("xyzabc"), fm.fetch_snippet(fm.span));

        assert_eq!(Err(LookupError::InvalidOffset),
                   fm.fetch_snippet(span(Offset(6), Offset(8))));

        assert_eq!(Err(LookupError::FileBoundaryViolation),
                   fm.fetch_snippet(span(Offset(3), Offset(8))));

        assert_eq!(Err(LookupError::SourceUnavailable),
                   FileMap{name: String::new(), source: None,
                           line_indices: vec![], non_monospaced_sequences: vec![],
                           span: span(Offset(0), Offset(100))}
                   .fetch_snippet(span(Offset(0), Offset(2))));
    }

    #[test]
    fn test_file_map_lines() {
        let fm = FileMap::from_source("", ALPHABET_LINES);
        macro_rules! check_line {
            ($fm: expr, $n: expr, $s: expr, $e: expr, $l: expr) => {
                assert_eq!($s, $fm.line_start_offset(Offset($s)).unwrap().0);
                assert_eq!($s, $fm.line_start_offset(Offset(($s + $e)/2)).unwrap().0);
                assert_eq!($s, $fm.line_start_offset(Offset($e - 1)).unwrap().0);

                assert_eq!($e, $fm.line_end_offset(Offset($s)).unwrap().0);
                assert_eq!($e, $fm.line_end_offset(Offset(($s + $e)/2)).unwrap().0);
                assert_eq!($e, $fm.line_end_offset(Offset($e - 1)).unwrap().0);

                assert_eq!($l, $fm.fetch_line(Offset($s)).unwrap());
                assert_eq!($l, $fm.fetch_line(Offset(($s + $e)/2)).unwrap());
                assert_eq!($l, $fm.fetch_line(Offset($e - 1)).unwrap());

                for i in $s..$e {
                    let cl = $l.chars().nth(i as usize - $s).unwrap();
                    let ca = ALPHABET_LINES.chars().nth(i as usize).unwrap();
                    assert_eq!(cl, ca);

                    assert_eq!(Ok(line_number!($n)), fm.line_at(Offset(i)),
                               "wrong line number for offset {} (char {:?})",
                               i, ca);
                }

            }
        }
        check_line!(fm, 1,  0,  5, "abcd\n");
        check_line!(fm, 2,  5, 10, "efgh\n");
        check_line!(fm, 3, 10, 15, "hijk\n");
        check_line!(fm, 4, 15, 20, "lmno\n");
        check_line!(fm, 5, 20, 25, "pqrs\n");
        check_line!(fm, 6, 25, 30, "tuvw\n");
        check_line!(fm, 7, 30, 34, "xyz\n");
    }

    #[test]
    fn test_file_map_columns() {
        let fm = FileMap::from_source("", ALPHABET_LINES);
        assert_eq!(Ok(4), fm.column_width(fm.fetch_line_span(Offset(2)).unwrap()));

        let fm = FileMap::from_source("", "☠\n");
        assert_eq!(Err(LookupError::CodepointBoundaryViolation),
                   fm.column_width(span(Offset(1), Offset(2))));
        assert_eq!(Ok(0), fm.column_width(span(Offset(1), Offset(2))));
        assert_eq!(Ok(1), fm.column_width(span(Offset(0), Offset(1))));
    }

    #[test]
    fn test_file_map_grid_impl() {
        let fm = FileMap::from_source("", ALPHABET_LINES);

        // When fetching the line number for a particular location, offsets and
        // indices should be treated as referring to the "gaps" between
        // characters; this means that e.g. Index(0) points to the start of the
        // first line, while (in `ALPHABET_LINES`) Index(5) points at the
        // location immediately after the first newline and immediately prior
        // to the first character on the next line.
        assert_eq!(Ok(line_number!(1)), fm.line_at(Offset(4)));
        assert_eq!(Ok(line_number!(2)), fm.line_at(Offset(5)));

        assert_eq!(Ok(Offset(2)), fm.position_at(loc!(1, 3)));
        assert_eq!(Ok(loc!(1, 3)), fm.loc_at(Offset(2)));

        assert_eq!(b'w', ALPHABET_LINES.as_bytes()[28]);
        assert_eq!(Ok(line_number!(6)), fm.line_at(Offset(25)));
        assert_eq!(Ok(line_number!(6)), fm.line_at(Offset(27)));
        assert_eq!(Ok(line_number!(6)), fm.line_at(Offset(28)));
        assert_eq!(Ok(line_number!(7)), fm.line_at(Offset(30)));
        assert_eq!(Ok(loc!(7, 1)), fm.loc_at(Offset(30)));

        assert_eq!(Ok(line_number!(7)), fm.line_at(Offset(33)));
        assert_eq!(Err(LookupError::InvalidOffset), fm.line_at(Offset(36)));

        assert_eq!(Err(LookupError::InvalidLocation), fm.position_at(loc!(10, 32)));
        assert_eq!(Err(LookupError::InvalidLocation), fm.position_at(loc!(8, 1)));
    }
}
