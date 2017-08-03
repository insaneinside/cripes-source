// Copyright (C) 2017 cripes-source Project Contributors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-Apache
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>,
// at your option. This file may not be copied, modified, or
// distributed except according to those terms.
//! Position-related primitives.
//!
//! This module provides several opaque position types.
//!
//! ## Linear positions
//!
//! Linear position types are used to identify positions within some source:
//!
//!   * [`Offset`] instances represent _absolute_ positions within
//!     a [`SourceMap`].
//!   * [`Index`] instances represent positions relative to some particular
//!     [`FileMap`].  Unlike `Offset`, an `Index` can be converted to `usize`
//!     via its `Into` implementation.
//!
//! [`Offset`]: struct.Offset.html
//! [`Index`]: struct.Index.html
//! [`SourceMap`]: ../storage/struct.SourceMap.html
//! [`FileMap`]: ../storage/struct.FileMap.html
//!
//! ## Grid positions
//!
//! Grid position types provide human-friendly representations of positions
//! _within_ a file.
//!
//!   * [`Line`] instances represent line numbers.
//!   * [`Column`] instances represent column numbers.
//!
//! [`Line`]: struct.Line.html
//! [`Column`]: struct.Column.html
//!
//! ## Regions
//! 
//! [`Span`] is used to represent ranges between two linear positions; aside
//! from trait bounds it is semantically equivalent to the standard library's
//! `Range` type.
//!
//! [`Span`]: struct.Span.html

use std::u16;
use std::cmp::{min, max};
use core::ops::{Add, AddAssign, Sub, SubAssign, Range, Deref};

// ----------------------------------------------------------------
// Helper traits
//
// We use these to allow argument overloading by implementing the traits with
// different concrete type parameters.

pub trait Contains<T> {
    fn contains(&self, other: T) -> bool;
}

// ----------------------------------------------------------------

/// Provides method `relative_to`, used to convert absolute positions to
/// relative positions.
pub trait RelativeTo<T> {
    type Output;

    /// Create a version of `self` with values measured "relative to"
    /// the argument.
    fn relative_to(self, reference: T) -> Self::Output;
}

// ----------------------------------------------------------------
// Line, Column

/// A line number.
///
/// `Line` is used to avoid any ambiguity between zero- and one-based line
/// numbers; use the [`number`](#tymethod.number) method to fetch a one-based
/// numeric value, and [`index`](#tymethod.index) to fetch a zero-based
/// numeric value.
#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct Line(u16);
impl Line {
    /// Create a `Line` for the given line number.
    pub fn from_number(n: usize) -> Self {
        assert!(n > 0, "Line numbers start from one");
        assert!(n <= u16::MAX as usize, "Line number exceeds storage range");
        Line((n - 1) as u16)
    }

    /// Create a `Line` for the given index.
    pub fn from_index(i: usize) -> Self {
        assert!(i <= u16::MAX as usize, "Line index exceeds storage range");
        Line(i as u16)
    }

    /// Fetch the line number as a one-based value
    pub fn number(self) -> usize {
        self.0 as usize + 1
    }

    /// Fetch the line number as a zero-based value
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A column number.
///
/// `Column` is used to avoid any ambiguity between zero- and one-based column
/// numbers; use the [`number`](#tymethod.number) method to fetch a one-based
/// numeric value, and [`index`](#tymethod.index) to fetch a zero-based
/// numeric value.
#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct Column(u16);
impl Column {
    /// Create a `Column` for the given column number.
    pub fn from_number(n: usize) -> Self {
        assert!(n > 0, "Column numbers start from one");
        assert!(n <= u16::MAX as usize, "Column number exceeds storage range");
        Column((n - 1) as u16)
    }

    /// Create a `Column` for the given index.
    pub fn from_index(i: usize) -> Self {
        assert!(i <= u16::MAX as usize, "Column index exceeds storage range");
        Column(i as u16)
    }

    /// Fetch the column number as a one-based value
    pub fn number(self) -> usize {
        self.0 as usize + 1
    }

    /// Fetch the column number as a zero-based value
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl Add<u16> for Column {
    type Output = Self;

    fn add(self, u: u16) -> Self::Output {
        Column(self.0 + u)
    }
}
impl AddAssign<u16> for Column {
    fn add_assign(&mut self, u: u16) {
        self.0 += u;
    }
}


impl Sub<Column> for Column {
    type Output = u16;

    fn sub(self, idx: Column) -> Self::Output {
        (self.0 - idx.0) as u16
    }
}




/// Combined line/column numbers.
#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct Loc {
    line: Line,
    column: Column,
}

impl Loc {
    pub fn at(line: Line, column: Column) -> Self {
        Loc{line, column}
    }

    /// Fetch the location's line.
    pub fn line(self) -> Line { self.line }
    /// Fetch the location's column.
    pub fn column(self) -> Column { self.column }
}

// ----------------------------------------------------------------
macro_rules! impl_add_sub_primitive_for_type {
    ($T: tt;) => {};
    ($T: tt; $U: ty $(, $rest: ty)*) => {
        impl Add<$U> for $T {
            type Output = $T;
            fn add(self, u: $U) -> Self::Output {
                $T(self.0 + u as u32)
            }
        }
        impl AddAssign<$U> for $T {
            fn add_assign(&mut self, u: $U) {
                self.0 += u as u32;
            }
        }
        impl Sub<$U> for $T {
            type Output = $T;
            fn sub(self, u: $U) -> Self::Output {
                $T(self.0 - u as u32)
            }
        }
        impl SubAssign<$U> for $T {
            fn sub_assign(&mut self, u: $U) {
                self.0 -= u as u32;
            }
        }
        impl_add_sub_primitive_for_type!($T; $($rest),*);
    };
}

// ----------------------------------------------------------------
// Offset

/// Absolute offset within the source map.
///
/// Offsets have no meaning as buffer indices, because they represent offsets
/// in a space made up of multiple allocations.
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct Offset(pub(crate) u32);

impl_add_sub_primitive_for_type!(Offset; u8, u16, u32);

/// The difference between two `Offset`s is a relative index.
impl Sub for Offset {
    type Output = Index;
    fn sub(self, rhs: Offset) -> Self::Output {
        Index(self.0 - rhs.0)
    }
}

/// Adding a relative index to an absolute offset results in an
/// absolute offset.
impl Add<Index> for Offset {
    type Output = Offset;

    fn add(self, idx: Index) -> Self::Output {
        Offset(self.0 + idx.0)
    }
}

impl RelativeTo<Offset> for Offset {
    type Output = Index;

    fn relative_to(self, ofs: Offset) -> Self::Output {
        self - ofs
    }
}

// ----------------------------------------------------------------
// Index

/// Relative offset.
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct Index(pub(crate) u32);

impl Sub<Index> for Index {
    type Output = u32;

    fn sub(self, idx: Index) -> Self::Output {
        self.0 - idx.0
    }
}

impl_add_sub_primitive_for_type!(Index; u8, u16, u32);

/// Adding a relative index to an absolute offset results in an
/// absolute offset.
impl Add<Offset> for Index {
    type Output = Offset;

    fn add(self, ofs: Offset) -> Self::Output {
        Offset(self.0 + ofs.0)
    }
}

impl Into<usize> for Index {
    fn into(self) -> usize {
        self.0 as usize
    }
}

// ----------------------------------------------------------------
// Span

/// A continuous region.  Spans represent half-open, fully-bounded ranges
/// within discretely-indexed spaces.
///
/// Spans have the same general semantics as Rust's own
/// [`Range`](std::ops::Range) (with the exception that they are [`Copy`]).
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct Span<T> {
    /// Lower bound (inclusive) of region covered by this span.
    pub(crate) start: T,
    /// Upper bound (exclusive) of region covered by this span.
    pub(crate) end: T,
}


/// Create a `Span` with the given endpoints.
pub fn span<T>(start: T, end: T) -> Span<T>
    where T: Copy + Ord
{
    Span{start: min(start, end), end: max(start, end)}
}

impl<T> Span<T> where T: Copy + PartialOrd {
    /// Check if the span overlaps with another.
    ///
    /// "Overlaps" is interpreted to mean that one of the spans contains _at
    /// least_ one of the other's (inclusive) end points, i.e. the two spans
    /// have a non-null intersection.
    pub fn intersects(&self, sp: Self) -> bool {
        sp.contains(self.start) || self.contains(sp.start) ||
            (self.end > sp.start && self.start < sp.end) ||
            (sp.end > self.start && sp.start < self.end)
    }

    /// Create a "merged" span that covers the regions included in both this
    /// *and* another span, and any space between the two.
    pub fn merge(&self, sp: Self) -> Self where T: Ord {
        span(min(self.start, sp.start), max(self.end, sp.end))
    }

    /// Determine the size of the region covered by the span.
    pub fn len(&self) -> usize
        where T: Sub,
              <T as Sub>::Output: Into<usize>
    {
        Into::<usize>::into(self.end - self.start)
    }
}

impl<T> Contains<Span<T>> for Span<T>
    where T: Copy + PartialOrd {
    /// Determine if a span completely contains another.
    fn contains(&self, sp: Self) -> bool {
        sp.start >= self.start && sp.end <= self.end
    }
}

impl<T> Contains<T> for Span<T>
    where T: Copy + PartialOrd {
    /// Check whether the given position is contained within this span.
    fn contains(&self, ofs: T) -> bool {
        ofs >= self.start && ofs < self.end
    }
}

impl<T, U> RelativeTo<U> for Span<T>
    where T: Copy + RelativeTo<U>,
          U: Copy
{
    type Output = Span<T::Output>;

    fn relative_to(self, to: U) -> Self::Output {
        Span{start: self.start.relative_to(to),
             end: self.end.relative_to(to)}
    }
}

impl<T, U> Sub<U> for Span<T>
    where T: Copy + Sub<U>,
          U: Copy
{
    type Output = Span<<T as Sub<U>>::Output>;

    fn sub(self, rhs: U) -> Self::Output {
        Span{start: self.start - rhs, end: self.end - rhs}
    }
}

impl<T, U> Into<Range<U>> for Span<T>
    where T: Into<U> {
    fn into(self) -> Range<U> {
        Range{start: self.start.into(),
              end: self.end.into()}
    }
}

// ----------------------------------------------------------------
// Spanned
pub struct Spanned<T, U> {
    node: T,
    span: Span<U>
}

impl<T, U: Copy> Spanned<T, U> {
    pub fn span(&self) -> Span<U> {
        self.span
    }
}

impl<T, U> Deref for Spanned<T, U> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.node
    }
}


// ----------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::{span, Contains};
    #[test]
    fn test_span() {
        // a span's length includes _both_ endpoints
        assert_eq!(10, span(0u8, 10).len());

        // a span "contains" another span that it fully encloses
        assert!(span(1, 10).contains(span(2, 9)));
        assert!(! span(1, 10).contains(span(2, 11)));

        // a span contains itself
        assert!(span(1, 2).contains(span(1, 2)));
        // a span contains other spans that rest on its borders
        assert!(span(1, 4).contains(span(1, 2)));
        assert!(span(1, 4).contains(span(3, 4)));

        // a span contains all points within its boundaries.
        assert!(span(1, 3).contains(1));
        assert!(span(1, 3).contains(2));
        assert!(! span(1, 3).contains(3));

        // smaller spans do not contain larger ones
        assert!(! span(2, 9).contains(span(1, 10)));

        // disjoint spans neither intersect nor contain each other
        // (note the 
        assert!(! span(3, 5).contains(span(5, 6)));
        assert!(! span(5, 6).contains(span(3, 5)));
        assert!(! span(3, 5).intersects(span(5, 6)));
        assert!(! span(5, 6).intersects(span(3, 5)));

        // end of a span does not "overlap" anything
        assert!(! span(3, 4).intersects(span(4, 5)));

        // spans that only overlap do not contain each other...
        assert!(span(3, 5).intersects(span(4, 6)));
        assert!(span(4, 6).intersects(span(3, 5)));
        assert!(! span(3, 5).contains(span(4, 6)));
        assert!(! span(4, 6).contains(span(3, 5)));

        // ...but if one span contains another, they both overlap
        assert!(span(1, 5).contains(span(2, 3)));
        assert!(span(1, 5).intersects(span(2, 3)));
        assert!(span(2, 3).intersects(span(1, 5)));
    }
}
