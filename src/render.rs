// Copyright (C) 2017 cripes-source Project Contributors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-Apache
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>,
// at your option. This file may not be copied, modified, or
// distributed except according to those terms.
//! Traits and utilities for rendering diagnostics for output.

use storage::SourceMap;

pub trait Render<Target> {
    type Error;

    fn render(&self, sm: &SourceMap, tgt: Target) -> Result<(), Self::Error>;
}

pub trait RenderTarget {
    type Value;
    type Position;
    type Size;
    type Error;

    /// Write a value at the given position.
    ///
    /// On success, returns the size occupied by the written value.
    fn write_at(&mut self, position: Self::Position, val: Self::Value) -> Result<Self::Size, Self::Error>;
}


// ----------------------------------------------------------------

pub struct GridBuf {
    grid: Vec<Vec<char>>,
}

impl GridBuf {
    pub fn new() -> Self {
        GridBuf{grid: vec![]}
    }
}

impl RenderTarget for GridBuf {
    type Value = char;
    type Position = GridPos;
    type Size = GridPos;
    type Error = 

    pub fn write_at(&mut self, position: Self::Position, value: Self::Value) {
        for _ in self.grid.len()..y {
            self.grid.push(vec![]);
        }
        
    }
}

// ================================================================

enum Axis {
    Horizontal,
    Vertical
}

trait Layout {
    /// Primary direction 
    const AXIS: Axis;
}

// ----------------------------------------------------------------

type GridCoord = u16;
type GridPos = [GridCoord; 2];
type GridOptPos = [Option<GridCoord>; 2];

/// An "element" to be rendered.
pub struct Element<T> {
    content: T,
    size: Option<GridPos>,
    position: GridOptPos,
}

pub struct Group<E>(Vec<E>);
impl<E> Layout for Group<E> {
    const AXIS: Axis = Axis::Vertical;
}

// ----------------------------------------------------------------

/// Grid-based render stage.
pub struct Renderer<E> {
    elements: Vec<E>,
    max_width: u16,
}

impl<E> Renderer<E> {
    fn push(&mut self, elt: E) {
        self.elements.push(elt);
    }
}

impl<E, T> Render<T> for Renderer<E>
    where T: RenderTarget,
          E: Render<T> {
    fn render(&mut self) -> String {
        unimplemented!()
    }
}
