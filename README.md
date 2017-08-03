# Source Tracking & Diagnostics Utilities in Rust

[![Build Status](https://travis-ci.org/insaneinside/cripes-source.svg?branch=master)](https://travis-ci.org/insaneinside/cripes-source)

This crate provides — or *will* provide — a set of types, traits, and routines
useful for tracking the provenance of AST items and other intermediate values
produced by a parser.  Its basic operation takes inspiration from the relevant
subsystems used in rustc itself, while its API is driven by the author's
penchant for elegant trait-directed designs.

cripes-source is part of the "Common (Rust) Infrastructure for Parsing and
Expressions" project.

## Roadmap/Status

Project is in its early stages; the API has not even been fully designed (and
the API that exists is certainly subject to change!).  Requires **nightly**
Rust for now.

* [ ] Source tracking and lookup
  - [x] Basic types for representing file locations
  - [x] Source storage + retrieval by offset and span
  - [ ] Line and column ↔offset conversion using per-file indexes (nearly
        completed)
  - [ ] Incremental indexing (insufficiently tested)
  - [ ] Support for obtaining span information while parsing (API work needed)
* [ ] Diagnostics: have some ideas sketched out...
  - [ ] Types for storing diagnostics to be rendered
  - [ ] Traits to be implemented by different renderers
  - [ ] The renderers themselves
* [ ] Polish pass
  - [ ] Document *all* the things
  - [ ] Integration tests!
  - [ ] Add prelude module?
  - [ ] Add benchmarks?
  - [ ] Increase test coverage (whatever it is, it's not high enough!)

## License

cripes-source is dual-licensed under both
the [Apache License version 2.0](LICENSE-Apache) and
the [MIT License](LICENSE-MIT); derivative works may be made under the terms of
either license.

