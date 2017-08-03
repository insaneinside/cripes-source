// Copyright (C) 2017 cripes-source Project Contributors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-Apache
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>,
// at your option. This file may not be copied, modified, or
// distributed except according to those terms.
//! Utilities for producing and rendering diagnostic messages.

use std::borrow::Cow;
type Span = ::pos::Span<::pos::Offset>;

// ----------------------------------------------------------------
// Diagnostic

/// Structured representation of a diagnostic message.
pub struct Diagnostic {
    /// Span to which the message refers.
    span: Span,

    /// Main message to be displayed.
    message: String,

    /// Labeled spans
    labels: Vec<(Span, String)>,
}

impl Diagnostic {
    /// Create a new `Diagnostic` for the given message and span.
    pub fn new(span: Span, message: String) -> Self {
        Diagnostic{span, message, labels: vec![]}
    }

    pub fn new_with_label(span: Span, message: String, label: String) -> Self {
        Diagnostic{span, message, labels: vec![(span, label)]}
    }

    /// Label a particular span of source with the given string.
    pub fn label_span(&mut self, sp: Span, label: String) {
        self.labels.push((sp, label));
    }
}

// ----------------------------------------------------------------
// Snippet

/// Annotated source code extract.
pub struct Snippet {
    /// Annotations to be added to the snippet.
    annotations: Vec<Annotation>
}

impl Snippet {
    /// Add an annotation to the snippet.
    pub fn add_annotation(&mut self, ann: Annotation) {
        self.annotations.push(ann)
    }
}

// ----------------------------------------------------------------
// Mark

enum Mark {
    /// "Invisible" mark, used in `Annotation` to ensure that a span is visible
    /// within the snippet.  Does _not_ add any visual indicators to the
    /// output, and does not accept a label.
    Show,

    /// Low-priority visual marking.
    Mark(Option<LabelStr>),
    
    /// High-priority visual marking, used to call attention to the marked span
    /// using a distinctive visual style.
    Highlight(Option<LabelStr>)
}

// ----------------------------------------------------------------
// Annotation

type LabelStr = Cow<'static, str>;

/// Annotation added to some source code.
pub struct Annotation {
    span: Span,
    mark: Mark,
}


impl Annotation {
    /// Ensure that the given span is visible within the snippet.  Use this to
    /// prevent contextual information from being elided.
    pub fn show(span: Span) -> Self {
        Annotation{span, mark: Mark::Show}
    }

    /// Highlight a span, with an optional label.
    pub fn highlight(span: Span, label: Option<LabelStr>) -> Self {
        Annotation{span, mark: Mark::Highlight(label)}
    }

    /// Mark a span, with an optional label.
    pub fn mark(span: Span, label: Option<LabelStr>) -> Self {
        Annotation{span, mark: Mark::Mark(label)}
    }
}


#[cfg(test)]
mod tests {
    
}
