//! Parser module for converting token streams into Abstract Syntax Trees.
//!
//! This module contains the complete parser implementation including AST definitions,
//! parser logic, and supporting utilities.

pub mod ast;
pub mod components;
pub mod config;
pub mod context;
pub mod grammar;
pub mod progress;
pub mod stream;
pub mod traits;

// Re-export supervision utilities for consumers and tests
pub use progress::{
    DefaultProgressObserver, ObservedTokenStream, ProgressConfig,
    ProgressObserver, ProgressTuning,
};

// Re-export main types for convenience
pub use config::{Diagnostic, DiagnosticSeverity, ParseResult, ParserOptions};
pub use context::DefaultParserContext;
pub use stream::{TokenStreamExt, VectorTokenStream};
pub use traits::{Parser, SchemaParser, TokenStream};
