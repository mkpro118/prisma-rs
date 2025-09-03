//! Scan schema text into a deterministic stream of tokens.
//!
//! The scanner (lexer) is the first stage of the compiler pipeline.
//! It converts raw Prisma schema text into `Token` values with
//! precise spans. Tokens include identifiers, keywords, literals,
//! punctuation, list and optional markers, and comments.
//!
//! This module provides a small, extensible lexer (`lexer`) with pluggable
//! input sources and token recognizers, and token types and spans (`tokens`)
//! used across parsing and diagnostics. Common items are re-exported so
//! callers can import from
//! `prisma_rs::core::scanner::{Lexer, Token, TokenType, ...}`.
//!
//! All spans use 1-based line and column. The scanner skips Unicode
//! whitespace between tokens, coalesces consecutive single-line comments
//! and doc comments, and emits a single `EOF` token after input is
//! consumed. Scanning runs in linear time over input. String and number
//! literals retain their original source text without normalization.
//!
//! Library users typically create a `Lexer` and iterate tokens. Plugin
//! authors can provide a custom `CharacterStream` or additional recognizers.
//!
//! ## Examples
//! ```
//! # use prisma_rs::core::scanner::{Lexer, TokenType};
//! let tokens: Result<Vec<_>, _> = Lexer::tokenize("model User {}").collect();
//! let tokens = tokens.expect("scan ok");
//! assert!(matches!(*tokens.last().unwrap().r#type(), TokenType::EOF));
//! ```
pub mod lexer;
pub mod tokens;

// Re-export common scanner API so users can write
// `use prisma_rs::core::scanner::{Lexer, Token, TokenType, ...};`
pub use lexer::*;
pub use tokens::*;
