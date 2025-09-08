#![deny(clippy::expect_used)] // using deny so that test code can use it
#![deny(clippy::style)]
#![deny(clippy::unwrap_used)] // using deny so that test code can use it
#![deny(unsafe_code)]
#![forbid(clippy::allow_attributes)]
#![forbid(clippy::complexity)]
#![forbid(clippy::correctness)]
#![forbid(clippy::pedantic)]
#![forbid(clippy::perf)]
#![forbid(clippy::suspicious)]
#![forbid(future_incompatible)]

pub mod core;

// Re-export proc macros for AST derivation
pub use compiler_macros::{AstContainerNode, AstLeafNode};
