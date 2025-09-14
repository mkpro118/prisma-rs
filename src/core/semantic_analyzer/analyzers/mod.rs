//! Concrete analyzer implementations for semantic analysis phases.
//!
//! This module contains the implementation of all semantic analysis phases
//! that work together to validate Prisma schemas. Each analyzer implements
//! the `PhaseAnalyzer` trait and focuses on a specific aspect of validation.

pub mod symbol_collector;

// Re-export implemented analyzers for convenience
pub use symbol_collector::SymbolCollectionAnalyzer;
