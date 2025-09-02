//! Concrete analyzer implementations for semantic analysis phases.
//!
//! This module contains the implementation of all semantic analysis phases
//! that work together to validate Prisma schemas. Each analyzer implements
//! the `PhaseAnalyzer` trait and focuses on a specific aspect of validation.

pub mod symbol_collector;

// Additional analyzers will be implemented in subsequent commits
// pub mod type_resolution;
// pub mod relationship;
// pub mod attribute_validation;
// pub mod business_rules;

// Re-export implemented analyzers for convenience
pub use symbol_collector::SymbolCollectionAnalyzer;

// Additional re-exports will be added as analyzers are implemented
// pub use type_resolution::TypeResolutionAnalyzer;
// pub use relationship::RelationshipAnalyzer;
// pub use attribute_validation::AttributeValidationAnalyzer;
// pub use business_rules::BusinessRuleAnalyzer;
