//! Scanner-Parser Integration Tests
//!
//! End-to-end tests for the complete parsing pipeline from raw strings
//! through lexical analysis to final AST generation with diagnostics.
//!
//! ## Test Categories
//!
//! ### Fast Tests (default)
//! - `cargo test --test scanner_parser_integration`
//! - Basic functionality, happy path, and error recovery tests
//! - Should complete in under 30 seconds
//!
//! ### Slow Tests (ignored by default)
//! - `cargo test --test scanner_parser_integration -- --ignored`
//! - Performance benchmarking, concurrent parsing, and exhaustive diagnostic tests
//! - May take several minutes to complete
//!
//! ### All Tests (fast + slow)
//! - `cargo test --test scanner_parser_integration -- --include-ignored`
//! - Complete validation suite

#[path = "scanner_parser/mod.rs"]
mod scanner_parser;

// Happy path integration tests
#[path = "scanner_parser/happy_path/minimal_schemas.rs"]
mod minimal_schemas;

#[path = "scanner_parser/happy_path/fixture_based_tests.rs"]
mod fixture_based_tests;

// Performance and benchmarking tests
#[path = "scanner_parser/performance/benchmarking_tests.rs"]
mod benchmarking_tests;

// Error recovery and diagnostic quality tests
#[path = "scanner_parser/error_recovery/diagnostic_quality_tests.rs"]
mod diagnostic_quality_tests;

// Concurrent parsing determinism tests
#[path = "scanner_parser/concurrent/deterministic_tests.rs"]
mod deterministic_tests;

// Parser configuration and options tests
#[path = "scanner_parser/configuration/options_tests.rs"]
mod options_tests;

// Additional test modules will be added here as they are implemented
// mod comprehensive_schemas;
// mod real_world_examples;
// mod declaration_coverage;

// Edge cases tests
// mod unicode_handling;
// mod boundary_conditions;
// mod comment_integration;

// Regression tests
// mod grammar_compliance;
// mod compatibility;
