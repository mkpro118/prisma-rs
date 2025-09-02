//! Semantic analyzer for Prisma schema validation and symbol resolution.
//!
//! The semantic analyzer operates on the AST produced by the parser and performs
//! multi-phase analysis to validate schema semantics, resolve types, analyze
//! relationships, and enforce business rules. The architecture is fully pluggable
//! and trait-based, allowing custom analyzers and validation rules.
//!
//! ## Architecture Overview
//!
//! The semantic analyzer follows a multi-phase approach:
//! 1. **Symbol Collection** - Build symbol tables and establish scopes
//! 2. **Type Resolution** - Resolve all type references and validate compatibility
//! 3. **Relationship Analysis** - Analyze model relationships and constraints
//! 4. **Attribute Validation** - Validate attributes and their arguments
//! 5. **Business Rule Validation** - Enforce Prisma-specific rules and best practices
//!
//! Each phase is implemented as a pluggable analyzer that implements the
//! `PhaseAnalyzer` trait. The `SemanticAnalyzer` orchestrator manages the
//! execution of all phases in dependency order.
//!
//! ## Examples
//!
//! Basic semantic analysis:
//! ```rust,ignore
//! use prisma_rs::core::semantic_analyzer::{SemanticAnalyzer, AnalyzerOptions};
//!
//! let schema = parser.parse_schema(&input)?;
//! let mut analyzer = SemanticAnalyzer::new();
//! let analysis_result = analyzer.analyze(&schema, &AnalyzerOptions::default())?;
//!
//! for diagnostic in &analysis_result.diagnostics {
//!     println!("{}: {}", diagnostic.severity, diagnostic.message);
//! }
//! ```

pub mod analyzer;
pub mod analyzers;
pub mod context;
pub mod diagnostics;
pub mod symbol_table;
pub mod traits;
pub mod type_resolver;

// Re-export main types for convenience
pub use analyzer::SemanticAnalyzer;
pub use context::{AnalysisContext, AnalysisResult};
pub use diagnostics::{DiagnosticCode, FixHint, SemanticDiagnostic};
pub use symbol_table::{Symbol, SymbolTable, SymbolType};
pub use traits::{
    AttributeAnalyzer, DeclarationAnalyzer, PhaseAnalyzer, RelationshipAnalyzer,
};
pub use type_resolver::{ResolvedType, ScalarType, TypeResolver};

/// Configuration options for semantic analysis.
/// Validation mode configuration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValidationMode {
    /// Lenient validation - allows warnings and continues
    Lenient,
    /// Strict validation - stops on first error
    Strict,
}

/// Feature validation configuration
#[derive(Debug, Clone)]
pub struct FeatureOptions {
    /// Validate experimental features
    pub validate_experimental: bool,
    /// Enable performance warnings
    pub performance_warnings: bool,
    /// Enable parallel analysis where possible
    pub enable_parallelism: bool,
}

#[derive(Debug, Clone)]
pub struct AnalyzerOptions {
    /// Validation mode
    pub validation_mode: ValidationMode,

    /// Feature validation options
    pub features: FeatureOptions,

    /// Maximum analysis time per phase
    pub phase_timeout: std::time::Duration,

    /// Target database provider for validation
    pub target_provider: Option<DatabaseProvider>,

    /// Maximum number of diagnostics to collect before stopping
    pub max_diagnostics: usize,
}

/// Supported database providers for provider-specific validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DatabaseProvider {
    PostgreSQL,
    MySQL,
    SQLite,
    SQLServer,
    MongoDB,
}

impl Default for AnalyzerOptions {
    fn default() -> Self {
        Self {
            validation_mode: ValidationMode::Lenient,
            features: FeatureOptions {
                validate_experimental: true,
                performance_warnings: true,
                enable_parallelism: true,
            },
            phase_timeout: std::time::Duration::from_secs(30),
            target_provider: None,
            max_diagnostics: 100,
        }
    }
}

impl DatabaseProvider {
    /// Get the provider name as a string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            DatabaseProvider::PostgreSQL => "postgresql",
            DatabaseProvider::MySQL => "mysql",
            DatabaseProvider::SQLite => "sqlite",
            DatabaseProvider::SQLServer => "sqlserver",
            DatabaseProvider::MongoDB => "mongodb",
        }
    }
}
