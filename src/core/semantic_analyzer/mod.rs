use compiler_macros::EnumKindName;

pub mod diagnostics;
pub mod symbol_table;
pub mod type_resolver;

// Re-export main types for convenience
pub use diagnostics::{DiagnosticCode, FixHint, SemanticDiagnostic};
pub use symbol_table::{Symbol, SymbolTable, SymbolType};

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

/// Concurrency mode for semantic analysis
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConcurrencyMode {
    /// Single-threaded analysis
    Sequential,
    /// Multi-threaded analysis with specified thread count and threshold
    Concurrent {
        max_threads: usize,
        threshold: usize,
    },
}

#[derive(Debug, Clone)]
pub struct AnalyzerOptions {
    /// Validation mode
    pub validation_mode: ValidationMode,

    /// Feature validation options
    pub features: FeatureOptions,

    /// Concurrency mode for analysis
    pub concurrency: ConcurrencyMode,

    /// Maximum analysis time per phase
    pub phase_timeout: std::time::Duration,

    /// Target database provider for validation
    pub target_provider: Option<DatabaseProvider>,

    /// Maximum number of diagnostics to collect before stopping
    pub max_diagnostics: usize,
}

/// Supported database providers for provider-specific validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumKindName)]
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
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 2,
            },
            phase_timeout: std::time::Duration::from_secs(30),
            target_provider: None,
            max_diagnostics: 100,
        }
    }
}
