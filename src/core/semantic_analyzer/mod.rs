use compiler_macros::EnumKindName;

pub mod context;
pub mod diagnostics;
pub mod symbol_table;
pub mod traits;
pub mod type_resolver;

// Re-export main types for convenience
pub use context::{AnalysisContext, AnalysisResult};
pub use diagnostics::{DiagnosticCode, FixHint, SemanticDiagnostic};
pub use symbol_table::{Symbol, SymbolTable, SymbolType};
pub use traits::{
    AttributeAnalyzer, DeclarationAnalyzer, PhaseAnalyzer, RelationshipAnalyzer,
};

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

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_validation_mode_variants() {
        let lenient = ValidationMode::Lenient;
        let strict = ValidationMode::Strict;

        assert_eq!(lenient, ValidationMode::Lenient);
        assert_eq!(strict, ValidationMode::Strict);
        assert_ne!(lenient, strict);

        // Test Debug trait
        assert_eq!(format!("{lenient:?}"), "Lenient");
        assert_eq!(format!("{strict:?}"), "Strict");
    }

    #[test]
    fn test_database_provider_as_str() {
        assert_eq!(DatabaseProvider::PostgreSQL.name(), "PostgreSQL");
        assert_eq!(DatabaseProvider::MySQL.name(), "MySQL");
        assert_eq!(DatabaseProvider::SQLite.name(), "SQLite");
        assert_eq!(DatabaseProvider::SQLServer.name(), "SQLServer");
        assert_eq!(DatabaseProvider::MongoDB.name(), "MongoDB");
    }

    #[test]
    fn test_database_provider_variants() {
        let providers = [
            DatabaseProvider::PostgreSQL,
            DatabaseProvider::MySQL,
            DatabaseProvider::SQLite,
            DatabaseProvider::SQLServer,
            DatabaseProvider::MongoDB,
        ];

        // Test equality and uniqueness
        for (i, provider1) in providers.iter().enumerate() {
            for (j, provider2) in providers.iter().enumerate() {
                if i == j {
                    assert_eq!(provider1, provider2);
                } else {
                    assert_ne!(provider1, provider2);
                }
            }
        }

        // Test Debug trait
        assert_eq!(format!("{:?}", DatabaseProvider::PostgreSQL), "PostgreSQL");
        assert_eq!(format!("{:?}", DatabaseProvider::MongoDB), "MongoDB");
    }

    #[test]
    fn test_feature_options() {
        let features = FeatureOptions {
            validate_experimental: true,
            performance_warnings: false,
            enable_parallelism: true,
        };

        assert!(features.validate_experimental);
        assert!(!features.performance_warnings);
        assert!(features.enable_parallelism);

        // Test Debug and Clone
        let cloned = features.clone();
        assert_eq!(
            cloned.validate_experimental,
            features.validate_experimental
        );
        assert_eq!(cloned.performance_warnings, features.performance_warnings);
        assert_eq!(cloned.enable_parallelism, features.enable_parallelism);
    }

    #[test]
    fn test_analyzer_options_default() {
        let options = AnalyzerOptions::default();

        assert_eq!(options.validation_mode, ValidationMode::Lenient);
        assert!(options.features.validate_experimental);
        assert!(options.features.performance_warnings);
        assert!(options.features.enable_parallelism);
        assert_eq!(options.phase_timeout, Duration::from_secs(30));
        assert_eq!(options.target_provider, None);
        assert_eq!(options.max_diagnostics, 100);
    }

    #[test]
    fn test_analyzer_options_with_custom_values() {
        let features = FeatureOptions {
            validate_experimental: false,
            performance_warnings: true,
            enable_parallelism: false,
        };

        let options = AnalyzerOptions {
            validation_mode: ValidationMode::Strict,
            features: features.clone(),
            concurrency: ConcurrencyMode::Sequential,
            phase_timeout: Duration::from_secs(60),
            target_provider: Some(DatabaseProvider::PostgreSQL),
            max_diagnostics: 200,
        };

        assert_eq!(options.validation_mode, ValidationMode::Strict);
        assert!(!options.features.validate_experimental);
        assert!(options.features.performance_warnings);
        assert!(!options.features.enable_parallelism);
        assert_eq!(options.phase_timeout, Duration::from_secs(60));
        assert_eq!(options.target_provider, Some(DatabaseProvider::PostgreSQL));
        assert_eq!(options.max_diagnostics, 200);

        // Test Debug and Clone
        let cloned_options = options.clone();
        assert_eq!(cloned_options.validation_mode, options.validation_mode);
        assert_eq!(cloned_options.max_diagnostics, options.max_diagnostics);
    }

    #[test]
    fn test_analyzer_options_with_all_providers() {
        let providers = [
            Some(DatabaseProvider::PostgreSQL),
            Some(DatabaseProvider::MySQL),
            Some(DatabaseProvider::SQLite),
            Some(DatabaseProvider::SQLServer),
            Some(DatabaseProvider::MongoDB),
            None,
        ];

        for provider in providers {
            let options = AnalyzerOptions {
                validation_mode: ValidationMode::Lenient,
                features: FeatureOptions {
                    validate_experimental: true,
                    performance_warnings: true,
                    enable_parallelism: true,
                },
                concurrency: ConcurrencyMode::Sequential,
                phase_timeout: Duration::from_secs(30),
                target_provider: provider,
                max_diagnostics: 100,
            };

            assert_eq!(options.target_provider, provider);

            if let Some(p) = provider {
                let _ = p.name();
            }
        }
    }

    #[test]
    fn test_validation_mode_ordering() {
        // ValidationMode should support PartialEq, Eq
        assert_eq!(ValidationMode::Lenient, ValidationMode::Lenient);
        assert_eq!(ValidationMode::Strict, ValidationMode::Strict);
        assert_ne!(ValidationMode::Lenient, ValidationMode::Strict);

        // Test copy behavior
        let mode1 = ValidationMode::Lenient;
        let mode2 = mode1; // This should copy, not move
        assert_eq!(mode1, mode2);
    }

    #[test]
    fn test_database_provider_hash() {
        use std::collections::HashMap;

        let mut provider_names = HashMap::new();
        provider_names.insert(DatabaseProvider::PostgreSQL, "postgres");
        provider_names.insert(DatabaseProvider::MySQL, "mysql");
        provider_names.insert(DatabaseProvider::SQLite, "sqlite");
        provider_names.insert(DatabaseProvider::SQLServer, "sqlserver");
        provider_names.insert(DatabaseProvider::MongoDB, "mongo");

        assert_eq!(
            provider_names.get(&DatabaseProvider::PostgreSQL),
            Some(&"postgres")
        );
        assert_eq!(
            provider_names.get(&DatabaseProvider::MongoDB),
            Some(&"mongo")
        );
        assert_eq!(provider_names.len(), 5);
    }
}
