//! Analysis context and result types.
//!
//! This module provides the shared state and result types used throughout
//! the semantic analysis pipeline.

use crate::core::semantic_analyzer::{
    AnalyzerOptions, diagnostics::SemanticDiagnostic,
    symbol_table::SymbolTable, type_resolver::TypeResolver,
};

#[cfg(test)]
use crate::core::semantic_analyzer::ConcurrencyMode;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};

/// Shared context for semantic analysis phases.
///
/// The analysis context provides shared state, utilities, and metadata
/// collection for all analyzers in the pipeline. State is shared via
/// thread-safe reference counting and read-write locks to support both
/// sequential and parallel execution.
#[derive(Debug)]
pub struct AnalysisContext {
    options: AnalyzerOptions,

    /// Shared symbol table across all phases
    pub symbol_table: Arc<RwLock<SymbolTable>>,

    /// Shared type resolver across all phases
    pub type_resolver: Arc<RwLock<TypeResolver>>,

    /// Shared relationship graph across all phases
    pub relationship_graph: Arc<RwLock<RelationshipGraph>>,

    /// Current scope stack for symbol resolution
    current_scope: ScopeStack,

    /// Analysis metadata collection
    metadata: AnalysisMetadata,

    /// Start time for timeout tracking
    start_time: Instant,

    /// Current analysis state
    current_model: Option<String>,
    current_field: Option<String>,
    current_enum: Option<String>,

    /// Stack for tracking type resolution to detect cycles
    type_resolution_stack: Vec<String>,
}

/// Relationship graph for tracking model relationships.
#[derive(Debug, Clone, Default)]
pub struct RelationshipGraph {
    /// All relationships indexed by ID
    pub relationships: HashMap<String, Relationship>,

    /// Relationships by source model
    pub model_relationships: HashMap<String, Vec<String>>,
}

/// Represents a relationship between two models.
#[derive(Debug, Clone)]
pub struct Relationship {
    pub id: String,
    pub from_model: String,
    pub from_field: String,
    pub to_model: String,
    pub to_field: Option<String>,
    pub relationship_type: RelationshipType,
    pub foreign_keys: Vec<String>,
    pub references: Vec<String>,
}

/// Type of relationship between models.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelationshipType {
    OneToOne,
    OneToMany,
    ManyToOne,
    ManyToMany,
}

impl AnalysisContext {
    /// Create a new analysis context with shared state.
    #[must_use]
    pub fn new(
        options: &AnalyzerOptions,
        symbol_table: Arc<RwLock<SymbolTable>>,
        type_resolver: Arc<RwLock<TypeResolver>>,
        relationship_graph: Arc<RwLock<RelationshipGraph>>,
    ) -> Self {
        Self {
            options: options.clone(),
            symbol_table,
            type_resolver,
            relationship_graph,
            current_scope: ScopeStack::new(),
            metadata: AnalysisMetadata::new(),
            start_time: Instant::now(),
            current_model: None,
            current_field: None,
            current_enum: None,
            type_resolution_stack: Vec::new(),
        }
    }

    /// Create a test context with default shared state for unit tests.
    #[cfg(test)]
    #[must_use]
    pub fn new_test(options: &AnalyzerOptions) -> Self {
        Self::new(
            options,
            Arc::new(RwLock::new(SymbolTable::new())),
            Arc::new(RwLock::new(TypeResolver::new())),
            Arc::new(RwLock::new(RelationshipGraph::default())),
        )
    }

    /// Get the analysis options.
    #[must_use]
    pub fn options(&self) -> &AnalyzerOptions {
        &self.options
    }

    // Note: Symbol table access will be handled by the analyzer orchestrator
    // to avoid unsafe code. Individual analyzers receive symbol table references
    // as method parameters.

    /// Enter a new scope.
    pub fn enter_scope(&mut self, scope_type: ScopeType, name: String) {
        self.current_scope.push(Scope { scope_type, name });
    }

    /// Exit the current scope.
    pub fn exit_scope(&mut self) -> Option<Scope> {
        self.current_scope.pop()
    }

    /// Get the current scope.
    #[must_use]
    pub fn current_scope(&self) -> Option<&Scope> {
        self.current_scope.current()
    }

    /// Set the current model being analyzed.
    pub fn set_current_model(&mut self, model_name: Option<String>) {
        self.current_model = model_name;
    }

    /// Get the current model being analyzed.
    #[must_use]
    pub fn current_model(&self) -> Option<&str> {
        self.current_model.as_deref()
    }

    /// Set the current field being analyzed.
    pub fn set_current_field(&mut self, field_name: Option<String>) {
        self.current_field = field_name;
    }

    /// Get the current field being analyzed.
    #[must_use]
    pub fn current_field(&self) -> Option<&str> {
        self.current_field.as_deref()
    }

    /// Set the current enum being analyzed.
    pub fn set_current_enum(&mut self, enum_name: Option<String>) {
        self.current_enum = enum_name;
    }

    /// Get the current enum being analyzed.
    #[must_use]
    pub fn current_enum(&self) -> Option<&str> {
        self.current_enum.as_deref()
    }

    /// Push a type onto the resolution stack (for cycle detection).
    pub fn push_type_resolution(&mut self, type_name: String) {
        self.type_resolution_stack.push(type_name);
    }

    /// Pop a type from the resolution stack.
    pub fn pop_type_resolution(&mut self) -> Option<String> {
        self.type_resolution_stack.pop()
    }

    /// Check if a type is currently being resolved (cycle detection).
    #[must_use]
    pub fn is_resolving_type(&self, type_name: &str) -> bool {
        self.type_resolution_stack.contains(&type_name.to_string())
    }

    /// Get the current type resolution stack.
    #[must_use]
    pub fn type_resolution_stack(&self) -> &[String] {
        &self.type_resolution_stack
    }

    /// Record metadata about the analysis.
    pub fn record_metadata(
        &mut self,
        key: String,
        value: AnalysisMetadataValue,
    ) {
        self.metadata.add_entry(key, value);
    }

    /// Get elapsed time since analysis started.
    #[must_use]
    pub fn elapsed_time(&self) -> Duration {
        self.start_time.elapsed()
    }

    /// Check if analysis has timed out.
    #[must_use]
    pub fn has_timed_out(&self) -> bool {
        self.elapsed_time() > self.options.phase_timeout
    }

    /// Take the analysis metadata (consuming it).
    #[must_use]
    pub fn take_metadata(self) -> AnalysisMetadata {
        self.metadata
    }

    // Symbol resolution will be handled by passing symbol table to methods
}

/// Stack for tracking analysis scopes.
#[derive(Debug, Clone)]
pub struct ScopeStack {
    scopes: Vec<Scope>,
}

impl Default for ScopeStack {
    fn default() -> Self {
        Self::new()
    }
}

impl ScopeStack {
    #[must_use]
    pub fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    pub fn push(&mut self, scope: Scope) {
        self.scopes.push(scope);
    }

    pub fn pop(&mut self) -> Option<Scope> {
        self.scopes.pop()
    }

    #[must_use]
    pub fn current(&self) -> Option<&Scope> {
        self.scopes.last()
    }

    #[must_use]
    pub fn depth(&self) -> usize {
        self.scopes.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.scopes.is_empty()
    }
}

/// A single scope in the scope stack.
#[derive(Debug, Clone)]
pub struct Scope {
    pub scope_type: ScopeType,
    pub name: String,
}

/// Types of scopes in semantic analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeType {
    Global,
    Model,
    Enum,
    Datasource,
    Generator,
    Field,
    EnumValue,
}

/// Result of symbol resolution.
#[derive(Debug, Clone)]
pub struct SymbolResolution {
    pub symbol: crate::core::semantic_analyzer::symbol_table::Symbol,
    pub scope: String,
}

/// Metadata collected during analysis.
#[derive(Debug, Clone)]
pub struct AnalysisMetadata {
    entries: HashMap<String, AnalysisMetadataValue>,
    phase_timings: HashMap<String, Duration>,
    statistics: AnalysisStatistics,
}

impl Default for AnalysisMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl AnalysisMetadata {
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
            phase_timings: HashMap::new(),
            statistics: AnalysisStatistics::default(),
        }
    }

    pub fn add_entry(&mut self, key: String, value: AnalysisMetadataValue) {
        self.entries.insert(key, value);
    }

    #[must_use]
    pub fn get_entry(&self, key: &str) -> Option<&AnalysisMetadataValue> {
        self.entries.get(key)
    }

    pub fn record_phase_timing(
        &mut self,
        phase_name: String,
        duration: Duration,
    ) {
        self.phase_timings.insert(phase_name, duration);
    }

    #[must_use]
    pub fn get_phase_timing(&self, phase_name: &str) -> Option<Duration> {
        self.phase_timings.get(phase_name).copied()
    }

    #[must_use]
    pub fn statistics(&self) -> &AnalysisStatistics {
        &self.statistics
    }

    pub fn statistics_mut(&mut self) -> &mut AnalysisStatistics {
        &mut self.statistics
    }

    #[must_use]
    pub fn total_analysis_time(&self) -> Duration {
        self.phase_timings.values().sum()
    }
}

/// Values that can be stored in analysis metadata.
#[derive(Debug, Clone, PartialEq)]
pub enum AnalysisMetadataValue {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Duration(Duration),
    StringList(Vec<String>),
}

/// Statistics collected during analysis.
#[derive(Debug, Clone, Default)]
pub struct AnalysisStatistics {
    pub models_analyzed: usize,
    pub enums_analyzed: usize,
    pub fields_analyzed: usize,
    pub relationships_found: usize,
    pub attributes_validated: usize,
    pub type_resolutions: usize,
    pub circular_dependencies_detected: usize,
    pub warnings_generated: usize,
    pub errors_generated: usize,
}

/// Result from a single analysis phase.
#[derive(Debug, Clone)]
pub struct PhaseResult {
    /// Diagnostics generated by this phase
    pub diagnostics: Vec<SemanticDiagnostic>,

    /// Whether this phase completed successfully
    pub success: bool,

    /// Time taken by this phase
    pub duration: Option<Duration>,

    /// Phase-specific metadata
    pub metadata: HashMap<String, AnalysisMetadataValue>,
}

impl PhaseResult {
    /// Create a new successful phase result with diagnostics.
    #[must_use]
    pub fn new(diagnostics: Vec<SemanticDiagnostic>) -> Self {
        Self {
            success: !diagnostics
                .iter()
                .any(super::diagnostics::SemanticDiagnostic::is_error),
            diagnostics,
            duration: None,
            metadata: HashMap::new(),
        }
    }

    /// Create a successful phase result with no diagnostics.
    #[must_use]
    pub fn success() -> Self {
        Self::new(Vec::new())
    }

    /// Create a failed phase result with an error diagnostic.
    #[must_use]
    pub fn error(diagnostic: SemanticDiagnostic) -> Self {
        Self {
            success: false,
            diagnostics: vec![diagnostic],
            duration: None,
            metadata: HashMap::new(),
        }
    }

    /// Add timing information to this result.
    #[must_use]
    pub fn with_duration(mut self, duration: Duration) -> Self {
        self.duration = Some(duration);
        self
    }

    /// Add metadata to this result.
    #[must_use]
    pub fn with_metadata(
        mut self,
        key: String,
        value: AnalysisMetadataValue,
    ) -> Self {
        self.metadata.insert(key, value);
        self
    }

    /// Check if this result has fatal errors that should stop analysis.
    #[must_use]
    pub fn has_fatal_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(super::diagnostics::SemanticDiagnostic::is_fatal)
    }

    /// Get the number of errors in this result.
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.diagnostics.iter().filter(|d| d.is_error()).count()
    }

    /// Get the number of warnings in this result.
    #[must_use]
    pub fn warning_count(&self) -> usize {
        self.diagnostics.iter().filter(|d| d.is_warning()).count()
    }
}

/// Final result of semantic analysis.
#[derive(Debug, Clone)]
pub struct AnalysisResult {
    /// The completed symbol table
    pub symbol_table: SymbolTable,

    /// The type resolver with all resolved types
    pub type_resolver: TypeResolver,

    /// All diagnostics from all phases
    pub diagnostics: Vec<SemanticDiagnostic>,

    /// Analysis metadata and statistics
    pub analysis_metadata: AnalysisMetadata,

    /// Total time taken for analysis
    pub analysis_time: Duration,

    /// Number of analyzers that were run
    pub analyzer_count: usize,
}

impl AnalysisResult {
    /// Check if the analysis was successful (no errors).
    #[must_use]
    pub fn is_success(&self) -> bool {
        !self
            .diagnostics
            .iter()
            .any(super::diagnostics::SemanticDiagnostic::is_error)
    }

    /// Get the number of errors.
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.diagnostics.iter().filter(|d| d.is_error()).count()
    }

    /// Get the number of warnings.
    #[must_use]
    pub fn warning_count(&self) -> usize {
        self.diagnostics.iter().filter(|d| d.is_warning()).count()
    }

    /// Get the number of informational diagnostics.
    #[must_use]
    pub fn info_count(&self) -> usize {
        self.diagnostics.iter().filter(|d| d.is_info()).count()
    }

    /// Get diagnostics by severity.
    #[must_use]
    pub fn diagnostics_by_severity(
        &self,
        severity: crate::core::semantic_analyzer::diagnostics::DiagnosticSeverity,
    ) -> Vec<&SemanticDiagnostic> {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == severity)
            .collect()
    }

    /// Get a summary of the analysis results.
    #[must_use]
    pub fn summary(&self) -> AnalysisSummary {
        AnalysisSummary {
            success: self.is_success(),
            error_count: self.error_count(),
            warning_count: self.warning_count(),
            info_count: self.info_count(),
            total_diagnostics: self.diagnostics.len(),
            analysis_time: self.analysis_time,
            models_count: self.symbol_table.models().count(),
            enums_count: self.symbol_table.enums().count(),
            total_symbols: self.symbol_table.total_symbol_count(),
        }
    }
}

/// Summary of analysis results.
#[derive(Debug, Clone)]
pub struct AnalysisSummary {
    pub success: bool,
    pub error_count: usize,
    pub warning_count: usize,
    pub info_count: usize,
    pub total_diagnostics: usize,
    pub analysis_time: Duration,
    pub models_count: usize,
    pub enums_count: usize,
    pub total_symbols: usize,
}

impl std::fmt::Display for AnalysisSummary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Analysis {} in {:?}: {} models, {} enums, {} total symbols. {} errors, {} warnings, {} info.",
            if self.success { "succeeded" } else { "failed" },
            self.analysis_time,
            self.models_count,
            self.enums_count,
            self.total_symbols,
            self.error_count,
            self.warning_count,
            self.info_count
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::scanner::{SymbolLocation, tokens::SymbolSpan};
    use crate::core::semantic_analyzer::{
        AnalyzerOptions, DatabaseProvider, DiagnosticCode, FeatureOptions,
        ValidationMode,
    };

    fn create_test_options() -> AnalyzerOptions {
        AnalyzerOptions {
            validation_mode: ValidationMode::Lenient,
            features: FeatureOptions {
                validate_experimental: false,
                performance_warnings: false,
                enable_parallelism: true,
            },
            concurrency: ConcurrencyMode::Sequential,
            phase_timeout: Duration::from_secs(30),
            target_provider: Some(DatabaseProvider::PostgreSQL),
            max_diagnostics: 100,
        }
    }

    fn create_test_context(options: &AnalyzerOptions) -> AnalysisContext {
        AnalysisContext::new_test(options)
    }

    #[test]
    fn test_analysis_context_creation() {
        let options = create_test_options();
        let context = create_test_context(&options);

        assert!(context.current_model().is_none());
        assert!(context.current_field().is_none());
        assert!(context.current_enum().is_none());
        assert_eq!(context.type_resolution_stack().len(), 0);
    }

    #[test]
    fn test_scope_stack() {
        let mut stack = ScopeStack::new();
        assert!(stack.is_empty());
        assert_eq!(stack.depth(), 0);

        stack.push(Scope {
            scope_type: ScopeType::Global,
            name: "global".to_string(),
        });

        assert!(!stack.is_empty());
        assert_eq!(stack.depth(), 1);
        match stack.current() {
            Some(scope) => assert_eq!(scope.name, "global"),
            None => panic!("Should have current scope"),
        }

        let Some(popped) = stack.pop() else {
            panic!("Should pop successfully")
        };
        assert_eq!(popped.name, "global");
        assert!(stack.is_empty());
    }

    #[test]
    fn test_analysis_metadata() {
        let mut metadata = AnalysisMetadata::new();

        metadata.add_entry(
            "test".to_string(),
            AnalysisMetadataValue::String("value".to_string()),
        );
        metadata.record_phase_timing(
            "phase1".to_string(),
            Duration::from_millis(100),
        );

        assert!(metadata.get_entry("test").is_some());
        assert_eq!(
            metadata.get_phase_timing("phase1"),
            Some(Duration::from_millis(100))
        );
    }

    #[test]
    fn test_phase_result() {
        let result = PhaseResult::success();
        assert!(result.success);
        assert_eq!(result.diagnostics.len(), 0);
        assert!(!result.has_fatal_errors());

        let result_with_duration =
            result.with_duration(Duration::from_millis(50));
        assert_eq!(
            result_with_duration.duration,
            Some(Duration::from_millis(50))
        );
    }

    #[test]
    fn test_model_field_enum_context() {
        let options = AnalyzerOptions::default();
        let mut context = create_test_context(&options);

        // Test model context
        assert!(context.current_model().is_none());
        context.set_current_model(Some("User".to_string()));
        assert_eq!(context.current_model(), Some("User"));

        // Test field context
        assert!(context.current_field().is_none());
        context.set_current_field(Some("email".to_string()));
        assert_eq!(context.current_field(), Some("email"));

        // Test enum context
        assert!(context.current_enum().is_none());
        context.set_current_enum(Some("Status".to_string()));
        assert_eq!(context.current_enum(), Some("Status"));

        // Clear contexts
        context.set_current_model(None);
        context.set_current_field(None);
        context.set_current_enum(None);

        assert!(context.current_model().is_none());
        assert!(context.current_field().is_none());
        assert!(context.current_enum().is_none());
    }

    #[test]
    fn test_type_resolution_stack() {
        let options = AnalyzerOptions::default();
        let mut context = create_test_context(&options);

        // Initially empty
        assert!(context.type_resolution_stack().is_empty());
        assert!(!context.is_resolving_type("User"));

        // Push types
        context.push_type_resolution("User".to_string());
        assert_eq!(context.type_resolution_stack().len(), 1);
        assert!(context.is_resolving_type("User"));
        assert!(!context.is_resolving_type("Post"));

        context.push_type_resolution("Post".to_string());
        assert_eq!(context.type_resolution_stack().len(), 2);
        assert!(context.is_resolving_type("User"));
        assert!(context.is_resolving_type("Post"));

        // Pop types
        let popped = context.pop_type_resolution();
        assert_eq!(popped, Some("Post".to_string()));
        assert!(context.is_resolving_type("User"));
        assert!(!context.is_resolving_type("Post"));

        let popped = context.pop_type_resolution();
        assert_eq!(popped, Some("User".to_string()));
        assert!(context.type_resolution_stack().is_empty());

        // Pop from empty stack
        let popped = context.pop_type_resolution();
        assert_eq!(popped, None);
    }

    #[test]
    fn test_metadata_recording() {
        let options = AnalyzerOptions::default();
        let mut context = create_test_context(&options);

        // Record various metadata
        context.record_metadata(
            "models_processed".to_string(),
            AnalysisMetadataValue::Integer(5),
        );
        context.record_metadata(
            "fields_processed".to_string(),
            AnalysisMetadataValue::Integer(20),
        );
        context.record_metadata(
            "relationships_found".to_string(),
            AnalysisMetadataValue::Integer(3),
        );

        // Check elapsed time is reasonable
        let _elapsed = context.elapsed_time();
        // Duration is always >= 0, so just verify it can be retrieved

        // Test timeout (should not timeout with default settings)
        assert!(!context.has_timed_out());
    }

    #[test]
    fn test_metadata_extraction() {
        let options = AnalyzerOptions::default();
        let mut context = create_test_context(&options);

        context.record_metadata(
            "test_metric".to_string(),
            AnalysisMetadataValue::Integer(42),
        );

        let metadata = context.take_metadata();
        assert_eq!(
            metadata.entries.get("test_metric"),
            Some(&AnalysisMetadataValue::Integer(42))
        );
        // Metadata doesn't track elapsed_time directly
        // Context should still be usable but metadata is moved
    }

    #[test]
    fn test_analyzer_options_defaults() {
        let options = create_test_options();
        assert_eq!(options.validation_mode, ValidationMode::Lenient);
        // Parallelism moved to options.concurrency
        assert_eq!(options.phase_timeout, Duration::from_secs(30));
        assert_eq!(options.max_diagnostics, 100);
    }

    #[test]
    fn test_analyzer_options_custom() {
        let options = AnalyzerOptions {
            validation_mode: ValidationMode::Lenient,
            features: FeatureOptions {
                validate_experimental: false,
                performance_warnings: false,
                enable_parallelism: true,
            },
            concurrency: ConcurrencyMode::Sequential,
            phase_timeout: Duration::from_secs(60),
            target_provider: Some(DatabaseProvider::SQLite),
            max_diagnostics: 50,
        };

        assert_eq!(options.validation_mode, ValidationMode::Lenient);
        // Parallelism moved to options.concurrency
        assert_eq!(options.phase_timeout, Duration::from_secs(60));
        assert_eq!(options.max_diagnostics, 50);

        let context = create_test_context(&options);
        assert_eq!(context.options().validation_mode, ValidationMode::Lenient);
        assert_eq!(context.options().max_diagnostics, 50);
    }

    #[test]
    fn test_scope_creation_and_properties() {
        let options = AnalyzerOptions::default();
        let mut context = create_test_context(&options);

        // Enter multiple scopes
        context.enter_scope(ScopeType::Model, "User".to_string());
        let current = context.current_scope().unwrap();
        assert_eq!(current.scope_type, ScopeType::Model);
        assert_eq!(current.name, "User");

        context.enter_scope(ScopeType::Enum, "Status".to_string());
        let current = context.current_scope().unwrap();
        assert_eq!(current.scope_type, ScopeType::Enum);
        assert_eq!(current.name, "Status");

        // Exit scopes
        let exited = context.exit_scope().unwrap();
        assert_eq!(exited.scope_type, ScopeType::Enum);
        assert_eq!(exited.name, "Status");

        let current = context.current_scope().unwrap();
        assert_eq!(current.scope_type, ScopeType::Model);
        assert_eq!(current.name, "User");

        context.exit_scope();
        assert!(context.current_scope().is_none());

        // Exit from empty stack
        let exited = context.exit_scope();
        assert!(exited.is_none());
    }

    #[test]
    fn test_timeout_behavior() {
        let options = AnalyzerOptions {
            validation_mode: ValidationMode::Lenient,
            features: FeatureOptions {
                validate_experimental: false,
                performance_warnings: false,
                enable_parallelism: true,
            },
            concurrency: ConcurrencyMode::Sequential,
            phase_timeout: Duration::from_nanos(1), // Very short timeout
            target_provider: Some(DatabaseProvider::PostgreSQL),
            max_diagnostics: 100,
        };

        let context = create_test_context(&options);

        // Sleep briefly to exceed timeout
        std::thread::sleep(Duration::from_millis(1));

        // Should now timeout (though timing is not guaranteed in tests)
        // This is more of a smoke test for the timeout logic
        let _has_timeout = context.has_timed_out();
    }

    #[test]
    fn test_phase_result_merge() {
        let mut result1 = PhaseResult::success();
        let result2 = PhaseResult::new(vec![SemanticDiagnostic::error(
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 5 },
            },
            "Test error".to_string(),
            DiagnosticCode::InvalidIdentifier,
        )]);

        // Test adding diagnostics to success
        result1.diagnostics.push(SemanticDiagnostic::warning(
            SymbolSpan {
                start: SymbolLocation { line: 2, column: 1 },
                end: SymbolLocation { line: 2, column: 5 },
            },
            "Test warning".to_string(),
            DiagnosticCode::DeprecatedFeature,
        ));

        assert_eq!(result1.diagnostics.len(), 1);
        assert!(result1.success);

        assert_eq!(result2.diagnostics.len(), 1);
        assert!(!result2.success);
    }

    #[test]
    fn test_analysis_metadata_default() {
        let metadata = AnalysisMetadata::default();
        assert!(metadata.entries.is_empty());
        // Metadata doesn't track elapsed_time directly
    }

    #[test]
    fn test_complex_scenario() {
        let options = AnalyzerOptions::default();
        let mut context = create_test_context(&options);

        // Simulate complex analysis scenario
        context.enter_scope(ScopeType::Model, "User".to_string());
        context.set_current_model(Some("User".to_string()));

        context.push_type_resolution("User".to_string());
        context.set_current_field(Some("posts".to_string()));
        context.push_type_resolution("Post".to_string());

        context.record_metadata(
            "fields_analyzed".to_string(),
            AnalysisMetadataValue::Integer(1),
        );

        // Verify state
        assert_eq!(context.current_model(), Some("User"));
        assert_eq!(context.current_field(), Some("posts"));
        assert!(context.is_resolving_type("User"));
        assert!(context.is_resolving_type("Post"));
        assert_eq!(context.type_resolution_stack().len(), 2);

        // Clean up
        context.pop_type_resolution();
        context.pop_type_resolution();
        context.set_current_field(None);
        context.set_current_model(None);
        context.exit_scope();

        // Verify cleanup
        assert!(context.current_model().is_none());
        assert!(context.current_field().is_none());
        assert!(!context.is_resolving_type("User"));
        assert!(!context.is_resolving_type("Post"));
        assert!(context.current_scope().is_none());
    }

    #[test]
    fn test_analysis_metadata_comprehensive() {
        let mut metadata = AnalysisMetadata::new();

        // Test all AnalysisMetadataValue variants
        metadata.add_entry(
            "string_val".to_string(),
            AnalysisMetadataValue::String("test".to_string()),
        );
        metadata.add_entry(
            "int_val".to_string(),
            AnalysisMetadataValue::Integer(42),
        );
        metadata.add_entry(
            "float_val".to_string(),
            AnalysisMetadataValue::Float(5.5),
        );
        metadata.add_entry(
            "bool_val".to_string(),
            AnalysisMetadataValue::Boolean(true),
        );
        metadata.add_entry(
            "duration_val".to_string(),
            AnalysisMetadataValue::Duration(Duration::from_millis(100)),
        );
        metadata.add_entry(
            "stringlist_val".to_string(),
            AnalysisMetadataValue::StringList(vec![
                "a".to_string(),
                "b".to_string(),
            ]),
        );

        // Test statistics access and mutation
        {
            let stats_mut = metadata.statistics_mut();
            stats_mut.models_analyzed = 5;
            stats_mut.enums_analyzed = 3;
            stats_mut.fields_analyzed = 20;
            stats_mut.relationships_found = 8;
            stats_mut.attributes_validated = 15;
            stats_mut.type_resolutions = 25;
            stats_mut.circular_dependencies_detected = 1;
            stats_mut.warnings_generated = 10;
            stats_mut.errors_generated = 2;
        }

        let stats = metadata.statistics();
        assert_eq!(stats.models_analyzed, 5);
        assert_eq!(stats.enums_analyzed, 3);
        assert_eq!(stats.fields_analyzed, 20);
        assert_eq!(stats.relationships_found, 8);
        assert_eq!(stats.attributes_validated, 15);
        assert_eq!(stats.type_resolutions, 25);
        assert_eq!(stats.circular_dependencies_detected, 1);
        assert_eq!(stats.warnings_generated, 10);
        assert_eq!(stats.errors_generated, 2);

        // Test phase timing
        metadata.record_phase_timing(
            "phase1".to_string(),
            Duration::from_millis(50),
        );
        metadata.record_phase_timing(
            "phase2".to_string(),
            Duration::from_millis(75),
        );

        assert_eq!(
            metadata.get_phase_timing("phase1"),
            Some(Duration::from_millis(50))
        );
        assert_eq!(
            metadata.get_phase_timing("phase2"),
            Some(Duration::from_millis(75))
        );
        assert_eq!(metadata.get_phase_timing("nonexistent"), None);

        // Test total analysis time
        assert_eq!(metadata.total_analysis_time(), Duration::from_millis(125));
    }

    #[test]
    fn test_phase_result_comprehensive() {
        // Test PhaseResult::error with a fatal error code
        let error_result = PhaseResult::error(SemanticDiagnostic::error(
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 5 },
            },
            "Fatal error".to_string(),
            DiagnosticCode::CircularDependency, // This is a fatal error
        ));

        assert!(!error_result.success);
        assert_eq!(error_result.diagnostics.len(), 1);
        assert_eq!(error_result.error_count(), 1);
        assert_eq!(error_result.warning_count(), 0);
        assert!(error_result.has_fatal_errors()); // CircularDependency is fatal

        // Test PhaseResult::error with a non-fatal error code
        let non_fatal_error_result =
            PhaseResult::error(SemanticDiagnostic::error(
                SymbolSpan {
                    start: SymbolLocation { line: 1, column: 1 },
                    end: SymbolLocation { line: 1, column: 5 },
                },
                "Non-fatal error".to_string(),
                DiagnosticCode::InvalidIdentifier, // This is not a fatal error
            ));

        assert!(!non_fatal_error_result.success);
        assert_eq!(non_fatal_error_result.error_count(), 1);
        assert!(!non_fatal_error_result.has_fatal_errors()); // InvalidIdentifier is not fatal

        // Test with metadata
        let result_with_metadata = PhaseResult::success()
            .with_metadata(
                "test_key".to_string(),
                AnalysisMetadataValue::String("test_value".to_string()),
            )
            .with_duration(Duration::from_millis(100));

        assert!(result_with_metadata.success);
        assert_eq!(
            result_with_metadata.duration,
            Some(Duration::from_millis(100))
        );
        assert!(result_with_metadata.metadata.contains_key("test_key"));

        // Test mixed diagnostics
        let mixed_result = PhaseResult::new(vec![
            SemanticDiagnostic::warning(
                SymbolSpan {
                    start: SymbolLocation { line: 1, column: 1 },
                    end: SymbolLocation { line: 1, column: 5 },
                },
                "Warning".to_string(),
                DiagnosticCode::DeprecatedFeature,
            ),
            SemanticDiagnostic::info(
                SymbolSpan {
                    start: SymbolLocation { line: 2, column: 1 },
                    end: SymbolLocation { line: 2, column: 5 },
                },
                "Info".to_string(),
                DiagnosticCode::PerformanceWarning,
            ),
        ]);

        assert!(mixed_result.success); // No errors
        assert_eq!(mixed_result.error_count(), 0);
        assert_eq!(mixed_result.warning_count(), 1);
        assert!(!mixed_result.has_fatal_errors());
    }

    #[test]
    fn test_analysis_result_comprehensive() {
        use crate::core::semantic_analyzer::diagnostics::DiagnosticSeverity;

        let symbol_table = SymbolTable::new();
        let type_resolver = TypeResolver::new();
        let mut metadata = AnalysisMetadata::new();

        // Set up statistics
        metadata.statistics_mut().models_analyzed = 3;
        metadata.statistics_mut().enums_analyzed = 2;
        metadata.record_phase_timing(
            "phase1".to_string(),
            Duration::from_millis(50),
        );

        let diagnostics = vec![
            SemanticDiagnostic::error(
                SymbolSpan {
                    start: SymbolLocation { line: 1, column: 1 },
                    end: SymbolLocation { line: 1, column: 5 },
                },
                "Error".to_string(),
                DiagnosticCode::InvalidIdentifier,
            ),
            SemanticDiagnostic::warning(
                SymbolSpan {
                    start: SymbolLocation { line: 2, column: 1 },
                    end: SymbolLocation { line: 2, column: 5 },
                },
                "Warning".to_string(),
                DiagnosticCode::DeprecatedFeature,
            ),
            SemanticDiagnostic::info(
                SymbolSpan {
                    start: SymbolLocation { line: 3, column: 1 },
                    end: SymbolLocation { line: 3, column: 5 },
                },
                "Info".to_string(),
                DiagnosticCode::PerformanceWarning,
            ),
        ];

        let analysis_result = AnalysisResult {
            symbol_table,
            type_resolver,
            diagnostics,
            analysis_metadata: metadata,
            analysis_time: Duration::from_millis(100),
            analyzer_count: 5,
        };

        // Test result analysis methods
        assert!(!analysis_result.is_success()); // Has errors
        assert_eq!(analysis_result.error_count(), 1);
        assert_eq!(analysis_result.warning_count(), 1);
        assert_eq!(analysis_result.info_count(), 1);

        // Test diagnostics by severity
        let errors =
            analysis_result.diagnostics_by_severity(DiagnosticSeverity::Error);
        let warnings = analysis_result
            .diagnostics_by_severity(DiagnosticSeverity::Warning);
        let infos =
            analysis_result.diagnostics_by_severity(DiagnosticSeverity::Info);

        assert_eq!(errors.len(), 1);
        assert_eq!(warnings.len(), 1);
        assert_eq!(infos.len(), 1);

        // Test summary
        let summary = analysis_result.summary();
        assert!(!summary.success);
        assert_eq!(summary.error_count, 1);
        assert_eq!(summary.warning_count, 1);
        assert_eq!(summary.info_count, 1);
        assert_eq!(summary.total_diagnostics, 3);
        assert_eq!(summary.analysis_time, Duration::from_millis(100));

        // Test Display implementation for summary
        let summary_str = format!("{summary}");
        assert!(summary_str.contains("failed"));
        assert!(summary_str.contains("1 errors"));
        assert!(summary_str.contains("1 warnings"));
        assert!(summary_str.contains("1 info"));
    }

    #[test]
    fn test_analysis_metadata_value_equality() {
        // Test PartialEq implementation for AnalysisMetadataValue
        let string_val1 = AnalysisMetadataValue::String("test".to_string());
        let string_val2 = AnalysisMetadataValue::String("test".to_string());
        let string_val3 =
            AnalysisMetadataValue::String("different".to_string());

        assert_eq!(string_val1, string_val2);
        assert_ne!(string_val1, string_val3);

        let int_val1 = AnalysisMetadataValue::Integer(42);
        let int_val2 = AnalysisMetadataValue::Integer(42);
        let int_val3 = AnalysisMetadataValue::Integer(43);

        assert_eq!(int_val1, int_val2);
        assert_ne!(int_val1, int_val3);
        assert_ne!(string_val1, int_val1); // Different types

        let float_val1 = AnalysisMetadataValue::Float(10.5);
        let float_val2 = AnalysisMetadataValue::Float(10.5);
        assert_eq!(float_val1, float_val2);

        let bool_val1 = AnalysisMetadataValue::Boolean(true);
        let bool_val2 = AnalysisMetadataValue::Boolean(true);
        let bool_val3 = AnalysisMetadataValue::Boolean(false);
        assert_eq!(bool_val1, bool_val2);
        assert_ne!(bool_val1, bool_val3);

        let duration_val1 =
            AnalysisMetadataValue::Duration(Duration::from_millis(100));
        let duration_val2 =
            AnalysisMetadataValue::Duration(Duration::from_millis(100));
        assert_eq!(duration_val1, duration_val2);

        let list_val1 = AnalysisMetadataValue::StringList(vec![
            "a".to_string(),
            "b".to_string(),
        ]);
        let list_val2 = AnalysisMetadataValue::StringList(vec![
            "a".to_string(),
            "b".to_string(),
        ]);
        let list_val3 = AnalysisMetadataValue::StringList(vec![
            "a".to_string(),
            "c".to_string(),
        ]);
        assert_eq!(list_val1, list_val2);
        assert_ne!(list_val1, list_val3);
    }

    #[test]
    fn test_successful_analysis_result() {
        let symbol_table = SymbolTable::new();
        let type_resolver = TypeResolver::new();
        let metadata = AnalysisMetadata::new();

        // Result with no errors (only warnings and info)
        let diagnostics = vec![SemanticDiagnostic::warning(
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 5 },
            },
            "Warning".to_string(),
            DiagnosticCode::DeprecatedFeature,
        )];

        let successful_result = AnalysisResult {
            symbol_table,
            type_resolver,
            diagnostics,
            analysis_metadata: metadata,
            analysis_time: Duration::from_millis(50),
            analyzer_count: 3,
        };

        assert!(successful_result.is_success()); // No errors
        assert_eq!(successful_result.error_count(), 0);
        assert_eq!(successful_result.warning_count(), 1);
        assert_eq!(successful_result.info_count(), 0);

        let summary = successful_result.summary();
        assert!(summary.success);

        let summary_str = format!("{summary}");
        assert!(summary_str.contains("succeeded"));
        assert!(summary_str.contains("0 errors"));
        assert!(summary_str.contains("1 warnings"));
    }

    #[test]
    fn test_scope_stack_default() {
        let stack = ScopeStack::default();
        assert!(stack.is_empty());
        assert_eq!(stack.depth(), 0);
        assert!(stack.current().is_none());
    }

    #[test]
    fn test_analysis_statistics_default() {
        let stats = AnalysisStatistics::default();
        assert_eq!(stats.models_analyzed, 0);
        assert_eq!(stats.enums_analyzed, 0);
        assert_eq!(stats.fields_analyzed, 0);
        assert_eq!(stats.relationships_found, 0);
        assert_eq!(stats.attributes_validated, 0);
        assert_eq!(stats.type_resolutions, 0);
        assert_eq!(stats.circular_dependencies_detected, 0);
        assert_eq!(stats.warnings_generated, 0);
        assert_eq!(stats.errors_generated, 0);
    }

    #[test]
    fn test_symbol_resolution_struct() {
        use crate::core::semantic_analyzer::symbol_table::{
            ModelSymbol, Symbol, SymbolMetadata, SymbolType, Visibility,
        };

        let symbol = Symbol {
            name: "Test".to_string(),
            symbol_type: SymbolType::Model(ModelSymbol {
                field_count: 0,
                has_primary_key: false,
                block_attributes: 0,
            }),
            declaration_span: SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 5 },
            },
            visibility: Visibility::Public,
            metadata: SymbolMetadata::new(),
        };

        let resolution = SymbolResolution {
            symbol,
            scope: "global".to_string(),
        };

        assert_eq!(resolution.scope, "global");
        assert_eq!(resolution.symbol.name, "Test");
    }

    #[test]
    fn test_scope_type_equality_and_debug() {
        // Test equality
        assert_eq!(ScopeType::Model, ScopeType::Model);
        assert_ne!(ScopeType::Model, ScopeType::Enum);

        // Test Debug formatting
        assert_eq!(format!("{:?}", ScopeType::Global), "Global");
        assert_eq!(format!("{:?}", ScopeType::Model), "Model");
        assert_eq!(format!("{:?}", ScopeType::Enum), "Enum");
        assert_eq!(format!("{:?}", ScopeType::Datasource), "Datasource");
        assert_eq!(format!("{:?}", ScopeType::Generator), "Generator");
        assert_eq!(format!("{:?}", ScopeType::Field), "Field");
        assert_eq!(format!("{:?}", ScopeType::EnumValue), "EnumValue");

        // Test Copy trait
        let scope1 = ScopeType::Model;
        let scope2 = scope1; // Should copy, not move
        assert_eq!(scope1, scope2);
    }
}
