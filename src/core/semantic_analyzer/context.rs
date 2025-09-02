//! Analysis context and result types.
//!
//! This module provides the shared state and result types used throughout
//! the semantic analysis pipeline.

use crate::core::semantic_analyzer::{
    AnalyzerOptions, diagnostics::SemanticDiagnostic,
    symbol_table::SymbolTable, type_resolver::TypeResolver,
};
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// Shared context for semantic analysis phases.
///
/// The analysis context provides shared state, utilities, and metadata
/// collection for all analyzers in the pipeline.
#[derive(Debug)]
pub struct AnalysisContext {
    options: AnalyzerOptions,

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

impl AnalysisContext {
    /// Create a new analysis context.
    #[must_use]
    pub fn new(options: &AnalyzerOptions) -> Self {
        Self {
            options: options.clone(),
            current_scope: ScopeStack::new(),
            metadata: AnalysisMetadata::new(),
            start_time: Instant::now(),
            current_model: None,
            current_field: None,
            current_enum: None,
            type_resolution_stack: Vec::new(),
        }
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
#[derive(Debug, Clone)]
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
    use crate::core::semantic_analyzer::AnalyzerOptions;

    #[test]
    fn test_analysis_context_creation() {
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new(&options);

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
}
