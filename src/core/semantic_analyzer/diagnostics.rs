//! Diagnostic system for semantic analysis.
//!
//! This module provides a rich diagnostic system with error codes, severity levels,
//! suggestions, fix hints, and related span tracking for comprehensive error reporting.

use crate::core::scanner::tokens::SymbolSpan;
use std::collections::HashMap;

/// A diagnostic message from semantic analysis.
#[derive(Debug, Clone)]
pub struct SemanticDiagnostic {
    /// Severity level of this diagnostic
    pub severity: DiagnosticSeverity,

    /// Source location where this diagnostic applies
    pub span: SymbolSpan,

    /// Human-readable diagnostic message
    pub message: String,

    /// Structured diagnostic code for programmatic handling
    pub diagnostic_code: DiagnosticCode,

    /// Optional suggestion for fixing the issue
    pub suggestion: Option<String>,

    /// Optional fix hint with specific replacements
    pub fix_hint: Option<FixHint>,

    /// Related spans that provide additional context
    pub related_spans: Vec<RelatedSpan>,

    /// Additional metadata about this diagnostic
    pub metadata: DiagnosticMetadata,
}

impl SemanticDiagnostic {
    /// Create a new error diagnostic.
    #[must_use]
    pub fn error(
        span: SymbolSpan,
        message: String,
        code: DiagnosticCode,
    ) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            span,
            message,
            diagnostic_code: code,
            suggestion: None,
            fix_hint: None,
            related_spans: Vec::new(),
            metadata: DiagnosticMetadata::default(),
        }
    }

    /// Create a new warning diagnostic.
    #[must_use]
    pub fn warning(
        span: SymbolSpan,
        message: String,
        code: DiagnosticCode,
    ) -> Self {
        Self {
            severity: DiagnosticSeverity::Warning,
            span,
            message,
            diagnostic_code: code,
            suggestion: None,
            fix_hint: None,
            related_spans: Vec::new(),
            metadata: DiagnosticMetadata::default(),
        }
    }

    /// Create a new info diagnostic.
    #[must_use]
    pub fn info(
        span: SymbolSpan,
        message: String,
        code: DiagnosticCode,
    ) -> Self {
        Self {
            severity: DiagnosticSeverity::Info,
            span,
            message,
            diagnostic_code: code,
            suggestion: None,
            fix_hint: None,
            related_spans: Vec::new(),
            metadata: DiagnosticMetadata::default(),
        }
    }

    /// Add a suggestion to this diagnostic.
    #[must_use]
    pub fn with_suggestion(mut self, suggestion: String) -> Self {
        self.suggestion = Some(suggestion);
        self
    }

    /// Add a fix hint to this diagnostic.
    #[must_use]
    pub fn with_fix_hint(mut self, fix_hint: FixHint) -> Self {
        self.fix_hint = Some(fix_hint);
        self
    }

    /// Add a related span to this diagnostic.
    #[must_use]
    pub fn with_related_span(
        mut self,
        span: SymbolSpan,
        message: String,
    ) -> Self {
        self.related_spans.push(RelatedSpan { span, message });
        self
    }

    /// Add multiple related spans to this diagnostic.
    #[must_use]
    pub fn with_related_spans(mut self, spans: Vec<RelatedSpan>) -> Self {
        self.related_spans.extend(spans);
        self
    }

    /// Add metadata to this diagnostic.
    #[must_use]
    pub fn with_metadata(mut self, key: String, value: String) -> Self {
        self.metadata.add(key, value);
        self
    }

    /// Check if this is an error diagnostic.
    #[must_use]
    pub fn is_error(&self) -> bool {
        matches!(self.severity, DiagnosticSeverity::Error)
    }

    /// Check if this is a warning diagnostic.
    #[must_use]
    pub fn is_warning(&self) -> bool {
        matches!(self.severity, DiagnosticSeverity::Warning)
    }

    /// Check if this is an info diagnostic.
    #[must_use]
    pub fn is_info(&self) -> bool {
        matches!(self.severity, DiagnosticSeverity::Info)
    }

    /// Check if this is a fatal error that should stop analysis.
    #[must_use]
    pub fn is_fatal(&self) -> bool {
        self.is_error()
            && matches!(
                self.diagnostic_code,
                DiagnosticCode::CircularDependency
                    | DiagnosticCode::InvalidSchemaStructure
                    | DiagnosticCode::InternalError
            )
    }
}

/// Severity levels for diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DiagnosticSeverity {
    /// Informational messages
    Info,
    /// Warning messages that don't prevent schema use
    Warning,
    /// Error messages that prevent schema use
    Error,
}

impl std::fmt::Display for DiagnosticSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DiagnosticSeverity::Info => write!(f, "info"),
            DiagnosticSeverity::Warning => write!(f, "warning"),
            DiagnosticSeverity::Error => write!(f, "error"),
        }
    }
}

/// Structured diagnostic codes for programmatic handling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DiagnosticCode {
    // Symbol Resolution Errors
    UndeclaredIdentifier,
    DuplicateDeclaration,
    InvalidShadowing,
    ReservedWordUsed,

    // Type System Errors
    TypeMismatch,
    UnknownType,
    CircularDependency,
    InvalidTypeModifier,
    InvalidTypeUsage,
    TypeConstraintViolation,
    ConstraintViolation,
    IncompatibleTypes,

    // Relationship Errors
    InvalidRelation,
    MissingBackReference,
    ConflictingRelations,
    InvalidReferentialAction,
    RelationshipCycle,

    // Attribute Errors
    UnknownAttribute,
    MissingRequiredAttribute,
    ConflictingAttributes,
    InvalidAttributeArgument,
    AttributeNotApplicable,

    // Business Rule Violations
    MissingPrimaryKey,
    InvalidIndexDefinition,
    DatabaseProviderMismatch,
    DeprecatedFeature,

    // Performance Warnings
    PerformanceWarning,
    IndexSuggestion,
    QueryOptimizationHint,

    // Schema Structure Issues
    InvalidSchemaStructure,
    EmptyModel,
    UnusedDeclaration,
    MissingField,
    MissingDatasource,

    // Naming and Convention Issues
    InvalidIdentifier,
    ReservedKeyword,
    NamingConvention,
    ExperimentalFeature,

    // Internal Errors
    InternalError,
    AnalysisTimeout,
}

impl DiagnosticCode {
    /// Get the string representation of this diagnostic code.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            DiagnosticCode::UndeclaredIdentifier => "E001",
            DiagnosticCode::DuplicateDeclaration => "E002",
            DiagnosticCode::InvalidShadowing => "E003",
            DiagnosticCode::ReservedWordUsed => "E004",
            DiagnosticCode::TypeMismatch => "E101",
            DiagnosticCode::UnknownType => "E102",
            DiagnosticCode::CircularDependency => "E103",
            DiagnosticCode::InvalidTypeModifier => "E104",
            DiagnosticCode::InvalidTypeUsage => "E105",
            DiagnosticCode::TypeConstraintViolation => "E106",
            DiagnosticCode::ConstraintViolation => "E107",
            DiagnosticCode::IncompatibleTypes => "E108",
            DiagnosticCode::InvalidRelation => "E201",
            DiagnosticCode::MissingBackReference => "E202",
            DiagnosticCode::ConflictingRelations => "E203",
            DiagnosticCode::InvalidReferentialAction => "E204",
            DiagnosticCode::RelationshipCycle => "E205",
            DiagnosticCode::UnknownAttribute => "E301",
            DiagnosticCode::MissingRequiredAttribute => "E302",
            DiagnosticCode::ConflictingAttributes => "E303",
            DiagnosticCode::InvalidAttributeArgument => "E304",
            DiagnosticCode::AttributeNotApplicable => "E305",
            DiagnosticCode::MissingPrimaryKey => "E401",
            DiagnosticCode::InvalidIndexDefinition => "E402",
            DiagnosticCode::DatabaseProviderMismatch => "E403",
            DiagnosticCode::DeprecatedFeature => "W001",
            DiagnosticCode::PerformanceWarning => "W101",
            DiagnosticCode::IndexSuggestion => "W102",
            DiagnosticCode::QueryOptimizationHint => "W103",
            DiagnosticCode::InvalidSchemaStructure => "E501",
            DiagnosticCode::EmptyModel => "W201",
            DiagnosticCode::UnusedDeclaration => "W202",
            DiagnosticCode::MissingField => "E504",
            DiagnosticCode::MissingDatasource => "W505",
            DiagnosticCode::InvalidIdentifier => "E601",
            DiagnosticCode::ReservedKeyword => "E602",
            DiagnosticCode::NamingConvention => "W603",
            DiagnosticCode::ExperimentalFeature => "W604",
            DiagnosticCode::InternalError => "E999",
            DiagnosticCode::AnalysisTimeout => "E998",
        }
    }

    /// Get the category of this diagnostic code.
    #[must_use]
    pub fn category(self) -> DiagnosticCategory {
        match self {
            DiagnosticCode::UndeclaredIdentifier
            | DiagnosticCode::DuplicateDeclaration
            | DiagnosticCode::InvalidShadowing
            | DiagnosticCode::ReservedWordUsed
            | DiagnosticCode::InvalidIdentifier
            | DiagnosticCode::ReservedKeyword
            | DiagnosticCode::NamingConvention
            | DiagnosticCode::ExperimentalFeature => {
                DiagnosticCategory::SymbolResolution
            }

            DiagnosticCode::TypeMismatch
            | DiagnosticCode::UnknownType
            | DiagnosticCode::CircularDependency
            | DiagnosticCode::InvalidTypeModifier
            | DiagnosticCode::InvalidTypeUsage
            | DiagnosticCode::TypeConstraintViolation
            | DiagnosticCode::ConstraintViolation
            | DiagnosticCode::IncompatibleTypes => {
                DiagnosticCategory::TypeSystem
            }

            DiagnosticCode::InvalidRelation
            | DiagnosticCode::MissingBackReference
            | DiagnosticCode::ConflictingRelations
            | DiagnosticCode::InvalidReferentialAction
            | DiagnosticCode::RelationshipCycle => {
                DiagnosticCategory::Relationships
            }

            DiagnosticCode::UnknownAttribute
            | DiagnosticCode::MissingRequiredAttribute
            | DiagnosticCode::ConflictingAttributes
            | DiagnosticCode::InvalidAttributeArgument
            | DiagnosticCode::AttributeNotApplicable => {
                DiagnosticCategory::Attributes
            }

            DiagnosticCode::MissingPrimaryKey
            | DiagnosticCode::InvalidIndexDefinition
            | DiagnosticCode::DatabaseProviderMismatch
            | DiagnosticCode::DeprecatedFeature => {
                DiagnosticCategory::BusinessRules
            }

            DiagnosticCode::PerformanceWarning
            | DiagnosticCode::IndexSuggestion
            | DiagnosticCode::QueryOptimizationHint => {
                DiagnosticCategory::Performance
            }

            DiagnosticCode::InvalidSchemaStructure
            | DiagnosticCode::EmptyModel
            | DiagnosticCode::UnusedDeclaration
            | DiagnosticCode::MissingField
            | DiagnosticCode::MissingDatasource => {
                DiagnosticCategory::SchemaStructure
            }

            DiagnosticCode::InternalError | DiagnosticCode::AnalysisTimeout => {
                DiagnosticCategory::Internal
            }
        }
    }

    /// Get the default severity for this diagnostic code.
    #[must_use]
    pub fn default_severity(self) -> DiagnosticSeverity {
        match self {
            DiagnosticCode::DeprecatedFeature
            | DiagnosticCode::PerformanceWarning
            | DiagnosticCode::IndexSuggestion
            | DiagnosticCode::QueryOptimizationHint
            | DiagnosticCode::EmptyModel
            | DiagnosticCode::UnusedDeclaration => DiagnosticSeverity::Warning,
            _ => DiagnosticSeverity::Error,
        }
    }
}

/// Categories of diagnostic codes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticCategory {
    SymbolResolution,
    TypeSystem,
    Relationships,
    Attributes,
    BusinessRules,
    Performance,
    SchemaStructure,
    Internal,
}

/// Fix hint with specific text replacements.
#[derive(Debug, Clone)]
pub struct FixHint {
    /// Description of what this fix does
    pub description: String,

    /// Specific text replacements to apply
    pub replacements: Vec<TextReplacement>,

    /// Whether this fix is safe to apply automatically
    pub is_safe_auto_fix: bool,
}

impl FixHint {
    /// Create a new fix hint.
    #[must_use]
    pub fn new(description: String) -> Self {
        Self {
            description,
            replacements: Vec::new(),
            is_safe_auto_fix: false,
        }
    }

    /// Add a text replacement to this fix hint.
    #[must_use]
    pub fn with_replacement(mut self, replacement: TextReplacement) -> Self {
        self.replacements.push(replacement);
        self
    }

    /// Mark this fix as safe for automatic application.
    #[must_use]
    pub fn as_safe_auto_fix(mut self) -> Self {
        self.is_safe_auto_fix = true;
        self
    }
}

/// A specific text replacement for a fix hint.
#[derive(Debug, Clone)]
pub struct TextReplacement {
    /// Span to replace
    pub span: SymbolSpan,

    /// New text to insert
    pub new_text: String,
}

/// Related span that provides additional context to a diagnostic.
#[derive(Debug, Clone)]
pub struct RelatedSpan {
    /// The related span
    pub span: SymbolSpan,

    /// Message explaining the relevance of this span
    pub message: String,
}

/// Additional metadata for diagnostics.
#[derive(Debug, Clone)]
pub struct DiagnosticMetadata {
    /// Key-value pairs of additional information
    data: HashMap<String, String>,
}

impl DiagnosticMetadata {
    #[must_use]
    pub fn new() -> Self {
        Self {
            data: HashMap::new(),
        }
    }

    pub fn add(&mut self, key: String, value: String) {
        self.data.insert(key, value);
    }

    #[must_use]
    pub fn get(&self, key: &str) -> Option<&str> {
        self.data.get(key).map(std::string::String::as_str)
    }

    #[must_use]
    pub fn contains_key(&self, key: &str) -> bool {
        self.data.contains_key(key)
    }

    pub fn keys(&self) -> impl Iterator<Item = &String> {
        self.data.keys()
    }

    pub fn values(&self) -> impl Iterator<Item = &String> {
        self.data.values()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&String, &String)> {
        self.data.iter()
    }
}

impl Default for DiagnosticMetadata {
    fn default() -> Self {
        Self::new()
    }
}

/// Collector for diagnostics from multiple sources.
#[derive(Debug, Clone)]
pub struct DiagnosticCollector {
    diagnostics: Vec<SemanticDiagnostic>,
    max_diagnostics: Option<usize>,
}

impl DiagnosticCollector {
    /// Create a new diagnostic collector.
    #[must_use]
    pub fn new() -> Self {
        Self {
            diagnostics: Vec::new(),
            max_diagnostics: None,
        }
    }

    /// Create a new diagnostic collector with a maximum capacity.
    #[must_use]
    pub fn with_limit(max_diagnostics: usize) -> Self {
        Self {
            diagnostics: Vec::new(),
            max_diagnostics: Some(max_diagnostics),
        }
    }

    /// Add a diagnostic to the collection.
    pub fn add(&mut self, diagnostic: SemanticDiagnostic) {
        if let Some(max) = self.max_diagnostics
            && self.diagnostics.len() >= max
        {
            return;
        }
        self.diagnostics.push(diagnostic);
    }

    /// Add multiple diagnostics to the collection.
    pub fn extend(&mut self, diagnostics: Vec<SemanticDiagnostic>) {
        for diagnostic in diagnostics {
            self.add(diagnostic);
        }
    }

    /// Get all diagnostics.
    #[must_use]
    pub fn all(&self) -> &[SemanticDiagnostic] {
        &self.diagnostics
    }

    /// Take all diagnostics, consuming the collector.
    #[must_use]
    pub fn take_all(self) -> Vec<SemanticDiagnostic> {
        self.diagnostics
    }

    /// Clear all diagnostics.
    pub fn clear(&mut self) {
        self.diagnostics.clear();
    }

    /// Get the number of diagnostics.
    #[must_use]
    pub fn len(&self) -> usize {
        self.diagnostics.len()
    }

    /// Check if the collector is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.diagnostics.is_empty()
    }

    /// Check if the collector has reached its limit.
    #[must_use]
    pub fn is_at_limit(&self) -> bool {
        self.max_diagnostics
            .is_some_and(|max| self.diagnostics.len() >= max)
    }

    /// Get diagnostics by severity.
    #[must_use]
    pub fn by_severity(
        &self,
        severity: DiagnosticSeverity,
    ) -> Vec<&SemanticDiagnostic> {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == severity)
            .collect()
    }

    /// Get diagnostics by category.
    #[must_use]
    pub fn by_category(
        &self,
        category: DiagnosticCategory,
    ) -> Vec<&SemanticDiagnostic> {
        self.diagnostics
            .iter()
            .filter(|d| d.diagnostic_code.category() == category)
            .collect()
    }

    /// Get diagnostic counts by severity.
    #[must_use]
    pub fn severity_counts(&self) -> DiagnosticCounts {
        let mut counts = DiagnosticCounts::default();
        for diagnostic in &self.diagnostics {
            match diagnostic.severity {
                DiagnosticSeverity::Error => counts.errors += 1,
                DiagnosticSeverity::Warning => counts.warnings += 1,
                DiagnosticSeverity::Info => counts.infos += 1,
            }
        }
        counts
    }
}

impl Default for DiagnosticCollector {
    fn default() -> Self {
        Self::new()
    }
}

/// Counts of diagnostics by severity.
#[derive(Debug, Clone, Default)]
pub struct DiagnosticCounts {
    pub errors: usize,
    pub warnings: usize,
    pub infos: usize,
}

impl DiagnosticCounts {
    #[must_use]
    pub fn total(&self) -> usize {
        self.errors + self.warnings + self.infos
    }

    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.errors > 0
    }

    #[must_use]
    pub fn has_warnings(&self) -> bool {
        self.warnings > 0
    }

    #[must_use]
    pub fn has_infos(&self) -> bool {
        self.infos > 0
    }
}

/// Common diagnostic factory methods.
impl SemanticDiagnostic {
    /// Create an "undeclared identifier" error.
    #[must_use]
    pub fn undeclared_identifier(span: SymbolSpan, name: &str) -> Self {
        Self::error(
            span,
            format!("Identifier '{name}' is not declared"),
            DiagnosticCode::UndeclaredIdentifier,
        )
        .with_suggestion(format!(
            "Check if '{name}' is spelled correctly and declared"
        ))
    }

    /// Create a "duplicate declaration" error.
    #[must_use]
    pub fn duplicate_declaration(
        span: SymbolSpan,
        name: &str,
        existing_span: SymbolSpan,
    ) -> Self {
        Self::error(
            span,
            format!("Duplicate declaration of '{name}'"),
            DiagnosticCode::DuplicateDeclaration,
        )
        .with_suggestion(format!(
            "Consider renaming one of the '{name}' declarations"
        ))
        .with_related_span(existing_span, "First declaration here".to_string())
    }

    /// Create an "unknown type" error.
    #[must_use]
    pub fn unknown_type(span: SymbolSpan, type_name: &str) -> Self {
        Self::error(
            span,
            format!("Unknown type '{type_name}'"),
            DiagnosticCode::UnknownType,
        )
        .with_suggestion(
            "Check if the type name is spelled correctly and declared"
                .to_string(),
        )
    }

    /// Create a "circular dependency" error.
    #[must_use]
    pub fn circular_dependency(span: SymbolSpan, cycle: &[String]) -> Self {
        Self::error(
            span,
            format!("Circular dependency detected: {}", cycle.join(" -> ")),
            DiagnosticCode::CircularDependency,
        )
        .with_suggestion(
            "Break the cycle by using optional fields or forward declarations"
                .to_string(),
        )
    }

    /// Create a "missing primary key" error.
    #[must_use]
    pub fn missing_primary_key(span: SymbolSpan, model_name: &str) -> Self {
        let span_clone = span.clone();
        Self::error(
            span,
            format!("Model '{model_name}' must have a primary key"),
            DiagnosticCode::MissingPrimaryKey,
        ).with_suggestion("Add an @id attribute to one of the fields".to_string())
         .with_fix_hint(FixHint::new("Add id field".to_string())
            .with_replacement(TextReplacement {
                span: span_clone,
                new_text: format!("model {model_name} {{\n  id String @id\n  // other fields...\n}}"),
            }))
    }

    /// Create a "performance warning" diagnostic.
    #[must_use]
    pub fn performance_warning(
        span: SymbolSpan,
        message: String,
        suggestion: String,
    ) -> Self {
        Self::warning(span, message, DiagnosticCode::PerformanceWarning)
            .with_suggestion(suggestion)
    }

    /// Create a "deprecated feature" warning.
    #[must_use]
    pub fn deprecated_feature(
        span: SymbolSpan,
        feature: &str,
        replacement: Option<&str>,
    ) -> Self {
        let message = format!("Feature '{feature}' is deprecated");
        let suggestion = if let Some(replacement) = replacement {
            format!("Use '{replacement}' instead")
        } else {
            "Consider removing this deprecated feature".to_string()
        };

        Self::warning(span, message, DiagnosticCode::DeprecatedFeature)
            .with_suggestion(suggestion)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};

    fn test_span() -> SymbolSpan {
        SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        }
    }

    #[test]
    fn test_diagnostic_creation() {
        let diagnostic = SemanticDiagnostic::error(
            test_span(),
            "Test error message".to_string(),
            DiagnosticCode::UnknownType,
        );

        assert!(diagnostic.is_error());
        assert!(!diagnostic.is_warning());
        assert!(!diagnostic.is_info());
        assert_eq!(diagnostic.message, "Test error message");
        assert_eq!(diagnostic.diagnostic_code, DiagnosticCode::UnknownType);
    }

    #[test]
    fn test_diagnostic_with_suggestion() {
        let diagnostic = SemanticDiagnostic::error(
            test_span(),
            "Test error".to_string(),
            DiagnosticCode::UnknownType,
        )
        .with_suggestion("Try this fix".to_string());

        assert_eq!(diagnostic.suggestion, Some("Try this fix".to_string()));
    }

    #[test]
    fn test_diagnostic_with_fix_hint() {
        let fix_hint = FixHint::new("Add missing field".to_string())
            .with_replacement(TextReplacement {
                span: test_span(),
                new_text: "id String @id".to_string(),
            });

        let diagnostic = SemanticDiagnostic::error(
            test_span(),
            "Missing field".to_string(),
            DiagnosticCode::MissingPrimaryKey,
        )
        .with_fix_hint(fix_hint);

        assert!(diagnostic.fix_hint.is_some());
        let Some(hint) = diagnostic.fix_hint else {
            panic!("Should have fix hint")
        };
        assert_eq!(hint.description, "Add missing field");
        assert_eq!(hint.replacements.len(), 1);
    }

    #[test]
    fn test_diagnostic_code_properties() {
        assert_eq!(DiagnosticCode::UnknownType.as_str(), "E102");
        assert_eq!(
            DiagnosticCode::UnknownType.category(),
            DiagnosticCategory::TypeSystem
        );
        assert_eq!(
            DiagnosticCode::UnknownType.default_severity(),
            DiagnosticSeverity::Error
        );

        assert_eq!(
            DiagnosticCode::PerformanceWarning.default_severity(),
            DiagnosticSeverity::Warning
        );

        // Schema structure codes and severities
        assert_eq!(
            DiagnosticCode::MissingField.category(),
            DiagnosticCategory::SchemaStructure
        );
        assert_eq!(
            DiagnosticCode::MissingField.default_severity(),
            DiagnosticSeverity::Error
        );
    }

    #[test]
    fn test_diagnostic_severity_ordering() {
        assert!(DiagnosticSeverity::Info < DiagnosticSeverity::Warning);
        assert!(DiagnosticSeverity::Warning < DiagnosticSeverity::Error);
    }

    #[test]
    fn test_diagnostic_collector() {
        let mut collector = DiagnosticCollector::new();
        assert!(collector.is_empty());

        let diagnostic = SemanticDiagnostic::error(
            test_span(),
            "Test error".to_string(),
            DiagnosticCode::UnknownType,
        );

        collector.add(diagnostic);
        assert_eq!(collector.len(), 1);
        assert!(!collector.is_empty());

        let counts = collector.severity_counts();
        assert_eq!(counts.errors, 1);
        assert_eq!(counts.warnings, 0);
        assert_eq!(counts.total(), 1);
    }

    #[test]
    fn test_diagnostic_collector_with_limit() {
        let mut collector = DiagnosticCollector::with_limit(2);

        for i in 0..5 {
            collector.add(SemanticDiagnostic::error(
                test_span(),
                format!("Error {i}"),
                DiagnosticCode::UnknownType,
            ));
        }

        assert_eq!(collector.len(), 2);
        assert!(collector.is_at_limit());
    }

    #[test]
    fn test_diagnostic_factory_methods() {
        let diagnostic =
            SemanticDiagnostic::undeclared_identifier(test_span(), "MyType");
        assert!(diagnostic.is_error());
        assert_eq!(
            diagnostic.diagnostic_code,
            DiagnosticCode::UndeclaredIdentifier
        );
        assert!(diagnostic.suggestion.is_some());

        let diagnostic =
            SemanticDiagnostic::missing_primary_key(test_span(), "User");
        assert!(diagnostic.is_error());
        assert_eq!(
            diagnostic.diagnostic_code,
            DiagnosticCode::MissingPrimaryKey
        );
        assert!(diagnostic.suggestion.is_some());
        assert!(diagnostic.fix_hint.is_some());

        let diagnostic = SemanticDiagnostic::deprecated_feature(
            test_span(),
            "oldFeature",
            Some("newFeature"),
        );
        assert!(diagnostic.is_warning());
        assert_eq!(
            diagnostic.diagnostic_code,
            DiagnosticCode::DeprecatedFeature
        );
        assert!(diagnostic.suggestion.is_some());
    }

    #[test]
    fn test_diagnostic_metadata() {
        let mut metadata = DiagnosticMetadata::new();
        metadata.add("key1".to_string(), "value1".to_string());
        metadata.add("key2".to_string(), "value2".to_string());

        assert_eq!(metadata.get("key1"), Some("value1"));
        assert_eq!(metadata.get("key2"), Some("value2"));
        assert_eq!(metadata.get("nonexistent"), None);
        assert!(metadata.contains_key("key1"));
        assert!(!metadata.contains_key("nonexistent"));

        let keys: Vec<_> = metadata.keys().collect();
        assert_eq!(keys.len(), 2);
    }

    #[test]
    fn test_diagnostic_metadata_iterators() {
        let mut metadata = DiagnosticMetadata::new();
        metadata.add("key1".to_string(), "value1".to_string());
        metadata.add("key2".to_string(), "value2".to_string());

        let values: Vec<_> = metadata.values().collect();
        assert_eq!(values.len(), 2);
        assert!(values.contains(&&"value1".to_string()));
        assert!(values.contains(&&"value2".to_string()));

        let entries: Vec<_> = metadata.iter().collect();
        assert_eq!(entries.len(), 2);

        // Test default
        let default_metadata = DiagnosticMetadata::default();
        assert!(default_metadata.keys().next().is_none());
    }

    #[test]
    fn test_diagnostic_severity_display() {
        assert_eq!(format!("{}", DiagnosticSeverity::Info), "info");
        assert_eq!(format!("{}", DiagnosticSeverity::Warning), "warning");
        assert_eq!(format!("{}", DiagnosticSeverity::Error), "error");
    }

    #[test]
    fn test_diagnostic_fatal_detection() {
        let fatal_diagnostic = SemanticDiagnostic::error(
            test_span(),
            "Circular dependency".to_string(),
            DiagnosticCode::CircularDependency,
        );
        assert!(fatal_diagnostic.is_fatal());

        let structure_diagnostic = SemanticDiagnostic::error(
            test_span(),
            "Invalid schema".to_string(),
            DiagnosticCode::InvalidSchemaStructure,
        );
        assert!(structure_diagnostic.is_fatal());

        let internal_diagnostic = SemanticDiagnostic::error(
            test_span(),
            "Internal error".to_string(),
            DiagnosticCode::InternalError,
        );
        assert!(internal_diagnostic.is_fatal());

        let non_fatal_diagnostic = SemanticDiagnostic::error(
            test_span(),
            "Unknown type".to_string(),
            DiagnosticCode::UnknownType,
        );
        assert!(!non_fatal_diagnostic.is_fatal());

        let warning_diagnostic = SemanticDiagnostic::warning(
            test_span(),
            "Deprecated feature".to_string(),
            DiagnosticCode::DeprecatedFeature,
        );
        assert!(!warning_diagnostic.is_fatal());
    }

    #[test]
    fn test_diagnostic_builder_methods() {
        let diagnostic = SemanticDiagnostic::info(
            test_span(),
            "Info message".to_string(),
            DiagnosticCode::ExperimentalFeature,
        );
        assert!(diagnostic.is_info());
        assert!(!diagnostic.is_error());
        assert!(!diagnostic.is_warning());

        let warning_diagnostic = SemanticDiagnostic::warning(
            test_span(),
            "Warning message".to_string(),
            DiagnosticCode::PerformanceWarning,
        );
        assert!(warning_diagnostic.is_warning());
        assert!(!warning_diagnostic.is_error());
        assert!(!warning_diagnostic.is_info());
    }

    #[test]
    fn test_diagnostic_with_related_spans() {
        let related_span = RelatedSpan {
            span: test_span(),
            message: "Related location".to_string(),
        };

        let diagnostic = SemanticDiagnostic::error(
            test_span(),
            "Main error".to_string(),
            DiagnosticCode::DuplicateDeclaration,
        )
        .with_related_span(test_span(), "First declaration".to_string())
        .with_related_spans(vec![related_span]);

        assert_eq!(diagnostic.related_spans.len(), 2);
        assert_eq!(diagnostic.related_spans[0].message, "First declaration");
        assert_eq!(diagnostic.related_spans[1].message, "Related location");
    }

    #[test]
    fn test_diagnostic_with_metadata() {
        let diagnostic = SemanticDiagnostic::error(
            test_span(),
            "Error with metadata".to_string(),
            DiagnosticCode::TypeMismatch,
        )
        .with_metadata("expected_type".to_string(), "String".to_string())
        .with_metadata("actual_type".to_string(), "Int".to_string());

        assert_eq!(diagnostic.metadata.get("expected_type"), Some("String"));
        assert_eq!(diagnostic.metadata.get("actual_type"), Some("Int"));
    }

    #[test]
    fn test_fix_hint_builder() {
        let replacement1 = TextReplacement {
            span: test_span(),
            new_text: "replacement1".to_string(),
        };
        let replacement2 = TextReplacement {
            span: test_span(),
            new_text: "replacement2".to_string(),
        };

        let fix_hint = FixHint::new("Multi-replacement fix".to_string())
            .with_replacement(replacement1)
            .with_replacement(replacement2)
            .as_safe_auto_fix();

        assert_eq!(fix_hint.description, "Multi-replacement fix");
        assert_eq!(fix_hint.replacements.len(), 2);
        assert!(fix_hint.is_safe_auto_fix);
    }

    #[test]
    fn test_diagnostic_collector_filtering() {
        let mut collector = DiagnosticCollector::new();

        collector.add(SemanticDiagnostic::error(
            test_span(),
            "Error 1".to_string(),
            DiagnosticCode::UnknownType,
        ));
        collector.add(SemanticDiagnostic::warning(
            test_span(),
            "Warning 1".to_string(),
            DiagnosticCode::PerformanceWarning,
        ));
        collector.add(SemanticDiagnostic::info(
            test_span(),
            "Info 1".to_string(),
            DiagnosticCode::ExperimentalFeature,
        ));
        collector.add(SemanticDiagnostic::error(
            test_span(),
            "Error 2".to_string(),
            DiagnosticCode::InvalidRelation,
        ));

        let errors = collector.by_severity(DiagnosticSeverity::Error);
        assert_eq!(errors.len(), 2);

        let warnings = collector.by_severity(DiagnosticSeverity::Warning);
        assert_eq!(warnings.len(), 1);

        let infos = collector.by_severity(DiagnosticSeverity::Info);
        assert_eq!(infos.len(), 1);

        let type_system_diagnostics =
            collector.by_category(DiagnosticCategory::TypeSystem);
        assert_eq!(type_system_diagnostics.len(), 1);

        let relationship_diagnostics =
            collector.by_category(DiagnosticCategory::Relationships);
        assert_eq!(relationship_diagnostics.len(), 1);

        let performance_diagnostics =
            collector.by_category(DiagnosticCategory::Performance);
        assert_eq!(performance_diagnostics.len(), 1);
    }

    #[test]
    fn test_diagnostic_collector_clear_and_take() {
        let mut collector = DiagnosticCollector::new();
        collector.add(SemanticDiagnostic::error(
            test_span(),
            "Error".to_string(),
            DiagnosticCode::UnknownType,
        ));

        assert_eq!(collector.len(), 1);
        collector.clear();
        assert_eq!(collector.len(), 0);
        assert!(collector.is_empty());

        collector.add(SemanticDiagnostic::error(
            test_span(),
            "Error".to_string(),
            DiagnosticCode::UnknownType,
        ));

        let diagnostics = collector.take_all();
        assert_eq!(diagnostics.len(), 1);
    }

    #[test]
    fn test_diagnostic_collector_extend() {
        let mut collector = DiagnosticCollector::new();
        let diagnostics = vec![
            SemanticDiagnostic::error(
                test_span(),
                "Error 1".to_string(),
                DiagnosticCode::UnknownType,
            ),
            SemanticDiagnostic::warning(
                test_span(),
                "Warning 1".to_string(),
                DiagnosticCode::PerformanceWarning,
            ),
        ];

        collector.extend(diagnostics);
        assert_eq!(collector.len(), 2);

        let counts = collector.severity_counts();
        assert_eq!(counts.errors, 1);
        assert_eq!(counts.warnings, 1);
        assert_eq!(counts.infos, 0);
        assert_eq!(counts.total(), 2);
        assert!(counts.has_errors());
        assert!(counts.has_warnings());
        assert!(!counts.has_infos());
    }

    #[test]
    fn test_diagnostic_collector_limit_with_extend() {
        let mut collector = DiagnosticCollector::with_limit(1);
        let diagnostics = vec![
            SemanticDiagnostic::error(
                test_span(),
                "Error 1".to_string(),
                DiagnosticCode::UnknownType,
            ),
            SemanticDiagnostic::error(
                test_span(),
                "Error 2".to_string(),
                DiagnosticCode::UnknownType,
            ),
        ];

        collector.extend(diagnostics);
        assert_eq!(collector.len(), 1);
        assert!(collector.is_at_limit());
    }

    #[test]
    fn test_all_diagnostic_codes_as_str() {
        // Symbol Resolution
        assert_eq!(DiagnosticCode::UndeclaredIdentifier.as_str(), "E001");
        assert_eq!(DiagnosticCode::DuplicateDeclaration.as_str(), "E002");
        assert_eq!(DiagnosticCode::InvalidShadowing.as_str(), "E003");
        assert_eq!(DiagnosticCode::ReservedWordUsed.as_str(), "E004");

        // Type System
        assert_eq!(DiagnosticCode::TypeMismatch.as_str(), "E101");
        assert_eq!(DiagnosticCode::UnknownType.as_str(), "E102");
        assert_eq!(DiagnosticCode::CircularDependency.as_str(), "E103");
        assert_eq!(DiagnosticCode::InvalidTypeModifier.as_str(), "E104");
        assert_eq!(DiagnosticCode::InvalidTypeUsage.as_str(), "E105");
        assert_eq!(DiagnosticCode::TypeConstraintViolation.as_str(), "E106");
        assert_eq!(DiagnosticCode::ConstraintViolation.as_str(), "E107");
        assert_eq!(DiagnosticCode::IncompatibleTypes.as_str(), "E108");

        // Relationships
        assert_eq!(DiagnosticCode::InvalidRelation.as_str(), "E201");
        assert_eq!(DiagnosticCode::MissingBackReference.as_str(), "E202");
        assert_eq!(DiagnosticCode::ConflictingRelations.as_str(), "E203");
        assert_eq!(DiagnosticCode::InvalidReferentialAction.as_str(), "E204");
        assert_eq!(DiagnosticCode::RelationshipCycle.as_str(), "E205");

        // Attributes
        assert_eq!(DiagnosticCode::UnknownAttribute.as_str(), "E301");
        assert_eq!(DiagnosticCode::MissingRequiredAttribute.as_str(), "E302");
        assert_eq!(DiagnosticCode::ConflictingAttributes.as_str(), "E303");
        assert_eq!(DiagnosticCode::InvalidAttributeArgument.as_str(), "E304");
        assert_eq!(DiagnosticCode::AttributeNotApplicable.as_str(), "E305");

        // Business Rules
        assert_eq!(DiagnosticCode::MissingPrimaryKey.as_str(), "E401");
        assert_eq!(DiagnosticCode::InvalidIndexDefinition.as_str(), "E402");
        assert_eq!(DiagnosticCode::DatabaseProviderMismatch.as_str(), "E403");

        // Warnings
        assert_eq!(DiagnosticCode::DeprecatedFeature.as_str(), "W001");
        assert_eq!(DiagnosticCode::PerformanceWarning.as_str(), "W101");
        assert_eq!(DiagnosticCode::IndexSuggestion.as_str(), "W102");
        assert_eq!(DiagnosticCode::QueryOptimizationHint.as_str(), "W103");
        assert_eq!(DiagnosticCode::EmptyModel.as_str(), "W201");
        assert_eq!(DiagnosticCode::UnusedDeclaration.as_str(), "W202");
        assert_eq!(DiagnosticCode::NamingConvention.as_str(), "W603");
        assert_eq!(DiagnosticCode::ExperimentalFeature.as_str(), "W604");

        // Schema Structure
        assert_eq!(DiagnosticCode::InvalidSchemaStructure.as_str(), "E501");
        assert_eq!(DiagnosticCode::MissingField.as_str(), "E504");
        assert_eq!(DiagnosticCode::MissingDatasource.as_str(), "W505");

        // Naming
        assert_eq!(DiagnosticCode::InvalidIdentifier.as_str(), "E601");
        assert_eq!(DiagnosticCode::ReservedKeyword.as_str(), "E602");

        // Internal
        assert_eq!(DiagnosticCode::InternalError.as_str(), "E999");
        assert_eq!(DiagnosticCode::AnalysisTimeout.as_str(), "E998");
    }

    #[test]
    fn test_all_diagnostic_codes_category() {
        // Symbol Resolution category
        assert_eq!(
            DiagnosticCode::UndeclaredIdentifier.category(),
            DiagnosticCategory::SymbolResolution
        );
        assert_eq!(
            DiagnosticCode::DuplicateDeclaration.category(),
            DiagnosticCategory::SymbolResolution
        );
        assert_eq!(
            DiagnosticCode::InvalidShadowing.category(),
            DiagnosticCategory::SymbolResolution
        );
        assert_eq!(
            DiagnosticCode::ReservedWordUsed.category(),
            DiagnosticCategory::SymbolResolution
        );
        assert_eq!(
            DiagnosticCode::InvalidIdentifier.category(),
            DiagnosticCategory::SymbolResolution
        );
        assert_eq!(
            DiagnosticCode::ReservedKeyword.category(),
            DiagnosticCategory::SymbolResolution
        );
        assert_eq!(
            DiagnosticCode::NamingConvention.category(),
            DiagnosticCategory::SymbolResolution
        );
        assert_eq!(
            DiagnosticCode::ExperimentalFeature.category(),
            DiagnosticCategory::SymbolResolution
        );

        // Type System category
        assert_eq!(
            DiagnosticCode::TypeMismatch.category(),
            DiagnosticCategory::TypeSystem
        );
        assert_eq!(
            DiagnosticCode::UnknownType.category(),
            DiagnosticCategory::TypeSystem
        );
        assert_eq!(
            DiagnosticCode::CircularDependency.category(),
            DiagnosticCategory::TypeSystem
        );
        assert_eq!(
            DiagnosticCode::InvalidTypeModifier.category(),
            DiagnosticCategory::TypeSystem
        );
        assert_eq!(
            DiagnosticCode::InvalidTypeUsage.category(),
            DiagnosticCategory::TypeSystem
        );
        assert_eq!(
            DiagnosticCode::TypeConstraintViolation.category(),
            DiagnosticCategory::TypeSystem
        );
        assert_eq!(
            DiagnosticCode::ConstraintViolation.category(),
            DiagnosticCategory::TypeSystem
        );
        assert_eq!(
            DiagnosticCode::IncompatibleTypes.category(),
            DiagnosticCategory::TypeSystem
        );

        // Relationships category
        assert_eq!(
            DiagnosticCode::InvalidRelation.category(),
            DiagnosticCategory::Relationships
        );
        assert_eq!(
            DiagnosticCode::MissingBackReference.category(),
            DiagnosticCategory::Relationships
        );
        assert_eq!(
            DiagnosticCode::ConflictingRelations.category(),
            DiagnosticCategory::Relationships
        );
        assert_eq!(
            DiagnosticCode::InvalidReferentialAction.category(),
            DiagnosticCategory::Relationships
        );
        assert_eq!(
            DiagnosticCode::RelationshipCycle.category(),
            DiagnosticCategory::Relationships
        );

        // Attributes category
        assert_eq!(
            DiagnosticCode::UnknownAttribute.category(),
            DiagnosticCategory::Attributes
        );
        assert_eq!(
            DiagnosticCode::MissingRequiredAttribute.category(),
            DiagnosticCategory::Attributes
        );
        assert_eq!(
            DiagnosticCode::ConflictingAttributes.category(),
            DiagnosticCategory::Attributes
        );
        assert_eq!(
            DiagnosticCode::InvalidAttributeArgument.category(),
            DiagnosticCategory::Attributes
        );
        assert_eq!(
            DiagnosticCode::AttributeNotApplicable.category(),
            DiagnosticCategory::Attributes
        );

        // Business Rules category
        assert_eq!(
            DiagnosticCode::MissingPrimaryKey.category(),
            DiagnosticCategory::BusinessRules
        );
        assert_eq!(
            DiagnosticCode::InvalidIndexDefinition.category(),
            DiagnosticCategory::BusinessRules
        );
        assert_eq!(
            DiagnosticCode::DatabaseProviderMismatch.category(),
            DiagnosticCategory::BusinessRules
        );
        assert_eq!(
            DiagnosticCode::DeprecatedFeature.category(),
            DiagnosticCategory::BusinessRules
        );

        // Performance category
        assert_eq!(
            DiagnosticCode::PerformanceWarning.category(),
            DiagnosticCategory::Performance
        );
        assert_eq!(
            DiagnosticCode::IndexSuggestion.category(),
            DiagnosticCategory::Performance
        );
        assert_eq!(
            DiagnosticCode::QueryOptimizationHint.category(),
            DiagnosticCategory::Performance
        );

        // Schema Structure category
        assert_eq!(
            DiagnosticCode::InvalidSchemaStructure.category(),
            DiagnosticCategory::SchemaStructure
        );
        assert_eq!(
            DiagnosticCode::EmptyModel.category(),
            DiagnosticCategory::SchemaStructure
        );
        assert_eq!(
            DiagnosticCode::UnusedDeclaration.category(),
            DiagnosticCategory::SchemaStructure
        );
        assert_eq!(
            DiagnosticCode::MissingField.category(),
            DiagnosticCategory::SchemaStructure
        );
        assert_eq!(
            DiagnosticCode::MissingDatasource.category(),
            DiagnosticCategory::SchemaStructure
        );

        // Internal category
        assert_eq!(
            DiagnosticCode::InternalError.category(),
            DiagnosticCategory::Internal
        );
        assert_eq!(
            DiagnosticCode::AnalysisTimeout.category(),
            DiagnosticCategory::Internal
        );
    }

    #[test]
    fn test_all_diagnostic_codes_default_severity() {
        // Warning severities
        assert_eq!(
            DiagnosticCode::DeprecatedFeature.default_severity(),
            DiagnosticSeverity::Warning
        );
        assert_eq!(
            DiagnosticCode::PerformanceWarning.default_severity(),
            DiagnosticSeverity::Warning
        );
        assert_eq!(
            DiagnosticCode::IndexSuggestion.default_severity(),
            DiagnosticSeverity::Warning
        );
        assert_eq!(
            DiagnosticCode::QueryOptimizationHint.default_severity(),
            DiagnosticSeverity::Warning
        );
        assert_eq!(
            DiagnosticCode::EmptyModel.default_severity(),
            DiagnosticSeverity::Warning
        );
        assert_eq!(
            DiagnosticCode::UnusedDeclaration.default_severity(),
            DiagnosticSeverity::Warning
        );

        // Error severities (test a few representative ones)
        assert_eq!(
            DiagnosticCode::UndeclaredIdentifier.default_severity(),
            DiagnosticSeverity::Error
        );
        assert_eq!(
            DiagnosticCode::TypeMismatch.default_severity(),
            DiagnosticSeverity::Error
        );
        assert_eq!(
            DiagnosticCode::InvalidRelation.default_severity(),
            DiagnosticSeverity::Error
        );
        assert_eq!(
            DiagnosticCode::UnknownAttribute.default_severity(),
            DiagnosticSeverity::Error
        );
        assert_eq!(
            DiagnosticCode::MissingPrimaryKey.default_severity(),
            DiagnosticSeverity::Error
        );
        assert_eq!(
            DiagnosticCode::InternalError.default_severity(),
            DiagnosticSeverity::Error
        );
    }

    #[test]
    fn test_factory_method_unknown_type() {
        let diagnostic =
            SemanticDiagnostic::unknown_type(test_span(), "MyType");
        assert!(diagnostic.is_error());
        assert_eq!(diagnostic.diagnostic_code, DiagnosticCode::UnknownType);
        assert_eq!(diagnostic.message, "Unknown type 'MyType'");
        assert!(diagnostic.suggestion.is_some());
        assert_eq!(
            diagnostic.suggestion.unwrap(),
            "Check if the type name is spelled correctly and declared"
        );
    }

    #[test]
    fn test_factory_method_circular_dependency() {
        let cycle = vec!["A".to_string(), "B".to_string(), "C".to_string()];
        let diagnostic =
            SemanticDiagnostic::circular_dependency(test_span(), &cycle);

        assert!(diagnostic.is_error());
        assert_eq!(
            diagnostic.diagnostic_code,
            DiagnosticCode::CircularDependency
        );
        assert_eq!(
            diagnostic.message,
            "Circular dependency detected: A -> B -> C"
        );
        assert!(diagnostic.suggestion.is_some());
        assert_eq!(
            diagnostic.suggestion.unwrap(),
            "Break the cycle by using optional fields or forward declarations"
        );
    }

    #[test]
    fn test_factory_method_duplicate_declaration() {
        let existing_span = SymbolSpan {
            start: SymbolLocation { line: 2, column: 1 },
            end: SymbolLocation {
                line: 2,
                column: 10,
            },
        };

        let diagnostic = SemanticDiagnostic::duplicate_declaration(
            test_span(),
            "MyModel",
            existing_span.clone(),
        );

        assert!(diagnostic.is_error());
        assert_eq!(
            diagnostic.diagnostic_code,
            DiagnosticCode::DuplicateDeclaration
        );
        assert_eq!(diagnostic.message, "Duplicate declaration of 'MyModel'");
        assert!(diagnostic.suggestion.is_some());
        assert_eq!(diagnostic.related_spans.len(), 1);
        assert_eq!(diagnostic.related_spans[0].span, existing_span);
        assert_eq!(
            diagnostic.related_spans[0].message,
            "First declaration here"
        );
    }

    #[test]
    fn test_factory_method_deprecated_feature_without_replacement() {
        let diagnostic = SemanticDiagnostic::deprecated_feature(
            test_span(),
            "oldFeature",
            None,
        );

        assert!(diagnostic.is_warning());
        assert_eq!(
            diagnostic.diagnostic_code,
            DiagnosticCode::DeprecatedFeature
        );
        assert_eq!(diagnostic.message, "Feature 'oldFeature' is deprecated");
        assert!(diagnostic.suggestion.is_some());
        assert_eq!(
            diagnostic.suggestion.unwrap(),
            "Consider removing this deprecated feature"
        );
    }

    #[test]
    fn test_factory_method_performance_warning() {
        let diagnostic = SemanticDiagnostic::performance_warning(
            test_span(),
            "Inefficient query detected".to_string(),
            "Add an index on the queried field".to_string(),
        );

        assert!(diagnostic.is_warning());
        assert_eq!(
            diagnostic.diagnostic_code,
            DiagnosticCode::PerformanceWarning
        );
        assert_eq!(diagnostic.message, "Inefficient query detected");
        assert!(diagnostic.suggestion.is_some());
        assert_eq!(
            diagnostic.suggestion.unwrap(),
            "Add an index on the queried field"
        );
    }

    #[test]
    fn test_diagnostic_counts_empty() {
        let counts = DiagnosticCounts::default();
        assert_eq!(counts.errors, 0);
        assert_eq!(counts.warnings, 0);
        assert_eq!(counts.infos, 0);
        assert_eq!(counts.total(), 0);
        assert!(!counts.has_errors());
        assert!(!counts.has_warnings());
        assert!(!counts.has_infos());
    }
}
