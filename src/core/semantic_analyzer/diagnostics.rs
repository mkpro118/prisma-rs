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
}
