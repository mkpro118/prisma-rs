//! Configure the parser and report diagnostics.
//!
//! This module defines the configuration knobs and result/diagnostic types
//! used by the parser. `ParserOptions` controls behavior like error limits
//! and experimental feature gates. `Diagnostic` carries structured messages
//! with spans. `ParseResult<T>` wraps a parsed value and any diagnostics,
//! and provides convenience helpers for success/error cases.
//!
//! Options are stable inputs; diagnostics and results are produced by parser
//! components and returned to callers. Callers can aggregate diagnostics
//! across stages (scanner, parser, type checker) using the same pattern.
//!
//! ## Examples
//! Create custom options and an error diagnostic.
//! ```
//! # use prisma_rs::core::parser::config::*;
//! # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
//! let opts = ParserOptions {
//!     max_errors: 10,
//!     parsing_mode: ParsingMode::Strict,
//!     feature_support: FeatureSupport::StableOnly,
//!     error_recovery: false,
//!     concurrency: ConcurrencyMode::Concurrent {
//!         max_threads: 2,
//!         threshold: 1,
//!     },
//!     ..Default::default()
//! };
//! assert_eq!(opts.parsing_mode, ParsingMode::Strict);
//! let span = SymbolSpan {
//!     start: SymbolLocation { line: 1, column: 1 },
//!     end: SymbolLocation { line: 1, column: 1 },
//! };
//! let diag = Diagnostic::error(span, "unexpected token");
//! assert_eq!(diag.severity, DiagnosticSeverity::Error);
//! ```

use crate::core::scanner::tokens::SymbolSpan;
use std::time::Duration;

/// Parsing mode configuration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParsingMode {
    /// Lenient parsing - recover from errors and allow ambiguities
    Lenient,
    /// Strict parsing - fail on any ambiguity or error
    Strict,
}

/// Feature support configuration  
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FeatureSupport {
    /// Only stable language features
    StableOnly,
    /// Include experimental language constructs
    WithExperimental,
}

/// Concurrency configuration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConcurrencyMode {
    /// Single-threaded parsing
    Sequential,
    /// Multi-threaded parsing with specified thread count and threshold
    Concurrent {
        max_threads: usize,
        threshold: usize,
    },
}

#[derive(Debug, Clone)]
pub struct ParserOptions {
    /// Maximum number of parse errors before aborting.
    pub max_errors: usize,
    /// Parsing mode (strict vs lenient)
    pub parsing_mode: ParsingMode,
    /// Feature support level
    pub feature_support: FeatureSupport,
    /// Enable recovery from syntax errors.
    pub error_recovery: bool,
    /// Concurrency configuration
    pub concurrency: ConcurrencyMode,
    /// Maximum time allowed for a single parser operation (progress supervision)
    pub max_parse_time: Duration,
    /// How often to check for parser progress
    pub progress_check_interval: Duration,
    /// Threshold for considering a parser stalled (currently informational)
    pub stall_threshold: Duration,
    /// Whether to enable progress validation
    pub enable_progress_validation: bool,
    /// Report every N token advances
    pub report_interval: usize,
}

impl Default for ParserOptions {
    fn default() -> Self {
        Self {
            max_errors: 100,
            parsing_mode: ParsingMode::Lenient,
            feature_support: FeatureSupport::WithExperimental,
            error_recovery: true,
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 2,
            },
            max_parse_time: Duration::from_millis(300),
            progress_check_interval: Duration::from_millis(25),
            stall_threshold: Duration::from_millis(100),
            enable_progress_validation: true,
            report_interval: 16,
        }
    }
}

/// Severity levels for parser diagnostics.
///
/// Severity does not imply sort order; callers control presentation. Only
/// `Error` contributes to error limits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    /// Fatal error that prevents parsing.
    Error,
    /// Warning about potentially problematic code.
    Warning,
    /// Informational message.
    Info,
}

/// Structured diagnostic message tied to a span.
///
/// Diagnostics can optionally include a suggestion string. Spans should
/// point to the most specific range that explains the issue.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// Severity level of the diagnostic.
    pub severity: DiagnosticSeverity,
    /// Location in source where the diagnostic applies.
    pub span: SymbolSpan,
    /// Human-readable diagnostic message.
    pub message: String,
    /// Optional suggestion for fixing the issue.
    pub suggestion: Option<String>,
}

impl Diagnostic {
    /// Create a new error diagnostic.
    pub fn error<S: Into<String>>(span: SymbolSpan, message: S) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            span,
            message: message.into(),
            suggestion: None,
        }
    }

    /// Create a new warning diagnostic.
    pub fn warning<S: Into<String>>(span: SymbolSpan, message: S) -> Self {
        Self {
            severity: DiagnosticSeverity::Warning,
            span,
            message: message.into(),
            suggestion: None,
        }
    }

    /// Add a suggestion to this diagnostic.
    #[must_use]
    pub fn with_suggestion<S: Into<String>>(mut self, suggestion: S) -> Self {
        self.suggestion = Some(suggestion.into());
        self
    }
}

/// Result of a parse with value and diagnostics.
///
/// A successful result has `value: Some(T)` and may still contain warnings.
/// `has_errors()` checks for any error-severity diagnostics regardless of
/// success. `is_success()` returns true only when a value exists and there
/// are no errors.
///
/// ## Examples
/// Build success and error results.
/// ```
/// # use prisma_rs::core::parser::config::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// let ok = ParseResult::success(42);
/// assert!(ok.is_success());
/// let span = SymbolSpan {
///     start: SymbolLocation { line: 1, column: 1 },
///     end: SymbolLocation { line: 1, column: 1 },
/// };
/// let err = ParseResult::<()>::error(Diagnostic::error(span, "boom"));
/// assert!(!err.is_success());
/// assert!(err.has_errors());
/// ```
#[derive(Debug)]
pub struct ParseResult<T> {
    /// The successfully parsed value, if any.
    pub value: Option<T>,
    /// Diagnostics generated during parsing.
    pub diagnostics: Vec<Diagnostic>,
}

impl<T> ParseResult<T> {
    /// Create a successful parse result.
    pub fn success(value: T) -> Self {
        Self {
            value: Some(value),
            diagnostics: Vec::new(),
        }
    }

    /// Create a failed parse result with an error.
    #[must_use]
    pub fn error(diagnostic: Diagnostic) -> Self {
        Self {
            value: None,
            diagnostics: vec![diagnostic],
        }
    }

    /// Add a diagnostic to this result.
    #[must_use]
    pub fn with_diagnostic(mut self, diagnostic: Diagnostic) -> Self {
        self.diagnostics.push(diagnostic);
        self
    }

    /// Check if this result represents a successful parse.
    pub fn is_success(&self) -> bool {
        self.value.is_some() && !self.has_errors()
    }

    /// Check if this result contains any error diagnostics.
    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|d| d.severity == DiagnosticSeverity::Error)
    }
}

#[cfg(test)]
mod config_tests {
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
    fn parser_options_default() {
        let options = ParserOptions::default();

        assert_eq!(options.max_errors, 100);
        assert_eq!(options.parsing_mode, ParsingMode::Lenient);
        assert_eq!(options.feature_support, FeatureSupport::WithExperimental);
        assert!(options.error_recovery);
        assert!(matches!(
            options.concurrency,
            ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 2
            }
        ));
    }

    #[test]
    fn parser_options_custom() {
        let options = ParserOptions {
            max_errors: 50,
            parsing_mode: ParsingMode::Strict,
            feature_support: FeatureSupport::StableOnly,
            error_recovery: false,
            concurrency: ConcurrencyMode::Sequential,
            ..Default::default()
        };

        assert_eq!(options.max_errors, 50);
        assert_eq!(options.parsing_mode, ParsingMode::Strict);
        assert_eq!(options.feature_support, FeatureSupport::StableOnly);
        assert!(!options.error_recovery);
        assert!(matches!(options.concurrency, ConcurrencyMode::Sequential));
    }

    #[test]
    fn diagnostic_severity_equality() {
        assert_eq!(DiagnosticSeverity::Error, DiagnosticSeverity::Error);
        assert_eq!(DiagnosticSeverity::Warning, DiagnosticSeverity::Warning);
        assert_eq!(DiagnosticSeverity::Info, DiagnosticSeverity::Info);

        assert_ne!(DiagnosticSeverity::Error, DiagnosticSeverity::Warning);
        assert_ne!(DiagnosticSeverity::Warning, DiagnosticSeverity::Info);
        assert_ne!(DiagnosticSeverity::Error, DiagnosticSeverity::Info);
    }

    #[test]
    fn diagnostic_error_creation() {
        let span = test_span();
        let diagnostic = Diagnostic::error(span.clone(), "Test error message");

        assert_eq!(diagnostic.severity, DiagnosticSeverity::Error);
        assert_eq!(diagnostic.span, span);
        assert_eq!(diagnostic.message, "Test error message");
        assert!(diagnostic.suggestion.is_none());
    }

    #[test]
    fn diagnostic_warning_creation() {
        let span = test_span();
        let diagnostic =
            Diagnostic::warning(span.clone(), "Test warning message");

        assert_eq!(diagnostic.severity, DiagnosticSeverity::Warning);
        assert_eq!(diagnostic.span, span);
        assert_eq!(diagnostic.message, "Test warning message");
        assert!(diagnostic.suggestion.is_none());
    }

    #[test]
    fn diagnostic_with_suggestion() {
        let span = test_span();
        let diagnostic = Diagnostic::error(span.clone(), "Syntax error")
            .with_suggestion("Try adding a semicolon");

        assert_eq!(diagnostic.severity, DiagnosticSeverity::Error);
        assert_eq!(diagnostic.span, span);
        assert_eq!(diagnostic.message, "Syntax error");
        assert_eq!(
            diagnostic.suggestion,
            Some("Try adding a semicolon".to_string())
        );
    }

    #[test]
    fn diagnostic_string_conversion() {
        let span = test_span();

        // Test &str to String conversion
        let diagnostic1 = Diagnostic::error(span.clone(), "string slice");
        assert_eq!(diagnostic1.message, "string slice");

        // Test String to String conversion
        let diagnostic2 =
            Diagnostic::warning(span.clone(), "owned string".to_string());
        assert_eq!(diagnostic2.message, "owned string");

        // Test suggestion conversion
        let diagnostic3 = Diagnostic::error(span, "error")
            .with_suggestion("fix it".to_string());
        assert_eq!(diagnostic3.suggestion, Some("fix it".to_string()));
    }

    #[test]
    fn parse_result_success() {
        let result = ParseResult::success("test value");

        assert!(result.value.is_some());
        assert_eq!(result.value.unwrap(), "test value");
        assert!(result.diagnostics.is_empty());
        assert!(result.is_success());
        assert!(!result.has_errors());
    }

    #[test]
    fn parse_result_error() {
        let span = test_span();
        let diagnostic = Diagnostic::error(span, "Parse error");
        let result: ParseResult<String> =
            ParseResult::error(diagnostic.clone());

        assert!(result.value.is_none());
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].message, "Parse error");
        assert!(!result.is_success());
        assert!(result.has_errors());
    }

    #[test]
    fn parse_result_with_diagnostic() {
        let span = test_span();
        let warning = Diagnostic::warning(span.clone(), "Warning message");
        let error = Diagnostic::error(span, "Error message");

        let result = ParseResult::success("value")
            .with_diagnostic(warning)
            .with_diagnostic(error);

        assert!(result.value.is_some());
        assert_eq!(result.diagnostics.len(), 2);
        assert_eq!(result.diagnostics[0].severity, DiagnosticSeverity::Warning);
        assert_eq!(result.diagnostics[1].severity, DiagnosticSeverity::Error);
        assert!(!result.is_success()); // Should fail because it has errors
        assert!(result.has_errors());
    }

    #[test]
    fn parse_result_success_with_warnings() {
        let span = test_span();
        let warning = Diagnostic::warning(span, "Warning message");

        let result = ParseResult::success("value").with_diagnostic(warning);

        assert!(result.value.is_some());
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].severity, DiagnosticSeverity::Warning);
        assert!(result.is_success()); // Should succeed despite warnings
        assert!(!result.has_errors()); // No errors, just warnings
    }

    #[test]
    fn parse_result_mixed_diagnostics() {
        let span = test_span();
        let info = Diagnostic {
            severity: DiagnosticSeverity::Info,
            span: span.clone(),
            message: "Info message".to_string(),
            suggestion: None,
        };
        let warning = Diagnostic::warning(span.clone(), "Warning message");
        let error = Diagnostic::error(span, "Error message");

        let result = ParseResult::success("value")
            .with_diagnostic(info)
            .with_diagnostic(warning)
            .with_diagnostic(error);

        assert!(result.value.is_some());
        assert_eq!(result.diagnostics.len(), 3);
        assert!(!result.is_success());
        assert!(result.has_errors());

        // Check that has_errors only counts errors, not warnings or info
        let no_error_result = ParseResult::success("value")
            .with_diagnostic(Diagnostic {
                severity: DiagnosticSeverity::Info,
                span: test_span(),
                message: "Info".to_string(),
                suggestion: None,
            })
            .with_diagnostic(Diagnostic::warning(test_span(), "Warning"));

        assert!(!no_error_result.has_errors());
        assert!(no_error_result.is_success());
    }

    #[test]
    fn diagnostic_creation_patterns() {
        let span = test_span();

        // Test format! with error creation
        let formatted_diagnostic =
            Diagnostic::error(span.clone(), format!("Error #{}", 42));
        assert_eq!(formatted_diagnostic.message, "Error #42");

        // Test error with suggestion chain
        let chained_diagnostic =
            Diagnostic::warning(span.clone(), "Deprecated syntax")
                .with_suggestion("Use new syntax instead")
                .with_suggestion("Or consider alternative approach"); // Should overwrite previous

        assert_eq!(chained_diagnostic.severity, DiagnosticSeverity::Warning);
        assert_eq!(
            chained_diagnostic.suggestion,
            Some("Or consider alternative approach".to_string())
        );

        // Test manual diagnostic creation
        let manual_diagnostic = Diagnostic {
            severity: DiagnosticSeverity::Info,
            span,
            message: "Manual creation".to_string(),
            suggestion: Some("Manual suggestion".to_string()),
        };

        assert_eq!(manual_diagnostic.severity, DiagnosticSeverity::Info);
        assert_eq!(manual_diagnostic.message, "Manual creation");
        assert_eq!(
            manual_diagnostic.suggestion,
            Some("Manual suggestion".to_string())
        );
    }
}
