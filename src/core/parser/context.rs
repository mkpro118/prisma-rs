//! Maintain parser state and collect diagnostics.
//!
//! This module provides a concrete `ParserContext` implementation that holds
//! `ParserOptions`, accumulates `Diagnostic`s, and exposes helpers like
//! error/warning counts and error-limit checks. Parsers receive a mutable
//! context when they need to record diagnostics or inspect options such as
//! strict mode and experimental feature gates.
//!
//! The default context is lightweight and suitable for single-threaded
//! parsing. Callers can embed or wrap it for more advanced needs (e.g.,
//! cross-file aggregation) while keeping the `ParserContext` contract.
//!
//! ## Examples
//! Collect errors and check the limit.
//! ```
//! # use prisma_rs::core::parser::context::DefaultParserContext;
//! # use prisma_rs::core::parser::config::{ParserOptions, Diagnostic};
//! # use prisma_rs::core::parser::traits::ParserContext;
//! # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
//! let opts = ParserOptions {
//!     max_errors: 1,
//!     ..ParserOptions::default()
//! };
//! let mut cx = DefaultParserContext::new(opts);
//! let sp = SymbolSpan {
//!     start: SymbolLocation { line: 1, column: 1 },
//!     end: SymbolLocation { line: 1, column: 1 },
//! };
//! cx.add_diagnostic(Diagnostic::error(sp.clone(), "first"));
//! assert!(cx.error_limit_exceeded());
//! ```

use crate::core::parser::config::{
    Diagnostic, DiagnosticSeverity, FeatureSupport, ParserOptions,
};
use crate::core::parser::traits::ParserContext;

/// Default parser context with options and diagnostics.
///
/// Stores immutable `ParserOptions` and a vector of diagnostics gathered
/// during parsing. Provides convenience counters and management helpers.
#[derive(Debug)]
pub struct DefaultParserContext {
    /// Parser configuration options.
    options: ParserOptions,
    /// Collected diagnostics during parsing.
    diagnostics: Vec<Diagnostic>,
}

impl Default for DefaultParserContext {
    fn default() -> Self {
        Self::new(ParserOptions::default())
    }
}

impl DefaultParserContext {
    /// Create a new parser context with the given options.
    ///
    /// Use this when you want to override defaults (e.g., tighter error
    /// limits or disabling experimental features).
    #[must_use]
    pub fn new(options: ParserOptions) -> Self {
        Self {
            options,
            diagnostics: Vec::new(),
        }
    }

    /// Return the number of error diagnostics.
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == DiagnosticSeverity::Error)
            .count()
    }

    /// Return the number of warning diagnostics.
    #[must_use]
    pub fn warning_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == DiagnosticSeverity::Warning)
            .count()
    }

    /// Clear all diagnostics.
    pub fn clear_diagnostics(&mut self) {
        self.diagnostics.clear();
    }

    /// Take all diagnostics, leaving this context empty.
    ///
    /// Useful when callers want to transfer ownership of messages to a
    /// higher-level accumulator or reporting layer.
    pub fn take_diagnostics(&mut self) -> Vec<Diagnostic> {
        std::mem::take(&mut self.diagnostics)
    }
}

impl ParserContext for DefaultParserContext {
    fn options(&self) -> &ParserOptions {
        &self.options
    }

    fn add_diagnostic(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }

    fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    fn error_limit_exceeded(&self) -> bool {
        self.error_count() >= self.options.max_errors
    }

    fn experimental_enabled(&self) -> bool {
        self.options.feature_support == FeatureSupport::WithExperimental
    }
}

#[cfg(test)]
mod context_tests {
    use super::*;
    use crate::core::parser::config::ParsingMode;
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
    fn default_parser_context_creation() {
        let context = DefaultParserContext::default();

        assert_eq!(context.options().parsing_mode, ParsingMode::Lenient);
        assert_eq!(
            context.options().feature_support,
            FeatureSupport::WithExperimental
        );
        assert!(context.options().error_recovery);
        assert_eq!(context.options().max_errors, 100);
        assert_eq!(context.diagnostics().len(), 0);
        assert_eq!(context.error_count(), 0);
        assert_eq!(context.warning_count(), 0);
    }

    #[test]
    fn parser_context_with_custom_options() {
        let options = ParserOptions {
            max_errors: 50,
            parsing_mode: ParsingMode::Strict,
            feature_support: FeatureSupport::StableOnly,
            error_recovery: false,
            ..Default::default()
        };

        let context = DefaultParserContext::new(options);

        assert_eq!(context.options().parsing_mode, ParsingMode::Strict);
        assert_eq!(
            context.options().feature_support,
            FeatureSupport::StableOnly
        );
        assert!(!context.options().error_recovery);
        assert_eq!(context.options().max_errors, 50);
        assert!(!context.experimental_enabled());
    }

    #[test]
    fn diagnostic_collection() {
        let mut context = DefaultParserContext::default();
        let span = test_span();

        // Add various types of diagnostics
        context.add_diagnostic(Diagnostic::error(span.clone(), "Error 1"));
        context.add_diagnostic(Diagnostic::warning(span.clone(), "Warning 1"));
        context.add_diagnostic(Diagnostic::error(span.clone(), "Error 2"));
        context.add_diagnostic(Diagnostic {
            severity: DiagnosticSeverity::Info,
            span: span.clone(),
            message: "Info 1".to_string(),
            suggestion: None,
        });

        assert_eq!(context.diagnostics().len(), 4);
        assert_eq!(context.error_count(), 2);
        assert_eq!(context.warning_count(), 1);

        // Check specific diagnostic content
        assert_eq!(context.diagnostics()[0].message, "Error 1");
        assert_eq!(context.diagnostics()[1].message, "Warning 1");
        assert_eq!(context.diagnostics()[2].message, "Error 2");
        assert_eq!(context.diagnostics()[3].message, "Info 1");
    }

    #[test]
    fn error_limit_checking() {
        let options = ParserOptions {
            max_errors: 2,
            parsing_mode: ParsingMode::Lenient,
            feature_support: FeatureSupport::WithExperimental,
            error_recovery: true,
            ..Default::default()
        };

        let mut context = DefaultParserContext::new(options);
        let span = test_span();

        // Should not exceed limit initially
        assert!(!context.error_limit_exceeded());

        // Add first error
        context.add_diagnostic(Diagnostic::error(span.clone(), "Error 1"));
        assert!(!context.error_limit_exceeded());

        // Add second error - should reach limit
        context.add_diagnostic(Diagnostic::error(span.clone(), "Error 2"));
        assert!(context.error_limit_exceeded());

        // Add warnings - shouldn't affect error limit
        context.add_diagnostic(Diagnostic::warning(span.clone(), "Warning"));
        assert_eq!(context.error_count(), 2);
        assert_eq!(context.warning_count(), 1);
        assert!(context.error_limit_exceeded());
    }

    #[test]
    fn diagnostic_management() {
        let mut context = DefaultParserContext::default();
        let span = test_span();

        // Add some diagnostics
        context.add_diagnostic(Diagnostic::error(span.clone(), "Error"));
        context.add_diagnostic(Diagnostic::warning(span.clone(), "Warning"));

        assert_eq!(context.diagnostics().len(), 2);
        assert_eq!(context.error_count(), 1);
        assert_eq!(context.warning_count(), 1);

        // Clear diagnostics
        context.clear_diagnostics();

        assert_eq!(context.diagnostics().len(), 0);
        assert_eq!(context.error_count(), 0);
        assert_eq!(context.warning_count(), 0);
        assert!(!context.error_limit_exceeded());
    }

    #[test]
    fn take_diagnostics() {
        let mut context = DefaultParserContext::default();
        let span = test_span();

        // Add some diagnostics
        context.add_diagnostic(Diagnostic::error(span.clone(), "Error"));
        context.add_diagnostic(Diagnostic::warning(span, "Warning"));

        assert_eq!(context.diagnostics().len(), 2);

        // Take diagnostics
        let taken = context.take_diagnostics();

        assert_eq!(taken.len(), 2);
        assert_eq!(taken[0].message, "Error");
        assert_eq!(taken[1].message, "Warning");

        // Context should now be empty
        assert_eq!(context.diagnostics().len(), 0);
        assert_eq!(context.error_count(), 0);
        assert_eq!(context.warning_count(), 0);
    }

    #[test]
    fn parser_context_trait_methods() {
        let mut context = DefaultParserContext::default();
        let span = test_span();

        // Test ParserContext trait methods
        assert_eq!(context.options().max_errors, 100);
        assert_eq!(context.diagnostics().len(), 0);
        assert!(!context.error_limit_exceeded());
        assert!(context.experimental_enabled());

        // Add diagnostic via trait method
        context.add_diagnostic(Diagnostic::error(span, "Trait method test"));

        assert_eq!(context.diagnostics().len(), 1);
        assert_eq!(context.error_count(), 1);
        assert!(!context.error_limit_exceeded()); // 1 < 100
    }
}
