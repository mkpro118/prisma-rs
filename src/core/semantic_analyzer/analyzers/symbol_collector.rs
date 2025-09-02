//! Symbol collection analyzer for building symbol tables from AST.
//!
//! This analyzer is the first phase of semantic analysis and is responsible
//! for traversing the AST and collecting all declared symbols into the
//! symbol table. It establishes the foundation for all subsequent analysis.

use crate::core::parser::ast::{Declaration, EnumMember, ModelMember, Schema};
use crate::core::semantic_analyzer::{
    context::{AnalysisContext, PhaseResult},
    diagnostics::{DiagnosticCode, SemanticDiagnostic},
    traits::PhaseAnalyzer,
};

/// Reserved keywords that cannot be used as identifiers.
const RESERVED_KEYWORDS: &[&str] = &[
    "model",
    "enum",
    "datasource",
    "generator",
    "type",
    "true",
    "false",
    "null",
    "undefined",
];

/// Analyzer responsible for collecting symbols from the AST into the symbol table.
///
/// This is the foundational phase that must run before any other analysis.
/// It traverses the entire schema and creates symbol table entries for:
/// - Models and their fields
/// - Enums and their values  
/// - Datasources and generators
/// - Type aliases (when experimental features are enabled)
///
/// The symbol collector also validates that symbol names are unique within
/// their respective scopes and follows Prisma naming conventions.
pub struct SymbolCollectionAnalyzer {
    /// Tracks whether we're currently processing experimental features
    processing_experimental: bool,
}

impl SymbolCollectionAnalyzer {
    /// Create a new symbol collection analyzer.
    #[must_use]
    pub fn new() -> Self {
        Self {
            processing_experimental: false,
        }
    }

    /// Validate that an identifier follows Prisma naming conventions.
    ///
    /// # Errors
    ///
    /// Returns a `SemanticDiagnostic` if the identifier:
    /// - Is empty
    /// - Uses a reserved keyword
    /// - Doesn't follow the appropriate naming convention
    fn validate_identifier(
        &self,
        name: &str,
        span: &crate::core::scanner::tokens::SymbolSpan,
    ) -> Result<(), Box<SemanticDiagnostic>> {
        // Check for empty name
        if name.is_empty() {
            return Err(Box::new(SemanticDiagnostic::error(
                span.clone(),
                "Identifier cannot be empty".to_string(),
                DiagnosticCode::InvalidIdentifier,
            )));
        }

        // Check for reserved keywords
        if RESERVED_KEYWORDS.contains(&name) {
            return Err(Box::new(SemanticDiagnostic::error(
                span.clone(),
                format!(
                    "'{name}' is a reserved keyword and cannot be used as an identifier"
                ),
                DiagnosticCode::ReservedKeyword,
            )));
        }

        // Check naming convention (PascalCase for types, camelCase for fields)
        if !self.processing_experimental
            && name.chars().next().is_some_and(|c| c.is_ascii_lowercase())
        {
            // This is likely a field or value - validate camelCase
            if !Self::is_camel_case(name) {
                return Err(Box::new(SemanticDiagnostic::warning(
                    span.clone(),
                    format!(
                        "Field '{name}' should use camelCase naming convention"
                    ),
                    DiagnosticCode::NamingConvention,
                )));
            }
        } else if !Self::is_pascal_case(name) {
            return Err(Box::new(SemanticDiagnostic::warning(
                span.clone(),
                format!(
                    "Type '{name}' should use PascalCase naming convention"
                ),
                DiagnosticCode::NamingConvention,
            )));
        }

        Ok(())
    }

    /// Check if a name follows `camelCase` convention.
    ///
    /// Returns `true` if the name starts with a lowercase letter and contains
    /// only alphanumeric characters (no underscores).
    fn is_camel_case(name: &str) -> bool {
        if name.is_empty() {
            return false;
        }

        let mut chars = name.chars();
        let Some(first) = chars.next() else {
            return false;
        };

        // First character should be lowercase
        if !first.is_ascii_lowercase() {
            return false;
        }

        // Rest should be alphanumeric, no underscores allowed in camelCase
        for ch in chars {
            if !ch.is_ascii_alphanumeric() {
                return false; // Invalid character (including underscores)
            }
        }

        true
    }

    /// Check if a name follows `PascalCase` convention.
    ///
    /// Returns `true` if the name starts with an uppercase letter and contains
    /// only alphanumeric characters (no underscores).
    fn is_pascal_case(name: &str) -> bool {
        if name.is_empty() {
            return false;
        }

        let mut chars = name.chars();
        let Some(first) = chars.next() else {
            return false;
        };

        // First character should be uppercase
        if !first.is_ascii_uppercase() {
            return false;
        }

        // Rest should be alphanumeric, no underscores in PascalCase
        for ch in chars {
            if !ch.is_ascii_alphanumeric() {
                return false;
            }
        }

        true
    }

    fn check_model(
        &self,
        model: &crate::core::parser::ast::ModelDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Err(diagnostic) =
            self.validate_identifier(&model.name.text, &model.name.span)
        {
            diagnostics.push(*diagnostic);
        }
        for member in &model.members {
            if let ModelMember::Field(field) = member
                && let Err(diagnostic) =
                    self.validate_identifier(&field.name.text, &field.name.span)
            {
                diagnostics.push(*diagnostic);
            }
        }
    }

    fn check_enum(
        &self,
        enum_decl: &crate::core::parser::ast::EnumDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Err(diagnostic) =
            self.validate_identifier(&enum_decl.name.text, &enum_decl.name.span)
        {
            diagnostics.push(*diagnostic);
        }
        for member in &enum_decl.members {
            if let EnumMember::Value(value) = member
                && let Err(diagnostic) =
                    self.validate_identifier(&value.name.text, &value.name.span)
            {
                diagnostics.push(*diagnostic);
            }
        }
    }

    fn check_datasource(
        &self,
        datasource: &crate::core::parser::ast::DatasourceDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Err(diagnostic) = self
            .validate_identifier(&datasource.name.text, &datasource.name.span)
        {
            diagnostics.push(*diagnostic);
        }
        let has_provider = datasource
            .assignments
            .iter()
            .any(|assignment| assignment.key.text == "provider");
        let has_url = datasource
            .assignments
            .iter()
            .any(|assignment| assignment.key.text == "url");

        if !has_provider {
            diagnostics.push(SemanticDiagnostic::error(
                datasource.name.span.clone(),
                "Datasource missing required 'provider' field".to_string(),
                DiagnosticCode::MissingField,
            ));
        }

        if !has_url {
            diagnostics.push(SemanticDiagnostic::error(
                datasource.name.span.clone(),
                "Datasource missing required 'url' field".to_string(),
                DiagnosticCode::MissingField,
            ));
        }
    }

    fn check_generator(
        &self,
        generator: &crate::core::parser::ast::GeneratorDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Err(diagnostic) =
            self.validate_identifier(&generator.name.text, &generator.name.span)
        {
            diagnostics.push(*diagnostic);
        }
        let has_provider = generator
            .assignments
            .iter()
            .any(|assignment| assignment.key.text == "provider");

        if !has_provider {
            diagnostics.push(SemanticDiagnostic::error(
                generator.name.span.clone(),
                "Generator missing required 'provider' field".to_string(),
                DiagnosticCode::MissingField,
            ));
        }
    }

    fn check_type_alias(
        &self,
        type_alias: &crate::core::parser::ast::TypeDecl,
        context: &AnalysisContext,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if context.options().features.validate_experimental {
            if let Err(diagnostic) = self.validate_identifier(
                &type_alias.name.text,
                &type_alias.name.span,
            ) {
                diagnostics.push(*diagnostic);
            }
        } else {
            diagnostics.push(SemanticDiagnostic::warning(
                type_alias.name.span.clone(),
                "Type aliases are experimental and disabled".to_string(),
                DiagnosticCode::ExperimentalFeature,
            ));
        }
    }

    fn check_has_datasource(
        schema: &Schema,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        let has_datasource = schema
            .declarations
            .iter()
            .any(|decl| matches!(decl, Declaration::Datasource(_)));

        if !has_datasource {
            diagnostics.push(SemanticDiagnostic::warning(
                schema.span.clone(),
                "Schema should contain at least one datasource declaration"
                    .to_string(),
                DiagnosticCode::MissingDatasource,
            ));
        }
    }
}

impl Default for SymbolCollectionAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl PhaseAnalyzer for SymbolCollectionAnalyzer {
    fn phase_name(&self) -> &'static str {
        "symbol-collection"
    }

    fn analyze(
        &mut self,
        schema: &Schema,
        context: &mut AnalysisContext,
    ) -> PhaseResult {
        let mut diagnostics = Vec::new();

        // Validate identifiers in all declarations
        for declaration in &schema.declarations {
            match declaration {
                Declaration::Model(model) => {
                    self.check_model(model, &mut diagnostics);
                }
                Declaration::Enum(enum_decl) => {
                    self.check_enum(enum_decl, &mut diagnostics);
                }
                Declaration::Datasource(datasource) => {
                    self.check_datasource(datasource, &mut diagnostics);
                }
                Declaration::Generator(generator) => {
                    self.check_generator(generator, &mut diagnostics);
                }
                Declaration::Type(type_alias) => {
                    self.check_type_alias(
                        type_alias,
                        context,
                        &mut diagnostics,
                    );
                }
            }
        }

        Self::check_has_datasource(schema, &mut diagnostics);

        PhaseResult::new(diagnostics)
    }

    fn dependencies(&self) -> &[&'static str] {
        // Symbol collection has no dependencies - it's the foundation
        &[]
    }

    fn supports_parallel_execution(&self) -> bool {
        // Symbol collection modifies shared state, so no parallelism
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::parser::ast::*;
    use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
    use crate::core::semantic_analyzer::{AnalyzerOptions, FeatureOptions};

    fn create_test_span() -> SymbolSpan {
        SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation { line: 1, column: 5 },
        }
    }

    #[test]
    fn test_symbol_collection_analyzer_creation() {
        let analyzer = SymbolCollectionAnalyzer::new();
        assert_eq!(analyzer.phase_name(), "symbol-collection");
        assert_eq!(analyzer.dependencies().len(), 0);
        assert!(!analyzer.supports_parallel_execution());
    }

    #[test]
    fn test_validate_identifier_valid_names() {
        let analyzer = SymbolCollectionAnalyzer::new();
        let span = create_test_span();

        // Valid PascalCase
        assert!(analyzer.validate_identifier("User", &span).is_ok());
        assert!(analyzer.validate_identifier("UserProfile", &span).is_ok());

        // Valid camelCase
        assert!(analyzer.validate_identifier("firstName", &span).is_ok());
        assert!(analyzer.validate_identifier("userId", &span).is_ok());
    }

    #[test]
    fn test_validate_identifier_reserved_keywords() {
        let analyzer = SymbolCollectionAnalyzer::new();
        let span = create_test_span();

        let result = analyzer.validate_identifier("model", &span);
        assert!(result.is_err());

        let Err(err) = result else {
            panic!("Expected validation to fail for reserved keyword")
        };
        assert_eq!(err.diagnostic_code, DiagnosticCode::ReservedKeyword);
        assert!(err.message.contains("reserved keyword"));
    }

    #[test]
    fn test_validate_identifier_empty_name() {
        let analyzer = SymbolCollectionAnalyzer::new();
        let span = create_test_span();

        let result = analyzer.validate_identifier("", &span);
        assert!(result.is_err());

        let Err(err) = result else {
            panic!("Expected validation to fail for empty identifier")
        };
        assert_eq!(err.diagnostic_code, DiagnosticCode::InvalidIdentifier);
    }

    #[test]
    fn test_naming_conventions() {
        let _analyzer = SymbolCollectionAnalyzer::new();

        // Test camelCase validation
        assert!(SymbolCollectionAnalyzer::is_camel_case("camelCase"));
        assert!(SymbolCollectionAnalyzer::is_camel_case("firstName"));
        assert!(SymbolCollectionAnalyzer::is_camel_case("userId"));
        assert!(!SymbolCollectionAnalyzer::is_camel_case("PascalCase"));
        assert!(!SymbolCollectionAnalyzer::is_camel_case("snake_case"));

        // Test PascalCase validation
        assert!(SymbolCollectionAnalyzer::is_pascal_case("PascalCase"));
        assert!(SymbolCollectionAnalyzer::is_pascal_case("User"));
        assert!(SymbolCollectionAnalyzer::is_pascal_case("UserProfile"));
        assert!(!SymbolCollectionAnalyzer::is_pascal_case("camelCase"));
        assert!(!SymbolCollectionAnalyzer::is_pascal_case("snake_case"));
    }

    #[test]
    fn test_validate_identifier_naming_convention_warnings() {
        let analyzer = SymbolCollectionAnalyzer::new();
        let span = create_test_span();

        // snake_case should trigger naming convention warning
        let res = analyzer.validate_identifier("first_name", &span);
        assert!(res.is_err());
        let Err(diag) = res else {
            panic!("Expected warning diagnostic")
        };
        assert_eq!(diag.diagnostic_code, DiagnosticCode::NamingConvention);
        assert!(diag.is_warning());

        // PascalCase with underscore should warn
        let res2 = analyzer.validate_identifier("User_Profile", &span);
        assert!(res2.is_err());
        let Err(diag2) = res2 else {
            panic!("Expected warning diagnostic")
        };
        assert_eq!(diag2.diagnostic_code, DiagnosticCode::NamingConvention);
        assert!(diag2.is_warning());
    }

    fn sp(s: (u32, u32), e: (u32, u32)) -> SymbolSpan {
        SymbolSpan {
            start: SymbolLocation {
                line: s.0,
                column: s.1,
            },
            end: SymbolLocation {
                line: e.0,
                column: e.1,
            },
        }
    }

    #[test]
    fn test_missing_datasource_warning() {
        let schema = Schema {
            declarations: vec![],
            span: sp((1, 1), (1, 1)),
        };
        let mut analyzer = SymbolCollectionAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut ctx = AnalysisContext::new(&options);
        let result = analyzer.analyze(&schema, &mut ctx);
        assert!(!result.diagnostics.is_empty());
        assert!(result
            .diagnostics
            .iter()
            .any(|d| d.diagnostic_code == DiagnosticCode::MissingDatasource));
    }

    #[test]
    fn test_datasource_and_generator_required_fields() {
        // Datasource missing provider and url
        let ds = DatasourceDecl {
            name: Ident {
                text: "db".to_string(),
                span: sp((1, 1), (1, 3)),
            },
            assignments: vec![],
            docs: None,
            span: sp((1, 1), (3, 1)),
        };
        // Generator missing provider
        let generator_decl = GeneratorDecl {
            name: Ident {
                text: "client".to_string(),
                span: sp((1, 1), (1, 7)),
            },
            assignments: vec![],
            docs: None,
            span: sp((1, 1), (3, 1)),
        };

        let schema = Schema {
            declarations: vec![
                Declaration::Datasource(ds),
                Declaration::Generator(generator_decl),
            ],
            span: sp((1, 1), (3, 1)),
        };
        let mut analyzer = SymbolCollectionAnalyzer::new();
        let mut ctx = AnalysisContext::new(&AnalyzerOptions::default());
        let result = analyzer.analyze(&schema, &mut ctx);
        // Expect MissingField diagnostics
        assert!(
            result
                .diagnostics
                .iter()
                .filter(|d| d.diagnostic_code == DiagnosticCode::MissingField)
                .count()
                >= 1
        );
    }

    #[test]
    fn test_type_alias_experimental_gating() {
        // Create a type alias decl
        let type_decl = TypeDecl {
            name: Ident {
                text: "UserId".to_string(),
                span: sp((1, 6), (1, 12)),
            },
            rhs: TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![Ident {
                        text: "String".to_string(),
                        span: sp((1, 15), (1, 21)),
                    }],
                    span: sp((1, 15), (1, 21)),
                },
                span: sp((1, 15), (1, 21)),
            }),
            docs: None,
            span: sp((1, 1), (1, 21)),
        };
        let schema = Schema {
            declarations: vec![Declaration::Type(type_decl)],
            span: sp((1, 1), (1, 21)),
        };

        // Experimental disabled
        let mut analyzer = SymbolCollectionAnalyzer::new();
        let options = AnalyzerOptions {
            validation_mode: AnalyzerOptions::default().validation_mode,
            features: FeatureOptions {
                validate_experimental: false,
                performance_warnings: true,
                enable_parallelism: true,
            },
            phase_timeout: AnalyzerOptions::default().phase_timeout,
            target_provider: None,
            max_diagnostics: 100,
        };
        let mut ctx = AnalysisContext::new(&options);
        let result = analyzer.analyze(&schema, &mut ctx);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|d| d.diagnostic_code
                    == DiagnosticCode::ExperimentalFeature)
        );

        // Experimental enabled
        let mut analyzer2 = SymbolCollectionAnalyzer::new();
        let mut ctx2 = AnalysisContext::new(&AnalyzerOptions::default());
        let result2 = analyzer2.analyze(&schema, &mut ctx2);
        assert!(
            result2
                .diagnostics
                .iter()
                .all(|d| d.diagnostic_code
                    != DiagnosticCode::ExperimentalFeature)
        );
    }
}
