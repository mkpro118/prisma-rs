//! Symbol collection analyzer for building symbol tables from AST.
//!
//! This analyzer is the first phase of semantic analysis and is responsible
//! for traversing the AST and collecting all declared symbols into the
//! symbol table. It establishes the foundation for all subsequent analysis.

use crate::core::parser::ast::{Declaration, EnumMember, ModelMember, Schema};
use crate::core::semantic_analyzer::symbol_table::SymbolError;
use crate::core::semantic_analyzer::{
    context::{AnalysisContext, PhaseResult},
    diagnostics::{DiagnosticCode, SemanticDiagnostic},
    traits::PhaseAnalyzer,
};

#[cfg(test)]
use crate::core::semantic_analyzer::ConcurrencyMode;

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
/// The symbol collector validates basic identifier rules (non-empty, non-reserved).
pub struct SymbolCollectionAnalyzer;

impl SymbolCollectionAnalyzer {
    /// Create a new symbol collection analyzer.
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    /// Validate that an identifier follows basic validation rules.
    ///
    /// # Errors
    ///
    /// Returns a `SemanticDiagnostic` if the identifier:
    /// - Is empty
    /// - Uses a reserved keyword
    fn validate_identifier(
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

        // Prisma allows all valid JavaScript identifiers that don't start with
        // underscores/digits and don't contain '$' - these are validated by the lexer,
        // so no additional restrictions are needed here for compliance

        Ok(())
    }

    fn check_model(
        model: &crate::core::parser::ast::ModelDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Err(diagnostic) =
            Self::validate_identifier(&model.name.text, &model.name.span)
        {
            diagnostics.push(*diagnostic);
        }
        for member in &model.members {
            if let ModelMember::Field(field) = member
                && let Err(diagnostic) = Self::validate_identifier(
                    &field.name.text,
                    &field.name.span,
                )
            {
                diagnostics.push(*diagnostic);
            }
        }
    }

    fn check_enum(
        enum_decl: &crate::core::parser::ast::EnumDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Err(diagnostic) = Self::validate_identifier(
            &enum_decl.name.text,
            &enum_decl.name.span,
        ) {
            diagnostics.push(*diagnostic);
        }
        for member in &enum_decl.members {
            if let EnumMember::Value(value) = member
                && let Err(diagnostic) = Self::validate_identifier(
                    &value.name.text,
                    &value.name.span,
                )
            {
                diagnostics.push(*diagnostic);
            }
        }
    }

    fn check_datasource(
        datasource: &crate::core::parser::ast::DatasourceDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Err(diagnostic) = Self::validate_identifier(
            &datasource.name.text,
            &datasource.name.span,
        ) {
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
        generator: &crate::core::parser::ast::GeneratorDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Err(diagnostic) = Self::validate_identifier(
            &generator.name.text,
            &generator.name.span,
        ) {
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
        type_alias: &crate::core::parser::ast::TypeDecl,
        context: &AnalysisContext,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if context.options().features.validate_experimental {
            if let Err(diagnostic) = Self::validate_identifier(
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
        Self
    }
}

impl PhaseAnalyzer for SymbolCollectionAnalyzer {
    fn phase_name(&self) -> &'static str {
        "symbol-collection"
    }

    fn analyze(
        &self,
        schema: &Schema,
        context: &AnalysisContext,
    ) -> PhaseResult {
        let mut diagnostics = Vec::new();

        // Validate identifiers in all declarations
        for declaration in &schema.declarations {
            match declaration {
                Declaration::Model(model) => {
                    Self::check_model(model, &mut diagnostics);
                }
                Declaration::Enum(enum_decl) => {
                    Self::check_enum(enum_decl, &mut diagnostics);
                }
                Declaration::Datasource(datasource) => {
                    Self::check_datasource(datasource, &mut diagnostics);
                }
                Declaration::Generator(generator) => {
                    Self::check_generator(generator, &mut diagnostics);
                }
                Declaration::Type(type_alias) => {
                    Self::check_type_alias(
                        type_alias,
                        context,
                        &mut diagnostics,
                    );
                }
            }
        }

        Self::check_has_datasource(schema, &mut diagnostics);

        // Populate the shared symbol table with declarations
        if let Ok(mut symtab) = context.symbol_table.write() {
            for declaration in &schema.declarations {
                match declaration {
                    Declaration::Model(m) => {
                        if let Err(err) = symtab.add_model(m) {
                            if let SymbolError::DuplicateSymbol {
                                name,
                                existing_span,
                                new_span,
                                ..
                            } = err
                            {
                                diagnostics.push(
                                    SemanticDiagnostic::duplicate_declaration(
                                        new_span,
                                        &name,
                                        existing_span,
                                    ),
                                );
                            }
                        }
                    }
                    Declaration::Enum(e) => {
                        if let Err(err) = symtab.add_enum(e) {
                            if let SymbolError::DuplicateSymbol {
                                name,
                                existing_span,
                                new_span,
                                ..
                            } = err
                            {
                                diagnostics.push(
                                    SemanticDiagnostic::duplicate_declaration(
                                        new_span,
                                        &name,
                                        existing_span,
                                    ),
                                );
                            }
                        }
                    }
                    Declaration::Datasource(d) => {
                        if let Err(err) = symtab.add_datasource(d) {
                            if let SymbolError::DuplicateSymbol {
                                name,
                                existing_span,
                                new_span,
                                ..
                            } = err
                            {
                                diagnostics.push(
                                    SemanticDiagnostic::duplicate_declaration(
                                        new_span,
                                        &name,
                                        existing_span,
                                    ),
                                );
                            }
                        }
                    }
                    Declaration::Generator(g) => {
                        if let Err(err) = symtab.add_generator(g) {
                            if let SymbolError::DuplicateSymbol {
                                name,
                                existing_span,
                                new_span,
                                ..
                            } = err
                            {
                                diagnostics.push(
                                    SemanticDiagnostic::duplicate_declaration(
                                        new_span,
                                        &name,
                                        existing_span,
                                    ),
                                );
                            }
                        }
                    }
                    Declaration::Type(_t) => {
                        // Type aliases currently not added to the symbol table.
                    }
                }
            }
        }

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
        let span = create_test_span();

        // Valid identifiers (Prisma allows all valid JS identifiers)
        assert!(
            SymbolCollectionAnalyzer::validate_identifier("User", &span)
                .is_ok()
        );
        assert!(
            SymbolCollectionAnalyzer::validate_identifier("UserProfile", &span)
                .is_ok()
        );
        assert!(
            SymbolCollectionAnalyzer::validate_identifier("firstName", &span)
                .is_ok()
        );
        assert!(
            SymbolCollectionAnalyzer::validate_identifier("userId", &span)
                .is_ok()
        );
        assert!(
            SymbolCollectionAnalyzer::validate_identifier("user_id", &span)
                .is_ok()
        ); // snake_case is valid
        assert!(
            SymbolCollectionAnalyzer::validate_identifier("someField", &span)
                .is_ok()
        );
    }

    #[test]
    fn test_validate_identifier_reserved_keywords() {
        let span = create_test_span();

        let result =
            SymbolCollectionAnalyzer::validate_identifier("model", &span);
        assert!(result.is_err());

        let Err(err) = result else {
            panic!("Expected validation to fail for reserved keyword")
        };
        assert_eq!(err.diagnostic_code, DiagnosticCode::ReservedKeyword);
        assert!(err.message.contains("reserved keyword"));
    }

    #[test]
    fn test_validate_identifier_empty_name() {
        let span = create_test_span();

        let result = SymbolCollectionAnalyzer::validate_identifier("", &span);
        assert!(result.is_err());

        let Err(err) = result else {
            panic!("Expected validation to fail for empty identifier")
        };
        assert_eq!(err.diagnostic_code, DiagnosticCode::InvalidIdentifier);
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
        let analyzer = SymbolCollectionAnalyzer::new();
        let options = AnalyzerOptions::default();
        let ctx = AnalysisContext::new_test(&options);
        let result = analyzer.analyze(&schema, &ctx);
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
        let analyzer = SymbolCollectionAnalyzer::new();
        let ctx = AnalysisContext::new_test(&AnalyzerOptions::default());
        let result = analyzer.analyze(&schema, &ctx);
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
    fn test_duplicate_model_related_span() {
        use crate::core::semantic_analyzer::DiagnosticCode;

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

        // Two models with the same name "User" using distinct spans
        let user_model1 = ModelDecl {
            docs: None,
            name: Ident {
                text: "User".to_string(),
                span: sp((1, 1), (1, 5)),
            },
            members: vec![],
            attrs: vec![],
            span: sp((1, 1), (3, 1)),
        };

        let user_model2 = ModelDecl {
            docs: None,
            name: Ident {
                text: "User".to_string(),
                span: sp((4, 1), (4, 5)),
            },
            members: vec![],
            attrs: vec![],
            span: sp((4, 1), (6, 1)),
        };

        // Include a datasource to avoid MissingDatasource warning noise
        let ds = DatasourceDecl {
            name: Ident {
                text: "db".to_string(),
                span: sp((7, 1), (7, 3)),
            },
            assignments: vec![Assignment {
                key: Ident {
                    text: "provider".to_string(),
                    span: sp((8, 3), (8, 11)),
                },
                value: Expr::StringLit(StringLit {
                    value: "postgresql".to_string(),
                    span: sp((8, 14), (8, 26)),
                }),
                docs: None,
                span: sp((8, 3), (8, 26)),
            }],
            docs: None,
            span: sp((7, 1), (9, 1)),
        };

        let schema = Schema {
            declarations: vec![
                Declaration::Model(user_model1.clone()),
                Declaration::Model(user_model2.clone()),
                Declaration::Datasource(ds),
            ],
            span: sp((1, 1), (10, 1)),
        };

        let analyzer = SymbolCollectionAnalyzer::new();
        let ctx = AnalysisContext::new_test(&AnalyzerOptions::default());
        let result = analyzer.analyze(&schema, &ctx);

        // Find duplicate declaration diagnostic and verify it carries a related span pointing to the first model
        let mut dup_diags = result.diagnostics.iter().filter(|d| {
            d.diagnostic_code == DiagnosticCode::DuplicateDeclaration
        });

        let diag = dup_diags
            .next()
            .expect("expected duplicate declaration diagnostic");
        assert!(
            !diag.related_spans.is_empty(),
            "duplicate declaration should include the first declaration span"
        );
        assert_eq!(diag.related_spans[0].span, user_model1.span);
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
        let analyzer = SymbolCollectionAnalyzer::new();
        let options = AnalyzerOptions {
            validation_mode: AnalyzerOptions::default().validation_mode,
            features: FeatureOptions {
                validate_experimental: false,
                performance_warnings: true,
                enable_parallelism: true,
            },
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 2,
            },
            phase_timeout: AnalyzerOptions::default().phase_timeout,
            target_provider: None,
            max_diagnostics: 100,
        };
        let ctx = AnalysisContext::new_test(&options);
        let result = analyzer.analyze(&schema, &ctx);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|d| d.diagnostic_code
                    == DiagnosticCode::ExperimentalFeature)
        );

        // Experimental enabled
        let analyzer2 = SymbolCollectionAnalyzer::new();
        let ctx2 = AnalysisContext::new_test(&AnalyzerOptions::default());
        let result2 = analyzer2.analyze(&schema, &ctx2);
        assert!(
            result2
                .diagnostics
                .iter()
                .all(|d| d.diagnostic_code
                    != DiagnosticCode::ExperimentalFeature)
        );
    }

    #[test]
    fn test_all_reserved_keywords() {
        let reserved_words = [
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

        for reserved_word in &reserved_words {
            let span = create_test_span();
            let result = SymbolCollectionAnalyzer::validate_identifier(
                reserved_word,
                &span,
            );

            assert!(
                result.is_err(),
                "Expected {reserved_word} to be rejected as reserved"
            );
            if let Err(diagnostic) = result {
                assert_eq!(
                    diagnostic.diagnostic_code,
                    DiagnosticCode::ReservedKeyword
                );
                assert!(diagnostic.message.contains("reserved keyword"));
            }
        }
    }

    #[test]
    fn test_various_valid_identifier_formats() {
        let valid_identifiers = [
            "user",
            "User",
            "userId",
            "UserProfile",
            "user_id",
            "user123",
            "a",
            "A",
            "myVeryLongIdentifierName",
            "snake_case_field",
            "camelCaseField",
            "PascalCaseType",
            "mixedCase123",
            "field1",
        ];

        for identifier in &valid_identifiers {
            let span = create_test_span();
            let result = SymbolCollectionAnalyzer::validate_identifier(
                identifier, &span,
            );
            assert!(result.is_ok(), "Expected {identifier} to be valid");
        }
    }

    #[test]
    fn test_model_with_various_field_types() {
        let fields = vec![
            ModelMember::Field(FieldDecl {
                docs: None,
                name: Ident {
                    text: "id".to_string(),
                    span: sp((1, 1), (1, 3)),
                },
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![Ident {
                            text: "String".to_string(),
                            span: sp((1, 4), (1, 10)),
                        }],
                        span: sp((1, 4), (1, 10)),
                    },
                    span: sp((1, 4), (1, 10)),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: sp((1, 1), (1, 10)),
            }),
            ModelMember::Field(FieldDecl {
                docs: None,
                name: Ident {
                    text: "name".to_string(),
                    span: sp((2, 1), (2, 5)),
                },
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![Ident {
                            text: "String".to_string(),
                            span: sp((2, 6), (2, 12)),
                        }],
                        span: sp((2, 6), (2, 12)),
                    },
                    span: sp((2, 6), (2, 12)),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: sp((2, 1), (2, 12)),
            }),
        ];

        let model = ModelDecl {
            name: Ident {
                text: "User".to_string(),
                span: sp((1, 7), (1, 11)),
            },
            members: fields,
            attrs: Vec::new(),
            docs: None,
            span: sp((1, 1), (3, 1)),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: sp((1, 1), (3, 1)),
        };

        let analyzer = SymbolCollectionAnalyzer::new();
        let ctx = AnalysisContext::new_test(&AnalyzerOptions::default());
        let result = analyzer.analyze(&schema, &ctx);

        // Should not have any identifier validation errors
        assert!(
            result.diagnostics.iter().all(|d| d.diagnostic_code
                != DiagnosticCode::InvalidIdentifier
                && d.diagnostic_code != DiagnosticCode::ReservedKeyword)
        );
    }

    #[test]
    fn test_enum_with_various_values() {
        let values = vec![
            EnumMember::Value(EnumValue {
                name: Ident {
                    text: "ACTIVE".to_string(),
                    span: sp((1, 1), (1, 7)),
                },
                attrs: Vec::new(),
                docs: None,
                span: sp((1, 1), (1, 7)),
            }),
            EnumMember::Value(EnumValue {
                name: Ident {
                    text: "INACTIVE".to_string(),
                    span: sp((2, 1), (2, 9)),
                },
                attrs: Vec::new(),
                docs: None,
                span: sp((2, 1), (2, 9)),
            }),
            EnumMember::Value(EnumValue {
                name: Ident {
                    text: "pending".to_string(),
                    span: sp((3, 1), (3, 8)),
                },
                attrs: Vec::new(),
                docs: None,
                span: sp((3, 1), (3, 8)),
            }),
        ];

        let enum_decl = EnumDecl {
            name: Ident {
                text: "Status".to_string(),
                span: sp((1, 6), (1, 12)),
            },
            members: values,
            attrs: Vec::new(),
            docs: None,
            span: sp((1, 1), (4, 1)),
        };

        let schema = Schema {
            declarations: vec![Declaration::Enum(enum_decl)],
            span: sp((1, 1), (4, 1)),
        };

        let analyzer = SymbolCollectionAnalyzer::new();
        let ctx = AnalysisContext::new_test(&AnalyzerOptions::default());
        let result = analyzer.analyze(&schema, &ctx);

        // Should not have identifier validation errors for valid enum values
        assert!(
            result.diagnostics.iter().all(|d| d.diagnostic_code
                != DiagnosticCode::InvalidIdentifier
                && d.diagnostic_code != DiagnosticCode::ReservedKeyword)
        );
    }

    #[test]
    fn test_datasource_with_all_required_fields() {
        let datasource = DatasourceDecl {
            name: Ident {
                text: "db".to_string(),
                span: sp((1, 11), (1, 13)),
            },
            assignments: vec![
                Assignment {
                    key: Ident {
                        text: "provider".to_string(),
                        span: sp((2, 3), (2, 11)),
                    },
                    value: Expr::StringLit(StringLit {
                        value: "postgresql".to_string(),
                        span: sp((2, 14), (2, 26)),
                    }),
                    docs: None,
                    span: sp((2, 3), (2, 26)),
                },
                Assignment {
                    key: Ident {
                        text: "url".to_string(),
                        span: sp((3, 3), (3, 6)),
                    },
                    value: Expr::StringLit(StringLit {
                        value: "env(\"DATABASE_URL\")".to_string(),
                        span: sp((3, 9), (3, 29)),
                    }),
                    docs: None,
                    span: sp((3, 3), (3, 29)),
                },
            ],
            docs: None,
            span: sp((1, 1), (4, 1)),
        };

        let schema = Schema {
            declarations: vec![Declaration::Datasource(datasource)],
            span: sp((1, 1), (4, 1)),
        };

        let analyzer = SymbolCollectionAnalyzer::new();
        let ctx = AnalysisContext::new_test(&AnalyzerOptions::default());
        let result = analyzer.analyze(&schema, &ctx);

        // Should not have missing field errors
        assert!(
            result
                .diagnostics
                .iter()
                .all(|d| d.diagnostic_code != DiagnosticCode::MissingField)
        );
    }

    #[test]
    fn test_generator_with_all_required_fields() {
        let generator = GeneratorDecl {
            name: Ident {
                text: "client".to_string(),
                span: sp((1, 11), (1, 17)),
            },
            assignments: vec![Assignment {
                key: Ident {
                    text: "provider".to_string(),
                    span: sp((2, 3), (2, 11)),
                },
                value: Expr::StringLit(StringLit {
                    value: "prisma-client-js".to_string(),
                    span: sp((2, 14), (2, 32)),
                }),
                docs: None,
                span: sp((2, 3), (2, 32)),
            }],
            docs: None,
            span: sp((1, 1), (3, 1)),
        };

        let schema = Schema {
            declarations: vec![Declaration::Generator(generator)],
            span: sp((1, 1), (3, 1)),
        };

        let analyzer = SymbolCollectionAnalyzer::new();
        let ctx = AnalysisContext::new_test(&AnalyzerOptions::default());
        let result = analyzer.analyze(&schema, &ctx);

        // Should not have missing field errors
        assert!(
            result
                .diagnostics
                .iter()
                .all(|d| d.diagnostic_code != DiagnosticCode::MissingField)
        );
    }

    /// Create a complex test schema with all declaration types for testing.
    fn create_complex_test_schema() -> Schema {
        let user_model = create_test_user_model();
        let status_enum = create_test_status_enum();
        let datasource = create_test_datasource();
        let generator = create_test_generator();

        Schema {
            declarations: vec![
                Declaration::Model(user_model),
                Declaration::Enum(status_enum),
                Declaration::Datasource(datasource),
                Declaration::Generator(generator),
            ],
            span: sp((1, 1), (16, 1)),
        }
    }

    /// Create a test User model declaration.
    fn create_test_user_model() -> ModelDecl {
        ModelDecl {
            name: Ident {
                text: "User".to_string(),
                span: sp((1, 7), (1, 11)),
            },
            members: vec![ModelMember::Field(FieldDecl {
                docs: None,
                name: Ident {
                    text: "id".to_string(),
                    span: sp((2, 3), (2, 5)),
                },
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![Ident {
                            text: "String".to_string(),
                            span: sp((2, 6), (2, 12)),
                        }],
                        span: sp((2, 6), (2, 12)),
                    },
                    span: sp((2, 6), (2, 12)),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: sp((2, 3), (2, 12)),
            })],
            attrs: Vec::new(),
            docs: None,
            span: sp((1, 1), (3, 1)),
        }
    }

    /// Create a test Status enum declaration.
    fn create_test_status_enum() -> EnumDecl {
        EnumDecl {
            name: Ident {
                text: "Status".to_string(),
                span: sp((5, 6), (5, 12)),
            },
            members: vec![EnumMember::Value(EnumValue {
                name: Ident {
                    text: "ACTIVE".to_string(),
                    span: sp((6, 3), (6, 9)),
                },
                attrs: Vec::new(),
                docs: None,
                span: sp((6, 3), (6, 9)),
            })],
            attrs: Vec::new(),
            docs: None,
            span: sp((5, 1), (7, 1)),
        }
    }

    /// Create a test datasource declaration.
    fn create_test_datasource() -> DatasourceDecl {
        DatasourceDecl {
            name: Ident {
                text: "db".to_string(),
                span: sp((9, 11), (9, 13)),
            },
            assignments: vec![
                Assignment {
                    key: Ident {
                        text: "provider".to_string(),
                        span: sp((10, 3), (10, 11)),
                    },
                    value: Expr::StringLit(StringLit {
                        value: "postgresql".to_string(),
                        span: sp((10, 14), (10, 26)),
                    }),
                    docs: None,
                    span: sp((10, 3), (10, 26)),
                },
                Assignment {
                    key: Ident {
                        text: "url".to_string(),
                        span: sp((11, 3), (11, 6)),
                    },
                    value: Expr::StringLit(StringLit {
                        value: "env(\"DATABASE_URL\")".to_string(),
                        span: sp((11, 9), (11, 29)),
                    }),
                    docs: None,
                    span: sp((11, 3), (11, 29)),
                },
            ],
            docs: None,
            span: sp((9, 1), (12, 1)),
        }
    }

    /// Create a test generator declaration.
    fn create_test_generator() -> GeneratorDecl {
        GeneratorDecl {
            name: Ident {
                text: "client".to_string(),
                span: sp((14, 11), (14, 17)),
            },
            assignments: vec![Assignment {
                key: Ident {
                    text: "provider".to_string(),
                    span: sp((15, 3), (15, 11)),
                },
                value: Expr::StringLit(StringLit {
                    value: "prisma-client-js".to_string(),
                    span: sp((15, 14), (15, 32)),
                }),
                docs: None,
                span: sp((15, 3), (15, 32)),
            }],
            docs: None,
            span: sp((14, 1), (16, 1)),
        }
    }

    /// Assert that no problematic diagnostics are present in the results.
    fn assert_no_problematic_diagnostics(diagnostics: &[SemanticDiagnostic]) {
        let problematic_diagnostics: Vec<_> = diagnostics
            .iter()
            .filter(|d| {
                matches!(
                    d.diagnostic_code,
                    DiagnosticCode::InvalidIdentifier
                        | DiagnosticCode::ReservedKeyword
                        | DiagnosticCode::MissingField
                )
            })
            .collect();

        assert!(
            problematic_diagnostics.is_empty(),
            "Unexpected validation errors: {problematic_diagnostics:?}"
        );
    }

    #[test]
    fn test_complex_schema_with_all_declaration_types() {
        let schema = create_complex_test_schema();

        let analyzer = SymbolCollectionAnalyzer::new();
        let ctx = AnalysisContext::new_test(&AnalyzerOptions::default());
        let result = analyzer.analyze(&schema, &ctx);

        assert_no_problematic_diagnostics(&result.diagnostics);
    }

    #[test]
    fn test_identifier_validation_edge_cases() {
        let edge_cases = [
            ("", true, DiagnosticCode::InvalidIdentifier), // Empty string
            ("123invalid", false, DiagnosticCode::InvalidIdentifier), // This should be caught by lexer, so we won't test it
            ("valid123", false, DiagnosticCode::InvalidIdentifier),
            ("_underscore", false, DiagnosticCode::InvalidIdentifier), // This should be caught by lexer
            ("validName", false, DiagnosticCode::InvalidIdentifier),
        ];

        for (identifier, should_error, expected_code) in &edge_cases {
            if identifier == &"123invalid" || identifier == &"_underscore" {
                // These would be caught by the lexer, so skip testing them here
                continue;
            }

            let span = create_test_span();
            let result = SymbolCollectionAnalyzer::validate_identifier(
                identifier, &span,
            );

            if *should_error {
                assert!(result.is_err(), "Expected {identifier} to be invalid");
                if let Err(diagnostic) = result {
                    assert_eq!(diagnostic.diagnostic_code, *expected_code);
                }
            } else {
                assert!(result.is_ok(), "Expected {identifier} to be valid");
            }
        }
    }

    #[test]
    fn test_schema_with_datasource_present() {
        let datasource = DatasourceDecl {
            name: Ident {
                text: "db".to_string(),
                span: sp((1, 11), (1, 13)),
            },
            assignments: vec![
                Assignment {
                    key: Ident {
                        text: "provider".to_string(),
                        span: sp((2, 3), (2, 11)),
                    },
                    value: Expr::StringLit(StringLit {
                        value: "postgresql".to_string(),
                        span: sp((2, 14), (2, 26)),
                    }),
                    docs: None,
                    span: sp((2, 3), (2, 26)),
                },
                Assignment {
                    key: Ident {
                        text: "url".to_string(),
                        span: sp((3, 3), (3, 6)),
                    },
                    value: Expr::StringLit(StringLit {
                        value: "env(\"DATABASE_URL\")".to_string(),
                        span: sp((3, 9), (3, 29)),
                    }),
                    docs: None,
                    span: sp((3, 3), (3, 29)),
                },
            ],
            docs: None,
            span: sp((1, 1), (4, 1)),
        };

        let model = ModelDecl {
            name: Ident {
                text: "User".to_string(),
                span: sp((5, 7), (5, 11)),
            },
            members: vec![],
            attrs: Vec::new(),
            docs: None,
            span: sp((5, 1), (6, 1)),
        };

        let schema = Schema {
            declarations: vec![
                Declaration::Datasource(datasource),
                Declaration::Model(model),
            ],
            span: sp((1, 1), (6, 1)),
        };

        let analyzer = SymbolCollectionAnalyzer::new();
        let ctx = AnalysisContext::new_test(&AnalyzerOptions::default());
        let result = analyzer.analyze(&schema, &ctx);

        // Should not have missing datasource warning
        assert!(!result.diagnostics.iter().any(|d|
            d.diagnostic_code == DiagnosticCode::MissingDatasource
        ));
    }
}
