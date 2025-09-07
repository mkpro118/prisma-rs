//! Type resolution analyzer for semantic analysis.
//!
//! This analyzer is the second phase of semantic analysis and resolves all type
//! references in the schema. It builds upon the symbol table created by the symbol
//! collection analyzer to validate that all type references are valid.

use crate::core::parser::ast::{
    Declaration, HasSpan, ModelMember, Schema, TypeRef,
};
use crate::core::scanner::tokens::SymbolSpan;
use crate::core::semantic_analyzer::{
    context::{AnalysisContext, PhaseResult},
    diagnostics::{DiagnosticCode, SemanticDiagnostic},
    traits::PhaseAnalyzer,
    type_resolver::{ResolvedType, TypeResolutionError, TypeResolver},
};

/// Analyzer responsible for resolving all type references in the schema.
///
/// This phase builds on the symbol collection phase and validates that:
/// - All type references resolve to valid types
/// - No circular type dependencies exist  
/// - Type usage follows Prisma rules (e.g., no recursive types without indirection)
///
/// The type resolution analyzer populates the schema with resolved type information
/// that subsequent analyzers can use for validation.
pub struct TypeResolutionAnalyzer {
    /// Type resolver instance for this analysis
    type_resolver: TypeResolver,
}

impl TypeResolutionAnalyzer {
    /// Create a new type resolution analyzer.
    #[must_use]
    pub fn new() -> Self {
        Self {
            type_resolver: TypeResolver::new(),
        }
    }

    /// Resolve all type references in the schema.
    fn resolve_schema_types(
        &mut self,
        schema: &Schema,
        context: &AnalysisContext,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Resolve types in all model fields
        for declaration in &schema.declarations {
            if let Declaration::Model(model) = declaration {
                self.resolve_model_types(model, context, diagnostics);
            }
        }

        // Check for circular dependencies after all types are processed
        if let Err(error) = self.type_resolver.check_circular_dependencies() {
            Self::add_type_resolution_error(error, &schema.span, diagnostics);
        }
    }

    /// Resolve types for all fields in a model.
    fn resolve_model_types(
        &mut self,
        model: &crate::core::parser::ast::ModelDecl,
        context: &AnalysisContext,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        for member in &model.members {
            if let ModelMember::Field(field) = member {
                self.resolve_field_type(field, context, diagnostics);
            }
        }
    }

    /// Resolve the type of a single field.
    fn resolve_field_type(
        &mut self,
        field: &crate::core::parser::ast::FieldDecl,
        _context: &AnalysisContext,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // For now, create a temporary symbol table
        // The actual implementation would get the symbol table from the analyzer orchestrator
        let symbol_table =
            crate::core::semantic_analyzer::symbol_table::SymbolTable::new();

        match self
            .type_resolver
            .resolve_type(&field.r#type, &symbol_table)
        {
            Ok(resolved_type) => {
                // Store the resolved type in context for later phases
                // For now, we just validate that resolution succeeds
                Self::validate_resolved_type(
                    &resolved_type,
                    &field.r#type,
                    diagnostics,
                );
            }
            Err(error) => {
                Self::add_type_resolution_error(
                    error,
                    field.r#type.span(),
                    diagnostics,
                );
            }
        }
    }

    /// Validate that a resolved type follows Prisma rules.
    fn validate_resolved_type(
        resolved_type: &ResolvedType,
        type_ref: &TypeRef,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Validate list nesting depth (Prisma doesn't allow nested lists)
        if let ResolvedType::List(inner) = resolved_type
            && inner.is_list()
        {
            diagnostics.push(SemanticDiagnostic::error(
                type_ref.span().clone(),
                "Prisma does not support nested lists".to_string(),
                DiagnosticCode::InvalidTypeUsage,
            ));
        }

        // Validate model references
        if let ResolvedType::Model(model_name) = resolved_type {
            // Add dependency tracking for circular reference detection
            // This would need access to current model context
            // For now, we just validate the reference exists
            Self::validate_model_reference(model_name, type_ref, diagnostics);
        }
    }

    /// Validate that a model reference is valid.
    fn validate_model_reference(
        model_name: &str,
        type_ref: &TypeRef,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Additional validation could be added here
        // For example, checking if the model has required fields
        _ = (model_name, type_ref, diagnostics);
    }

    /// Convert a type resolution error into a diagnostic.
    fn add_type_resolution_error(
        error: TypeResolutionError,
        span: &SymbolSpan,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        let diagnostic = match error {
            TypeResolutionError::UnknownType { name } => {
                SemanticDiagnostic::error(
                    span.clone(),
                    format!("Unknown type '{name}'"),
                    DiagnosticCode::UnknownType,
                )
            }
            TypeResolutionError::CircularDependency { cycle } => {
                SemanticDiagnostic::error(
                    span.clone(),
                    format!("Circular type dependency: {}", cycle.join(" -> ")),
                    DiagnosticCode::CircularDependency,
                )
            }
            TypeResolutionError::NotAType {
                name,
                actual_symbol_type,
            } => SemanticDiagnostic::error(
                span.clone(),
                format!("'{name}' is not a type (it's a {actual_symbol_type})"),
                DiagnosticCode::InvalidTypeUsage,
            ),
            TypeResolutionError::UnknownBuiltinType { name } => {
                SemanticDiagnostic::error(
                    span.clone(),
                    format!("Unknown built-in type '{name}'"),
                    DiagnosticCode::UnknownType,
                )
            }
            TypeResolutionError::ConstraintViolation {
                type_name,
                constraint,
                message,
            } => SemanticDiagnostic::error(
                span.clone(),
                format!(
                    "Type '{type_name}' violates constraint '{constraint}': {message}"
                ),
                DiagnosticCode::ConstraintViolation,
            ),
            TypeResolutionError::IncompatibleTypes { from, to, context } => {
                SemanticDiagnostic::error(
                    span.clone(),
                    format!(
                        "Incompatible types: cannot convert '{from}' to '{to}' in {context}"
                    ),
                    DiagnosticCode::TypeMismatch,
                )
            }
        };

        diagnostics.push(diagnostic);
    }

    // No longer needed - using proper spans from TypeRef
}

impl Default for TypeResolutionAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl PhaseAnalyzer for TypeResolutionAnalyzer {
    fn phase_name(&self) -> &'static str {
        "type-resolution"
    }

    fn analyze(
        &self,
        schema: &Schema,
        context: &AnalysisContext,
    ) -> PhaseResult {
        let diagnostics = Vec::new();

        // TODO: Re-implement with thread-safe approach
        // For now, basic validation without state tracking
        // self.resolve_schema_types(schema, context, &mut diagnostics);

        PhaseResult::new(diagnostics)
    }

    fn dependencies(&self) -> &[&'static str] {
        // Type resolution requires symbol collection to have run first
        &["symbol-collection"]
    }

    fn supports_parallel_execution(&self) -> bool {
        // Type resolution modifies shared type resolver state, so no parallelism
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::parser::ast::*;
    use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
    use crate::core::semantic_analyzer::AnalyzerOptions;

    fn create_test_span() -> SymbolSpan {
        SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation { line: 1, column: 5 },
        }
    }

    fn create_test_ident(name: &str) -> Ident {
        Ident {
            text: name.to_string(),
            span: create_test_span(),
        }
    }

    #[test]
    fn test_type_resolution_analyzer_creation() {
        let analyzer = TypeResolutionAnalyzer::new();
        assert_eq!(analyzer.phase_name(), "type-resolution");
        assert_eq!(analyzer.dependencies(), &["symbol-collection"]);
        assert!(!analyzer.supports_parallel_execution());
    }

    #[test]
    fn test_schema_with_valid_builtin_types() {
        // Create a schema with a model using builtin types
        let field = FieldDecl {
            docs: None,
            name: create_test_ident("name"),
            r#type: TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![create_test_ident("String")],
                    span: create_test_span(),
                },
                span: create_test_span(),
            }),
            optional: false,
            modifiers: Vec::new(),
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: vec![ModelMember::Field(field)],
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let mut analyzer = TypeResolutionAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Should have no errors for valid builtin types
        assert!(
            result.diagnostics.is_empty()
                || result.diagnostics.iter().all(|d| !d.is_error())
        );
    }

    #[test]
    fn test_schema_with_unknown_type() {
        let field = FieldDecl {
            docs: None,
            name: create_test_ident("profile"),
            r#type: TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![create_test_ident("UnknownType")],
                    span: create_test_span(),
                },
                span: create_test_span(),
            }),
            optional: false,
            modifiers: Vec::new(),
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: vec![ModelMember::Field(field)],
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let mut analyzer = TypeResolutionAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Should have errors for unknown type
        assert!(!result.diagnostics.is_empty());
        assert!(result.diagnostics.iter().any(|d| d.is_error()
            && matches!(d.diagnostic_code, DiagnosticCode::UnknownType)));
    }

    #[test]
    fn test_nested_list_validation() {
        // Create a field with nested list type: String[][]
        let inner_list = TypeRef::List(ListType {
            inner: Box::new(TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![create_test_ident("String")],
                    span: create_test_span(),
                },
                span: create_test_span(),
            })),
            span: create_test_span(),
        });

        let nested_list = TypeRef::List(ListType {
            inner: Box::new(inner_list),
            span: create_test_span(),
        });

        let field = FieldDecl {
            docs: None,
            name: create_test_ident("tags"),
            r#type: nested_list,
            optional: false,
            modifiers: Vec::new(),
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: vec![ModelMember::Field(field)],
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let mut analyzer = TypeResolutionAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Should have error for nested lists
        assert!(!result.diagnostics.is_empty());
        assert!(result.diagnostics.iter().any(|d| d.is_error()
            && matches!(d.diagnostic_code, DiagnosticCode::InvalidTypeUsage)));
    }

    #[test]
    fn test_all_builtin_scalar_types() {
        let scalar_types = [
            "String", "Int", "Float", "Boolean", "DateTime", "Json", "Bytes",
            "Decimal", "BigInt", "Uuid",
        ];

        for scalar_type in &scalar_types {
            let field = FieldDecl {
                docs: None,
                name: create_test_ident("test_field"),
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident(scalar_type)],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: create_test_span(),
            };

            let model = ModelDecl {
                docs: None,
                name: create_test_ident("TestModel"),
                members: vec![ModelMember::Field(field)],
                attrs: Vec::new(),
                span: create_test_span(),
            };

            let schema = Schema {
                declarations: vec![Declaration::Model(model)],
                span: create_test_span(),
            };

            let mut analyzer = TypeResolutionAnalyzer::new();
            let options = AnalyzerOptions::default();
            let mut context = AnalysisContext::new_test(&options);

            let result = analyzer.analyze(&schema, &mut context);

            // Should not have errors for valid builtin types
            let error_diagnostics: Vec<_> =
                result.diagnostics.iter().filter(|d| d.is_error()).collect();
            assert!(
                error_diagnostics.is_empty(),
                "Unexpected errors for type {scalar_type}: {error_diagnostics:?}"
            );
        }
    }

    #[test]
    fn test_list_types_validation() {
        let test_cases = [
            ("String[]", false),  // Valid single list
            ("Int[]", false),     // Valid single list
            ("Boolean[]", false), // Valid single list
        ];

        for (type_description, should_error) in &test_cases {
            let list_type = TypeRef::List(ListType {
                inner: Box::new(TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("String")],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                })),
                span: create_test_span(),
            });

            let field = FieldDecl {
                docs: None,
                name: create_test_ident("list_field"),
                r#type: list_type,
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: create_test_span(),
            };

            let model = ModelDecl {
                docs: None,
                name: create_test_ident("TestModel"),
                members: vec![ModelMember::Field(field)],
                attrs: Vec::new(),
                span: create_test_span(),
            };

            let schema = Schema {
                declarations: vec![Declaration::Model(model)],
                span: create_test_span(),
            };

            let mut analyzer = TypeResolutionAnalyzer::new();
            let options = AnalyzerOptions::default();
            let mut context = AnalysisContext::new_test(&options);

            let result = analyzer.analyze(&schema, &mut context);

            let has_errors = result.diagnostics.iter().any(crate::core::semantic_analyzer::diagnostics::SemanticDiagnostic::is_error);

            if *should_error {
                assert!(
                    has_errors,
                    "Expected errors for type {type_description}"
                );
            } else {
                assert!(
                    !has_errors,
                    "Unexpected errors for type {}: {:?}",
                    type_description, result.diagnostics
                );
            }
        }
    }

    #[test]
    fn test_multiple_fields_with_different_types() {
        let fields = vec![
            FieldDecl {
                docs: None,
                name: create_test_ident("id"),
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("String")],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: create_test_span(),
            },
            FieldDecl {
                docs: None,
                name: create_test_ident("age"),
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("Int")],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: create_test_span(),
            },
            FieldDecl {
                docs: None,
                name: create_test_ident("tags"),
                r#type: TypeRef::List(ListType {
                    inner: Box::new(TypeRef::Named(NamedType {
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("String")],
                            span: create_test_span(),
                        },
                        span: create_test_span(),
                    })),
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: create_test_span(),
            },
        ];

        let model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: fields.into_iter().map(ModelMember::Field).collect(),
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let mut analyzer = TypeResolutionAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Should not have errors for valid mixed types
        let error_diagnostics: Vec<_> =
            result.diagnostics.iter().filter(|d| d.is_error()).collect();
        assert!(
            error_diagnostics.is_empty(),
            "Unexpected errors: {error_diagnostics:?}"
        );
    }

    #[test]
    fn test_empty_schema() {
        let schema = Schema {
            declarations: vec![],
            span: create_test_span(),
        };

        let mut analyzer = TypeResolutionAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Empty schema should not produce errors
        assert!(result.diagnostics.iter().all(|d| !d.is_error()));
    }

    #[test]
    fn test_model_without_fields() {
        let model = ModelDecl {
            docs: None,
            name: create_test_ident("EmptyModel"),
            members: vec![], // No fields
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let mut analyzer = TypeResolutionAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Model without fields should not cause type resolution errors
        assert!(result.diagnostics.iter().all(|d| !d.is_error()));
    }

    #[test]
    fn test_multiple_models() {
        let user_model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: vec![ModelMember::Field(FieldDecl {
                docs: None,
                name: create_test_ident("name"),
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("String")],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: create_test_span(),
            })],
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let post_model = ModelDecl {
            docs: None,
            name: create_test_ident("Post"),
            members: vec![ModelMember::Field(FieldDecl {
                docs: None,
                name: create_test_ident("title"),
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("String")],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: create_test_span(),
            })],
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![
                Declaration::Model(user_model),
                Declaration::Model(post_model),
            ],
            span: create_test_span(),
        };

        let mut analyzer = TypeResolutionAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Multiple models with valid types should not have errors
        let error_diagnostics: Vec<_> =
            result.diagnostics.iter().filter(|d| d.is_error()).collect();
        assert!(
            error_diagnostics.is_empty(),
            "Unexpected errors: {error_diagnostics:?}"
        );
    }

    #[test]
    fn test_mixed_valid_and_invalid_types() {
        let fields = vec![
            FieldDecl {
                docs: None,
                name: create_test_ident("valid_field"),
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("String")],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: create_test_span(),
            },
            FieldDecl {
                docs: None,
                name: create_test_ident("invalid_field"),
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("NonExistentType")],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: Vec::new(),
                span: create_test_span(),
            },
        ];

        let model = ModelDecl {
            docs: None,
            name: create_test_ident("MixedModel"),
            members: fields.into_iter().map(ModelMember::Field).collect(),
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let mut analyzer = TypeResolutionAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Should have exactly one error for the invalid type
        let error_diagnostics: Vec<_> =
            result.diagnostics.iter().filter(|d| d.is_error()).collect();
        assert_eq!(error_diagnostics.len(), 1);
        assert!(matches!(
            error_diagnostics[0].diagnostic_code,
            DiagnosticCode::UnknownType
        ));
    }

    #[test]
    fn test_circular_dependency_detection() {
        // This test requires more complex setup that would need model references
        // For now, we test that the circular dependency checker is called
        let mut analyzer = TypeResolutionAnalyzer::new();

        // Add some fake dependencies to the type resolver
        analyzer
            .type_resolver
            .add_type_dependency("A".to_string(), "B".to_string());
        analyzer
            .type_resolver
            .add_type_dependency("B".to_string(), "A".to_string());

        let schema = Schema {
            declarations: vec![],
            span: create_test_span(),
        };

        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Should detect circular dependency
        assert!(result.diagnostics.iter().any(|d| matches!(
            d.diagnostic_code,
            DiagnosticCode::CircularDependency
        )));
    }
}
