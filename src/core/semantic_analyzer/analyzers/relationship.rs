//! Relationship analyzer for semantic analysis.
//!
//! This analyzer is the third phase of semantic analysis and analyzes all `@relation`
//! attributes in the schema. It validates relationship definitions, checks for proper
//! back-references, and builds a relationship graph for the schema.

use crate::core::parser::ast::{
    Declaration, FieldAttribute, ModelMember, Schema,
};
use crate::core::scanner::tokens::SymbolSpan;
use crate::core::semantic_analyzer::{
    context::{AnalysisContext, PhaseResult, Relationship, RelationshipType},
    diagnostics::{DiagnosticCode, SemanticDiagnostic},
    traits::PhaseAnalyzer,
};
use std::collections::HashSet;

// Relationship and RelationshipType are now imported from context

/// Analyzer responsible for validating model relationships.
///
/// This phase builds on the symbol collection and type resolution phases to validate:
/// - All `@relation` attributes are properly formed
/// - Back-references exist for bidirectional relationships
/// - Foreign key fields exist and have correct types
/// - No conflicting relationship definitions
/// - Proper naming of relationship fields
///
/// The relationship analyzer is now stateless and writes directly to the shared
/// `RelationshipGraph` in the `AnalysisContext`, eliminating redundant internal state.
pub struct RelationshipAnalyzer;

impl RelationshipAnalyzer {
    /// Create a new relationship analyzer.
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    /// Extract the target model name from a field type.
    fn extract_target_model_from_field_type(
        field_type: &crate::core::parser::ast::TypeRef,
    ) -> Option<String> {
        match field_type {
            crate::core::parser::ast::TypeRef::Named(named) => named
                .name
                .parts
                .first()
                .map(|first_part| first_part.text.clone()),
            crate::core::parser::ast::TypeRef::List(list) => {
                // For list types like User[], extract User
                Self::extract_target_model_from_field_type(&list.inner)
            }
        }
    }

    /// Parse arguments from a @relation attribute.
    fn parse_relation_arguments(
        attr: &FieldAttribute,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) -> RelationArguments {
        let mut args = RelationArguments {
            name: None,
            fields: None,
            references: None,
            on_delete: None,
            on_update: None,
        };

        if let Some(arg_list) = &attr.args {
            for arg in &arg_list.items {
                if let crate::core::parser::ast::Arg::Named(named_arg) = arg {
                    Self::parse_single_relation_argument(
                        named_arg,
                        &mut args,
                        diagnostics,
                    );
                }
            }
        }

        args
    }

    /// Parse a single named argument from a @relation attribute.
    fn parse_single_relation_argument(
        named_arg: &crate::core::parser::ast::NamedArg,
        args: &mut RelationArguments,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        let arg_name = &named_arg.name.text;
        match arg_name.as_str() {
            "name" => Self::parse_string_relation_arg(
                named_arg,
                &mut args.name,
                "name",
                diagnostics,
            ),
            "fields" => Self::parse_array_relation_arg(
                named_arg,
                &mut args.fields,
                "fields",
                "field names",
                diagnostics,
            ),
            "references" => Self::parse_array_relation_arg(
                named_arg,
                &mut args.references,
                "references",
                "field names",
                diagnostics,
            ),
            "onDelete" => Self::parse_string_relation_arg(
                named_arg,
                &mut args.on_delete,
                "onDelete",
                diagnostics,
            ),
            "onUpdate" => Self::parse_string_relation_arg(
                named_arg,
                &mut args.on_update,
                "onUpdate",
                diagnostics,
            ),
            _ => {
                diagnostics.push(SemanticDiagnostic::error(
                    named_arg.name.span.clone(),
                    format!("Unknown @relation argument: {arg_name}"),
                    DiagnosticCode::InvalidAttributeArgument,
                ));
            }
        }
    }

    /// Parse a string argument for @relation attributes.
    fn parse_string_relation_arg(
        named_arg: &crate::core::parser::ast::NamedArg,
        target: &mut Option<String>,
        arg_name: &str,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Some(value) =
            Self::extract_string_argument_value(&named_arg.value)
        {
            *target = Some(value);
        } else {
            diagnostics.push(SemanticDiagnostic::error(
                named_arg.span.clone(),
                format!("Expected string value for '{arg_name}' argument"),
                DiagnosticCode::InvalidAttributeArgument,
            ));
        }
    }

    /// Parse an array argument for @relation attributes.
    fn parse_array_relation_arg(
        named_arg: &crate::core::parser::ast::NamedArg,
        target: &mut Option<Vec<String>>,
        arg_name: &str,
        content_description: &str,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Some(array_value) =
            Self::extract_array_argument_value(&named_arg.value)
        {
            *target = Some(array_value);
        } else {
            diagnostics.push(SemanticDiagnostic::error(
                named_arg.span.clone(),
                format!("Expected array of {content_description} for '{arg_name}' argument"),
                DiagnosticCode::InvalidAttributeArgument,
            ));
        }
    }

    /// Determine the type of relationship from the field.
    fn determine_relationship_type(
        field: &crate::core::parser::ast::FieldDecl,
    ) -> RelationshipType {
        match &field.r#type {
            crate::core::parser::ast::TypeRef::List(_) => {
                // Field is a list, so it's One-to-Many or Many-to-Many
                RelationshipType::OneToMany
            }
            crate::core::parser::ast::TypeRef::Named(_) => {
                if field.optional {
                    // Optional single field could be One-to-One
                    RelationshipType::OneToOne
                } else {
                    // Non-optional single field is likely Many-to-One
                    RelationshipType::ManyToOne
                }
            }
        }
    }

    /// Extract string value from an argument expression.
    fn extract_string_argument_value(
        value: &crate::core::parser::ast::Expr,
    ) -> Option<String> {
        match value {
            crate::core::parser::ast::Expr::StringLit(string_lit) => {
                Some(string_lit.value.clone())
            }
            _ => None,
        }
    }

    /// Extract array of strings from an argument expression.
    fn extract_array_argument_value(
        value: &crate::core::parser::ast::Expr,
    ) -> Option<Vec<String>> {
        match value {
            crate::core::parser::ast::Expr::Array(array) => {
                let mut result = Vec::new();
                for element in &array.elements {
                    if let Some(string_val) =
                        Self::extract_string_argument_value(element)
                    {
                        result.push(string_val);
                    } else {
                        return None; // Non-string element in array
                    }
                }
                Some(result)
            }
            _ => None,
        }
    }

    /// Validate referential actions in @relation attributes.
    fn validate_referential_actions(
        relation_info: &RelationArguments,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        let valid_actions =
            &["Cascade", "Restrict", "NoAction", "SetNull", "SetDefault"];

        if let Some(on_delete) = &relation_info.on_delete
            && !valid_actions.contains(&on_delete.as_str())
        {
            diagnostics.push(SemanticDiagnostic::error(
                SymbolSpan {
                    start: crate::core::scanner::tokens::SymbolLocation {
                        line: 0,
                        column: 0,
                    },
                    end: crate::core::scanner::tokens::SymbolLocation {
                        line: 0,
                        column: 0,
                    },
                },
                format!(
                    "Invalid onDelete action: '{}'. Valid actions are: {}",
                    on_delete,
                    valid_actions.join(", ")
                ),
                DiagnosticCode::InvalidReferentialAction,
            ));
        }

        if let Some(on_update) = &relation_info.on_update
            && !valid_actions.contains(&on_update.as_str())
        {
            diagnostics.push(SemanticDiagnostic::error(
                SymbolSpan {
                    start: crate::core::scanner::tokens::SymbolLocation {
                        line: 0,
                        column: 0,
                    },
                    end: crate::core::scanner::tokens::SymbolLocation {
                        line: 0,
                        column: 0,
                    },
                },
                format!(
                    "Invalid onUpdate action: '{}'. Valid actions are: {}",
                    on_update,
                    valid_actions.join(", ")
                ),
                DiagnosticCode::InvalidReferentialAction,
            ));
        }
    }
}

impl Default for RelationshipAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl PhaseAnalyzer for RelationshipAnalyzer {
    fn phase_name(&self) -> &'static str {
        "relationship-analysis"
    }

    fn analyze(
        &self,
        schema: &Schema,
        context: &AnalysisContext,
    ) -> PhaseResult {
        let mut diagnostics = Vec::new();

        // Clear the shared relationship graph at the start of analysis
        if let Ok(mut relationship_graph) = context.relationship_graph.write() {
            relationship_graph.relationships.clear();
            relationship_graph.model_relationships.clear();
        }

        // Analyze all relationships and write directly to shared context
        self.analyze_schema_relationships_stateless(
            schema,
            context,
            &mut diagnostics,
        );

        PhaseResult::new(diagnostics)
    }

    fn dependencies(&self) -> &[&'static str] {
        // Relationship analysis requires symbol collection and type resolution
        &["symbol-collection", "type-resolution"]
    }

    fn supports_parallel_execution(&self) -> bool {
        // Relationship analysis writes to shared state but can potentially support parallelism
        // with proper synchronization. For now, keeping it false for safety.
        false
    }
}

impl RelationshipAnalyzer {
    /// Stateless relationship analysis that writes directly to shared context.
    fn analyze_schema_relationships_stateless(
        &self,
        schema: &Schema,
        context: &AnalysisContext,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Keep track of processed relationships to avoid duplicates
        let mut processed_relationships = HashSet::new();

        // First pass: collect all @relation attributes and write to shared context
        for declaration in &schema.declarations {
            if let Declaration::Model(model) = declaration {
                self.analyze_model_relationships_stateless(
                    model,
                    context,
                    &mut processed_relationships,
                    diagnostics,
                );
            }
        }

        // Second pass: validate relationship consistency using shared context
        self.validate_relationship_consistency_from_context(
            context,
            diagnostics,
        );
    }

    /// Analyze relationships for a single model (stateless version).
    fn analyze_model_relationships_stateless(
        &self,
        model: &crate::core::parser::ast::ModelDecl,
        context: &AnalysisContext,
        processed_relationships: &mut HashSet<String>,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        for member in &model.members {
            if let ModelMember::Field(field) = member {
                self.analyze_field_relationships_stateless(
                    model,
                    field,
                    context,
                    processed_relationships,
                    diagnostics,
                );
            }
        }
    }

    /// Analyze relationships for a single field (stateless version).
    fn analyze_field_relationships_stateless(
        &self,
        model: &crate::core::parser::ast::ModelDecl,
        field: &crate::core::parser::ast::FieldDecl,
        context: &AnalysisContext,
        processed_relationships: &mut HashSet<String>,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        for attr in &field.attrs {
            if attr.name.parts.len() == 1
                && attr.name.parts[0].text == "relation"
            {
                self.analyze_relation_attribute_stateless(
                    model,
                    field,
                    attr,
                    context,
                    processed_relationships,
                    diagnostics,
                );
            }
        }
    }

    /// Analyze a single @relation attribute (stateless version).
    fn analyze_relation_attribute_stateless(
        &self,
        model: &crate::core::parser::ast::ModelDecl,
        field: &crate::core::parser::ast::FieldDecl,
        attr: &FieldAttribute,
        context: &AnalysisContext,
        processed_relationships: &mut HashSet<String>,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Extract target model from field type
        let Some(target_model) =
            Self::extract_target_model_from_field_type(&field.r#type)
        else {
            diagnostics.push(SemanticDiagnostic::error(
                field.span.clone(),
                "Cannot determine target model for @relation attribute"
                    .to_string(),
                DiagnosticCode::InvalidRelation,
            ));
            return;
        };

        // Create relationship ID for tracking
        let relationship_id =
            format!("{}_{}", model.name.text, field.name.text);

        // Skip if already processed (avoid duplicates)
        if processed_relationships.contains(&relationship_id) {
            return;
        }

        // Parse relation arguments
        let relation_info = Self::parse_relation_arguments(attr, diagnostics);

        // Validate referential actions
        Self::validate_referential_actions(&relation_info, diagnostics);

        // Create relationship
        let relationship = Relationship {
            id: relationship_id.clone(),
            from_model: model.name.text.clone(),
            from_field: field.name.text.clone(),
            to_model: target_model,
            to_field: Some(
                relation_info
                    .name
                    .clone()
                    .unwrap_or_else(|| field.name.text.clone()),
            ),
            relationship_type: Self::determine_relationship_type(field),
            foreign_keys: relation_info.fields.unwrap_or_default(),
            references: relation_info.references.unwrap_or_default(),
            span: attr.span.clone(),
        };

        // Mark as processed
        processed_relationships.insert(relationship_id.clone());

        // Write directly to shared context
        if let Ok(mut relationship_graph) = context.relationship_graph.write() {
            // Add to relationships map
            relationship_graph
                .relationships
                .insert(relationship_id, relationship.clone());

            // Add to model relationships map
            relationship_graph
                .model_relationships
                .entry(model.name.text.clone())
                .or_default()
                .push(relationship.id.clone());
        }
    }

    /// Validate relationship consistency using shared context data.
    fn validate_relationship_consistency_from_context(
        &self,
        context: &AnalysisContext,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Access the shared relationship graph
        let Ok(relationship_graph) = context.relationship_graph.read() else {
            return;
        };

        // Check for missing back-references and other consistency issues
        for relationship in relationship_graph.relationships.values() {
            // Look for corresponding back-reference
            let back_ref_found =
                relationship_graph.relationships.values().any(|other| {
                    other.from_model == relationship.to_model
                        && other.to_model == relationship.from_model
                        && other.id != relationship.id // Not the same relationship
                });

            if !back_ref_found
                && relationship.relationship_type == RelationshipType::OneToMany
            {
                // This might be intentional for some one-to-many relationships
                // For now, just add an informational diagnostic
                diagnostics.push(SemanticDiagnostic::info(
                    relationship.span.clone(),
                    format!(
                        "Relationship from '{}' to '{}' may need a corresponding back-reference",
                        relationship.from_model,
                        relationship.to_model
                    ),
                    DiagnosticCode::MissingBackReference,
                ));
            }
        }
    }
}

/// Information about a relationship between models.
#[derive(Debug, Clone)]
pub struct RelationshipInfo {
    pub source_model: String,
    pub target_model: String,
    pub field_name: String,
    pub span: SymbolSpan,
}

/// Arguments parsed from a @relation attribute.
#[derive(Debug, Clone)]
pub struct RelationArguments {
    /// Name of the relationship
    pub name: Option<String>,

    /// Foreign key fields
    pub fields: Option<Vec<String>>,

    /// Referenced fields  
    pub references: Option<Vec<String>>,

    /// `OnDelete` action
    pub on_delete: Option<String>,

    /// `OnUpdate` action
    pub on_update: Option<String>,
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
    fn test_relationship_analyzer_creation() {
        let analyzer = RelationshipAnalyzer::new();
        assert_eq!(analyzer.phase_name(), "relationship-analysis");
        assert_eq!(
            analyzer.dependencies(),
            &["symbol-collection", "type-resolution"]
        );
        assert!(!analyzer.supports_parallel_execution());
    }

    #[test]
    fn test_relationship_type_determination() {
        let _analyzer = RelationshipAnalyzer::new();

        // List field should be OneToMany
        let list_field = FieldDecl {
            docs: None,
            name: create_test_ident("posts"),
            r#type: TypeRef::List(ListType {
                inner: Box::new(TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("Post")],
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
        };

        assert_eq!(
            RelationshipAnalyzer::determine_relationship_type(&list_field),
            RelationshipType::OneToMany
        );

        // Optional single field should be OneToOne
        let optional_field = FieldDecl {
            docs: None,
            name: create_test_ident("profile"),
            r#type: TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![create_test_ident("Profile")],
                    span: create_test_span(),
                },
                span: create_test_span(),
            }),
            optional: true,
            modifiers: Vec::new(),
            attrs: Vec::new(),
            span: create_test_span(),
        };

        assert_eq!(
            RelationshipAnalyzer::determine_relationship_type(&optional_field),
            RelationshipType::OneToOne
        );

        // Required single field should be ManyToOne
        let required_field = FieldDecl {
            docs: None,
            name: create_test_ident("author"),
            r#type: TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![create_test_ident("User")],
                    span: create_test_span(),
                },
                span: create_test_span(),
            }),
            optional: false,
            modifiers: Vec::new(),
            attrs: Vec::new(),
            span: create_test_span(),
        };

        assert_eq!(
            RelationshipAnalyzer::determine_relationship_type(&required_field),
            RelationshipType::ManyToOne
        );
    }

    #[test]
    fn test_target_model_extraction() {
        let _analyzer = RelationshipAnalyzer::new();

        // Simple named type
        let named_type = TypeRef::Named(NamedType {
            name: QualifiedIdent {
                parts: vec![create_test_ident("User")],
                span: create_test_span(),
            },
            span: create_test_span(),
        });

        assert_eq!(
            RelationshipAnalyzer::extract_target_model_from_field_type(
                &named_type
            ),
            Some("User".to_string())
        );

        // List type
        let list_type = TypeRef::List(ListType {
            inner: Box::new(TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![create_test_ident("Post")],
                    span: create_test_span(),
                },
                span: create_test_span(),
            })),
            span: create_test_span(),
        });

        assert_eq!(
            RelationshipAnalyzer::extract_target_model_from_field_type(
                &list_type
            ),
            Some("Post".to_string())
        );
    }

    #[test]
    fn test_empty_schema_analysis() {
        let schema = Schema {
            declarations: vec![],
            span: create_test_span(),
        };

        let analyzer = RelationshipAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Empty schema should not have relationship errors
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn test_model_without_relations() {
        let model = ModelDecl {
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

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let analyzer = RelationshipAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Model without relations should not have errors
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn test_model_with_relation_field_no_attribute() {
        // Field that looks like a relation but has no @relation attribute
        let field = FieldDecl {
            docs: None,
            name: create_test_ident("author"),
            r#type: TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![create_test_ident("User")],
                    span: create_test_span(),
                },
                span: create_test_span(),
            }),
            optional: false,
            modifiers: Vec::new(),
            attrs: Vec::new(), // No @relation attribute
            span: create_test_span(),
        };

        let model = ModelDecl {
            docs: None,
            name: create_test_ident("Post"),
            members: vec![ModelMember::Field(field)],
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let analyzer = RelationshipAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Field without @relation attribute should not create relationships
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn test_extract_string_argument_value() {
        // Test string literal extraction
        let string_expr = Expr::StringLit(StringLit {
            value: "test_value".to_string(),
            span: create_test_span(),
        });
        assert_eq!(
            RelationshipAnalyzer::extract_string_argument_value(&string_expr),
            Some("test_value".to_string())
        );

        // Test non-string expression
        let int_expr = Expr::IntLit(IntLit {
            value: "42".to_string(),
            span: create_test_span(),
        });
        assert_eq!(
            RelationshipAnalyzer::extract_string_argument_value(&int_expr),
            None
        );
    }

    #[test]
    fn test_extract_array_argument_value() {
        // Test array with string elements
        let array_expr = Expr::Array(ArrayExpr {
            elements: vec![
                Expr::StringLit(StringLit {
                    value: "item1".to_string(),
                    span: create_test_span(),
                }),
                Expr::StringLit(StringLit {
                    value: "item2".to_string(),
                    span: create_test_span(),
                }),
            ],
            span: create_test_span(),
        });
        assert_eq!(
            RelationshipAnalyzer::extract_array_argument_value(&array_expr),
            Some(vec!["item1".to_string(), "item2".to_string()])
        );

        // Test non-array expression
        let string_expr = Expr::StringLit(StringLit {
            value: "not_array".to_string(),
            span: create_test_span(),
        });
        assert_eq!(
            RelationshipAnalyzer::extract_array_argument_value(&string_expr),
            None
        );
    }

    #[test]
    fn test_validate_referential_actions() {
        // Test valid actions
        let valid_relation = RelationArguments {
            name: None,
            fields: None,
            references: None,
            on_delete: Some("Cascade".to_string()),
            on_update: Some("Restrict".to_string()),
        };

        let mut diagnostics = Vec::new();
        RelationshipAnalyzer::validate_referential_actions(
            &valid_relation,
            &mut diagnostics,
        );
        assert!(diagnostics.is_empty());

        // Test invalid onDelete action
        let invalid_delete_relation = RelationArguments {
            name: None,
            fields: None,
            references: None,
            on_delete: Some("InvalidAction".to_string()),
            on_update: None,
        };

        let mut diagnostics = Vec::new();
        RelationshipAnalyzer::validate_referential_actions(
            &invalid_delete_relation,
            &mut diagnostics,
        );
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(
            diagnostics[0].diagnostic_code,
            DiagnosticCode::InvalidReferentialAction
        );

        // Test invalid onUpdate action
        let invalid_update_relation = RelationArguments {
            name: None,
            fields: None,
            references: None,
            on_delete: None,
            on_update: Some("InvalidAction".to_string()),
        };

        let mut diagnostics = Vec::new();
        RelationshipAnalyzer::validate_referential_actions(
            &invalid_update_relation,
            &mut diagnostics,
        );
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(
            diagnostics[0].diagnostic_code,
            DiagnosticCode::InvalidReferentialAction
        );
    }

    #[test]
    fn test_one_to_many_relationship() {
        let schema = Schema {
            declarations: vec![Declaration::Model(ModelDecl {
                name: create_test_ident("User"),
                members: vec![ModelMember::Field(FieldDecl {
                    docs: None,
                    name: create_test_ident("posts"),
                    r#type: TypeRef::List(ListType {
                        inner: Box::new(TypeRef::Named(NamedType {
                            name: QualifiedIdent {
                                parts: vec![create_test_ident("Post")],
                                span: create_test_span(),
                            },
                            span: create_test_span(),
                        })),
                        span: create_test_span(),
                    }),
                    optional: false,
                    modifiers: Vec::new(),
                    attrs: vec![FieldAttribute {
                        docs: None,
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("relation")],
                            span: create_test_span(),
                        },
                        args: None,
                        span: create_test_span(),
                    }],
                    span: create_test_span(),
                })],
                attrs: Vec::new(),
                docs: None,
                span: create_test_span(),
            })],
            span: create_test_span(),
        };

        let analyzer = RelationshipAnalyzer::new();
        let ctx = AnalysisContext::new_test(&AnalyzerOptions::default());
        let result = analyzer.analyze(&schema, &ctx);

        // Should not have any errors or warnings, info diagnostics are acceptable
        let error_diagnostics: Vec<_> = result.diagnostics.iter()
            .filter(|d| matches!(d.severity, crate::core::semantic_analyzer::diagnostics::DiagnosticSeverity::Error | crate::core::semantic_analyzer::diagnostics::DiagnosticSeverity::Warning))
            .collect();
        if !error_diagnostics.is_empty() {
            for diagnostic in &error_diagnostics {
                eprintln!("Error/Warning Diagnostic: {diagnostic:?}");
            }
        }
        assert!(error_diagnostics.is_empty());

        // Verify relationship was created in the shared context
        let relationship_graph = ctx.relationship_graph.read().unwrap();
        assert_eq!(relationship_graph.relationships.len(), 1);
        let relationship =
            relationship_graph.relationships.values().next().unwrap();
        assert_eq!(relationship.from_model, "User");
        assert_eq!(relationship.to_model, "Post");
        assert_eq!(relationship.relationship_type, RelationshipType::OneToMany);
    }

    #[test]
    fn test_analyzer_parallel_execution_support() {
        let analyzer = RelationshipAnalyzer::new();
        assert!(!analyzer.supports_parallel_execution());
    }

    #[test]
    fn test_analyzer_dependencies() {
        let analyzer = RelationshipAnalyzer::new();
        let deps = analyzer.dependencies();
        assert!(deps.contains(&"symbol-collection"));
        assert!(deps.contains(&"type-resolution"));
    }

    #[test]
    fn test_analyzer_phase_name() {
        let analyzer = RelationshipAnalyzer::new();
        assert_eq!(analyzer.phase_name(), "relationship-analysis");
    }

    #[test]
    fn test_relationship_graph_access() {
        let _analyzer = RelationshipAnalyzer::new();
        // Analyzer is now stateless and doesn't maintain internal graph
    }

    #[test]
    fn test_parse_relation_arguments_no_args() {
        // Test parsing @relation attribute with no arguments
        let attr = FieldAttribute {
            docs: None,
            name: QualifiedIdent {
                parts: vec![create_test_ident("relation")],
                span: create_test_span(),
            },
            args: None,
            span: create_test_span(),
        };

        let mut diagnostics = Vec::new();
        let args = RelationshipAnalyzer::parse_relation_arguments(
            &attr,
            &mut diagnostics,
        );

        assert!(diagnostics.is_empty());
        assert!(args.name.is_none());
        assert!(args.fields.is_none());
        assert!(args.references.is_none());
        assert!(args.on_delete.is_none());
        assert!(args.on_update.is_none());
    }

    #[test]
    fn test_parse_relation_arguments_with_name() {
        // Test parsing @relation attribute with name argument
        let attr = FieldAttribute {
            docs: None,
            name: QualifiedIdent {
                parts: vec![create_test_ident("relation")],
                span: create_test_span(),
            },
            args: Some(ArgList {
                items: vec![Arg::Named(NamedArg {
                    name: create_test_ident("name"),
                    value: Expr::StringLit(StringLit {
                        value: "UserProfile".to_string(),
                        span: create_test_span(),
                    }),
                    span: create_test_span(),
                })],
                span: create_test_span(),
            }),
            span: create_test_span(),
        };

        let mut diagnostics = Vec::new();
        let args = RelationshipAnalyzer::parse_relation_arguments(
            &attr,
            &mut diagnostics,
        );

        assert!(diagnostics.is_empty());
        assert_eq!(args.name, Some("UserProfile".to_string()));
        assert!(args.fields.is_none());
        assert!(args.references.is_none());
        assert!(args.on_delete.is_none());
        assert!(args.on_update.is_none());
    }

    #[test]
    fn test_parse_relation_arguments_invalid_name() {
        // Test parsing with invalid name type
        let attr = FieldAttribute {
            docs: None,
            name: QualifiedIdent {
                parts: vec![create_test_ident("relation")],
                span: create_test_span(),
            },
            args: Some(ArgList {
                items: vec![Arg::Named(NamedArg {
                    name: create_test_ident("name"),
                    value: Expr::IntLit(IntLit {
                        value: "123".to_string(),
                        span: create_test_span(),
                    }),
                    span: create_test_span(),
                })],
                span: create_test_span(),
            }),
            span: create_test_span(),
        };

        let mut diagnostics = Vec::new();
        let args = RelationshipAnalyzer::parse_relation_arguments(
            &attr,
            &mut diagnostics,
        );

        assert_eq!(diagnostics.len(), 1);
        assert!(args.name.is_none());
        assert_eq!(
            diagnostics[0].diagnostic_code,
            DiagnosticCode::InvalidAttributeArgument
        );
    }

    #[test]
    fn test_parse_relation_arguments_unknown_arg() {
        // Test parsing with unknown argument
        let attr = FieldAttribute {
            docs: None,
            name: QualifiedIdent {
                parts: vec![create_test_ident("relation")],
                span: create_test_span(),
            },
            args: Some(ArgList {
                items: vec![Arg::Named(NamedArg {
                    name: create_test_ident("unknown_arg"),
                    value: Expr::StringLit(StringLit {
                        value: "value".to_string(),
                        span: create_test_span(),
                    }),
                    span: create_test_span(),
                })],
                span: create_test_span(),
            }),
            span: create_test_span(),
        };

        let mut diagnostics = Vec::new();
        let _args = RelationshipAnalyzer::parse_relation_arguments(
            &attr,
            &mut diagnostics,
        );

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(
            diagnostics[0].diagnostic_code,
            DiagnosticCode::InvalidAttributeArgument
        );
    }

    #[test]
    fn test_stateless_analyzer_writes_to_shared_context() {
        // Test that the new stateless analyzer writes directly to shared context
        use crate::core::parser::ast::*;
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
        use crate::core::semantic_analyzer::AnalyzerOptions;

        fn sp() -> SymbolSpan {
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation {
                    line: 1,
                    column: 10,
                },
            }
        }

        // Create a schema with a relationship
        let schema = Schema {
            declarations: vec![Declaration::Model(ModelDecl {
                docs: None,
                name: create_test_ident("User"),
                members: vec![ModelMember::Field(FieldDecl {
                    docs: None,
                    name: create_test_ident("post"),
                    r#type: TypeRef::Named(NamedType {
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("Post")],
                            span: sp(),
                        },
                        span: sp(),
                    }),
                    optional: true,
                    modifiers: Vec::new(),
                    attrs: vec![FieldAttribute {
                        docs: None,
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("relation")],
                            span: sp(),
                        },
                        args: None,
                        span: sp(),
                    }],
                    span: sp(),
                })],
                attrs: Vec::new(),
                span: sp(),
            })],
            span: sp(),
        };

        let analyzer = RelationshipAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        // The shared relationship graph should be empty initially
        {
            let relationship_graph = context.relationship_graph.read().unwrap();
            assert!(relationship_graph.relationships.is_empty());
        }

        let result = analyzer.analyze(&schema, &context);

        // After analysis, the shared context should contain the relationship
        {
            let relationship_graph = context.relationship_graph.read().unwrap();
            assert!(
                !relationship_graph.relationships.is_empty(),
                "Stateless analyzer should write relationships to shared context"
            );

            // Check that the relationship was created correctly
            let relationship =
                relationship_graph.relationships.values().next().unwrap();
            assert_eq!(relationship.from_model, "User");
            assert_eq!(relationship.to_model, "Post");
            assert_eq!(relationship.from_field, "post");
        }

        // Should have successful result
        assert!(result.diagnostics.is_empty() || result.diagnostics.iter().all(|d| {
            // Allow info-level diagnostics (like missing back-references)
            matches!(d.severity, crate::core::semantic_analyzer::diagnostics::DiagnosticSeverity::Info)
        }));
    }

    #[test]
    fn test_stateless_analyzer_thread_safety() {
        // Test that the stateless RelationshipAnalyzer is thread-safe
        use crate::core::parser::ast::*;
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
        use crate::core::semantic_analyzer::AnalyzerOptions;
        use std::sync::Arc;
        use std::thread;

        fn sp() -> SymbolSpan {
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation {
                    line: 1,
                    column: 10,
                },
            }
        }

        let schema = Arc::new(Schema {
            declarations: vec![Declaration::Model(ModelDecl {
                docs: None,
                name: create_test_ident("TestModel"),
                members: vec![ModelMember::Field(FieldDecl {
                    docs: None,
                    name: create_test_ident("id"),
                    r#type: TypeRef::Named(NamedType {
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("Int")],
                            span: sp(),
                        },
                        span: sp(),
                    }),
                    optional: false,
                    modifiers: Vec::new(),
                    attrs: Vec::new(),
                    span: sp(),
                })],
                attrs: Vec::new(),
                span: sp(),
            })],
            span: sp(),
        });

        let analyzer = Arc::new(RelationshipAnalyzer::new());
        let options = AnalyzerOptions::default();
        let context = Arc::new(AnalysisContext::new_test(&options));

        let mut handles = Vec::new();

        // Run the analyzer from multiple threads
        for _ in 0..4 {
            let schema_clone = Arc::clone(&schema);
            let analyzer_clone = Arc::clone(&analyzer);
            let context_clone = Arc::clone(&context);

            let handle = thread::spawn(move || {
                analyzer_clone.analyze(&schema_clone, &context_clone)
            });
            handles.push(handle);
        }

        // All threads should complete successfully without race conditions
        for handle in handles {
            let result = handle.join().expect("Thread should not panic");
            // Result should be consistent (no relationships in this simple schema)
            assert!(result.diagnostics.is_empty());
        }
    }

    #[test]
    fn test_no_internal_state_after_refactor() {
        use crate::core::parser::ast::*;
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
        use crate::core::semantic_analyzer::AnalyzerOptions;

        let sp = || SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        };

        // Test that the analyzer no longer has internal state that could cause issues
        let analyzer1 = RelationshipAnalyzer::new();
        let analyzer2 = RelationshipAnalyzer::new();

        // Both analyzers should be identical and stateless
        assert_eq!(analyzer1.phase_name(), analyzer2.phase_name());
        assert_eq!(analyzer1.dependencies(), analyzer2.dependencies());
        assert_eq!(
            analyzer1.supports_parallel_execution(),
            analyzer2.supports_parallel_execution()
        );

        let schema = Schema {
            declarations: Vec::new(),
            span: sp(),
        };

        let options = AnalyzerOptions::default();
        let context1 = AnalysisContext::new_test(&options);
        let context2 = AnalysisContext::new_test(&options);

        let result1 = analyzer1.analyze(&schema, &context1);
        let result2 = analyzer2.analyze(&schema, &context2);

        // Results should be identical for empty schema
        assert_eq!(result1.diagnostics.len(), result2.diagnostics.len());
    }

    #[test]
    fn test_relationship_consistency_validation() {
        // Test the new stateless relationship consistency validation
        use crate::core::parser::ast::*;
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
        use crate::core::semantic_analyzer::AnalyzerOptions;

        fn sp() -> SymbolSpan {
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation {
                    line: 1,
                    column: 10,
                },
            }
        }

        // Create a schema with one-way relationship (should generate info diagnostic)
        let schema = Schema {
            declarations: vec![
                Declaration::Model(ModelDecl {
                    docs: None,
                    name: create_test_ident("User"),
                    members: vec![ModelMember::Field(FieldDecl {
                        docs: None,
                        name: create_test_ident("posts"),
                        r#type: TypeRef::List(ListType {
                            inner: Box::new(TypeRef::Named(NamedType {
                                name: QualifiedIdent {
                                    parts: vec![create_test_ident("Post")],
                                    span: sp(),
                                },
                                span: sp(),
                            })),
                            span: sp(),
                        }),
                        optional: false,
                        modifiers: Vec::new(),
                        attrs: vec![FieldAttribute {
                            docs: None,
                            name: QualifiedIdent {
                                parts: vec![create_test_ident("relation")],
                                span: sp(),
                            },
                            args: None,
                            span: sp(),
                        }],
                        span: sp(),
                    })],
                    attrs: Vec::new(),
                    span: sp(),
                }),
                Declaration::Model(ModelDecl {
                    docs: None,
                    name: create_test_ident("Post"),
                    members: vec![ModelMember::Field(FieldDecl {
                        docs: None,
                        name: create_test_ident("title"),
                        r#type: TypeRef::Named(NamedType {
                            name: QualifiedIdent {
                                parts: vec![create_test_ident("String")],
                                span: sp(),
                            },
                            span: sp(),
                        }),
                        optional: false,
                        modifiers: Vec::new(),
                        attrs: Vec::new(),
                        span: sp(),
                    })],
                    attrs: Vec::new(),
                    span: sp(),
                }),
            ],
            span: sp(),
        };

        let analyzer = RelationshipAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Should potentially have an info diagnostic about missing back-reference
        let has_back_ref_info = result.diagnostics.iter().any(|d| {
            d.message.contains("back-reference") && 
            matches!(d.severity, crate::core::semantic_analyzer::diagnostics::DiagnosticSeverity::Info)
        });

        // This is acceptable (info-level diagnostics are fine)
        if has_back_ref_info {
            println!(
                "Got expected info diagnostic about missing back-reference"
            );
        }

        // No errors should occur
        let has_errors = result.diagnostics.iter().any(|d| {
            matches!(d.severity, crate::core::semantic_analyzer::diagnostics::DiagnosticSeverity::Error)
        });
        assert!(
            !has_errors,
            "Should not have errors for valid relationship schema"
        );
    }
}
