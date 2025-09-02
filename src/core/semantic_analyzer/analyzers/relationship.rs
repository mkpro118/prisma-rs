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
    context::{AnalysisContext, PhaseResult},
    diagnostics::{DiagnosticCode, SemanticDiagnostic},
    traits::PhaseAnalyzer,
};
use std::collections::{HashMap, HashSet};

/// Represents a relationship between two models.
#[derive(Debug, Clone)]
pub struct Relationship {
    /// ID of the relationship
    pub id: String,

    /// Source model name
    pub from_model: String,

    /// Source field name
    pub from_field: String,

    /// Target model name  
    pub to_model: String,

    /// Target field name (if specified)
    pub to_field: Option<String>,

    /// Type of relationship
    pub relationship_type: RelationshipType,

    /// Foreign key fields
    pub foreign_keys: Vec<String>,

    /// Referenced fields
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

/// Analyzer responsible for validating model relationships.
///
/// This phase builds on the symbol collection and type resolution phases to validate:
/// - All `@relation` attributes are properly formed
/// - Back-references exist for bidirectional relationships
/// - Foreign key fields exist and have correct types
/// - No conflicting relationship definitions
/// - Proper naming of relationship fields
///
/// The relationship analyzer builds a comprehensive relationship graph that can be
/// used by subsequent phases for additional validation.
pub struct RelationshipAnalyzer {
    /// Graph of all relationships found in the schema
    relationship_graph: HashMap<String, Vec<Relationship>>,

    /// Track processed relationships to avoid duplicates
    processed_relationships: HashSet<String>,
}

impl RelationshipAnalyzer {
    /// Create a new relationship analyzer.
    #[must_use]
    pub fn new() -> Self {
        Self {
            relationship_graph: HashMap::new(),
            processed_relationships: HashSet::new(),
        }
    }

    /// Analyze all relationships in the schema.
    fn analyze_schema_relationships(
        &mut self,
        schema: &Schema,
        _context: &AnalysisContext,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // First pass: collect all @relation attributes
        for declaration in &schema.declarations {
            if let Declaration::Model(model) = declaration {
                self.analyze_model_relationships(model, diagnostics);
            }
        }

        // Second pass: validate relationship consistency
        self.validate_relationship_consistency(diagnostics);
    }

    /// Analyze relationships for a single model.
    fn analyze_model_relationships(
        &mut self,
        model: &crate::core::parser::ast::ModelDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        for member in &model.members {
            if let ModelMember::Field(field) = member {
                self.analyze_field_relationships(model, field, diagnostics);
            }
        }
    }

    /// Analyze relationships for a single field.
    fn analyze_field_relationships(
        &mut self,
        model: &crate::core::parser::ast::ModelDecl,
        field: &crate::core::parser::ast::FieldDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        for attr in &field.attrs {
            if attr.name.parts.len() == 1
                && attr.name.parts[0].text == "relation"
            {
                self.analyze_relation_attribute(
                    model,
                    field,
                    attr,
                    diagnostics,
                );
            }
        }
    }

    /// Analyze a single `@relation` attribute.
    fn analyze_relation_attribute(
        &mut self,
        model: &crate::core::parser::ast::ModelDecl,
        field: &crate::core::parser::ast::FieldDecl,
        attr: &FieldAttribute,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Extract target model from field type
        let target_model =
            Self::extract_target_model_from_field_type(&field.r#type);

        let Some(target_model) = target_model else {
            diagnostics.push(SemanticDiagnostic::error(
                field.span.clone(),
                "Cannot determine target model for @relation attribute"
                    .to_string(),
                DiagnosticCode::InvalidRelation,
            ));
            return;
        };

        // Parse relation arguments
        let relation_info = Self::parse_relation_arguments(attr, diagnostics);

        // Create relationship ID for tracking
        let relationship_id =
            format!("{}_{}", model.name.text, field.name.text);

        // Skip if already processed (avoid duplicates)
        if self.processed_relationships.contains(&relationship_id) {
            return;
        }

        // Validate referential actions first
        Self::validate_referential_actions(&relation_info, diagnostics);

        // Create relationship
        let relationship = Relationship {
            id: relationship_id.clone(),
            from_model: model.name.text.clone(),
            from_field: field.name.text.clone(),
            to_model: target_model,
            to_field: relation_info.name.clone(), // Use relation name if specified
            relationship_type: Self::determine_relationship_type(field),
            foreign_keys: relation_info.fields.unwrap_or_default(),
            references: relation_info.references.unwrap_or_default(),
        };

        // Track as processed
        self.processed_relationships.insert(relationship_id);

        // Add to graph
        self.relationship_graph
            .entry(model.name.text.clone())
            .or_default()
            .push(relationship);
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

    /// Validate consistency of all relationships.
    fn validate_relationship_consistency(
        &self,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Check for missing back-references
        self.validate_back_references(diagnostics);

        // Check for conflicting relationships
        self.validate_relationship_conflicts(diagnostics);

        // Check foreign key consistency
        self.validate_foreign_key_consistency(diagnostics);
    }

    /// Validate that relationships have proper back-references.
    fn validate_back_references(
        &self,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // For each relationship, check if the target model has a back-reference
        for (from_model, relationships) in &self.relationship_graph {
            for relationship in relationships {
                // Skip self-referential relations for now
                if relationship.from_model == relationship.to_model {
                    continue;
                }

                // Check if target model has a relationship back to source
                if let Some(target_relationships) =
                    self.relationship_graph.get(&relationship.to_model)
                {
                    let has_back_reference =
                        target_relationships.iter().any(|target_rel| {
                            target_rel.to_model == relationship.from_model
                        });

                    // For explicit bidirectional relations (those with 'name' parameter),
                    // we should always have a back-reference
                    if !relationship.foreign_keys.is_empty()
                        && !has_back_reference
                    {
                        // This is likely a unidirectional relation with foreign keys,
                        // which should have a back-reference
                        diagnostics.push(
                            SemanticDiagnostic::error(
                                SymbolSpan {
                                    start: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                    end: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                },
                                format!(
                                    "Relationship from '{}' to '{}' is missing a back-reference in model '{}'",
                                    from_model, relationship.to_model, relationship.to_model
                                ),
                                DiagnosticCode::MissingBackReference,
                            )
                            .with_suggestion(
                                format!(
                                    "Add a field in model '{}' that references '{}'",
                                    relationship.to_model, from_model
                                )
                            ),
                        );
                    }
                }
            }
        }
    }

    /// Validate that there are no conflicting relationship definitions.
    fn validate_relationship_conflicts(
        &self,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Check for multiple relationships between the same pair of models
        // with potentially conflicting configurations
        for relationships in self.relationship_graph.values() {
            // Group relationships by target model
            let mut target_groups: HashMap<&String, Vec<&Relationship>> =
                HashMap::new();
            for relationship in relationships {
                target_groups
                    .entry(&relationship.to_model)
                    .or_default()
                    .push(relationship);
            }

            // Check each group for conflicts
            for (target_model, group) in target_groups {
                if group.len() > 1 {
                    // Multiple relationships to same target - check for conflicts
                    for i in 0..group.len() {
                        for j in i + 1..group.len() {
                            let rel1 = group[i];
                            let rel2 = group[j];

                            // Check for conflicting foreign keys
                            if !rel1.foreign_keys.is_empty()
                                && !rel2.foreign_keys.is_empty()
                            {
                                let has_overlapping_keys = rel1
                                    .foreign_keys
                                    .iter()
                                    .any(|key| rel2.foreign_keys.contains(key));

                                if has_overlapping_keys {
                                    diagnostics.push(
                                        SemanticDiagnostic::error(
                                            SymbolSpan {
                                                start: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                                end: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                            },
                                            format!(
                                                "Conflicting relationships from '{}' to '{}': fields '{}' and '{}' share foreign keys",
                                                rel1.from_model, target_model, rel1.from_field, rel2.from_field
                                            ),
                                            DiagnosticCode::ConflictingRelations,
                                        )
                                        .with_suggestion(
                                            "Use different foreign key fields for each relationship".to_string()
                                        ),
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Validate that foreign keys are consistent.
    fn validate_foreign_key_consistency(
        &self,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        for relationships in self.relationship_graph.values() {
            for relationship in relationships {
                // Validate that foreign keys and references have matching lengths
                if !relationship.foreign_keys.is_empty()
                    && !relationship.references.is_empty()
                    && relationship.foreign_keys.len()
                        != relationship.references.len()
                {
                    diagnostics.push(
                            SemanticDiagnostic::error(
                                SymbolSpan {
                                    start: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                    end: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                },
                                format!(
                                    "Relationship '{}' has mismatched foreign keys and references: {} fields vs {} references",
                                    relationship.id,
                                    relationship.foreign_keys.len(),
                                    relationship.references.len()
                                ),
                                DiagnosticCode::InvalidRelation,
                            )
                            .with_suggestion(
                                "Ensure the 'fields' and 'references' arrays have the same number of items".to_string()
                            ),
                        );
                }

                // Validate that foreign keys are specified for Many-to-One relationships
                if matches!(
                    relationship.relationship_type,
                    RelationshipType::ManyToOne
                ) && relationship.foreign_keys.is_empty()
                {
                    diagnostics.push(
                            SemanticDiagnostic::error(
                                SymbolSpan {
                                    start: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                    end: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                },
                                format!(
                                    "Many-to-one relationship '{}' requires foreign key fields to be specified",
                                    relationship.id
                                ),
                                DiagnosticCode::InvalidRelation,
                            )
                            .with_suggestion(
                                "Add 'fields' and 'references' to the @relation attribute".to_string()
                            ),
                        );
                }

                // Validate one-to-many relationships don't have foreign keys
                if matches!(
                    relationship.relationship_type,
                    RelationshipType::OneToMany
                ) && !relationship.foreign_keys.is_empty()
                {
                    diagnostics.push(
                            SemanticDiagnostic::warning(
                                SymbolSpan {
                                    start: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                    end: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                },
                                format!(
                                    "One-to-many relationship '{}' should not specify foreign key fields",
                                    relationship.id
                                ),
                                DiagnosticCode::InvalidRelation,
                            )
                            .with_suggestion(
                                "Remove 'fields' and 'references' from the @relation attribute".to_string()
                            ),
                        );
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

    /// Get the relationship graph.
    #[must_use]
    pub fn relationship_graph(&self) -> &HashMap<String, Vec<Relationship>> {
        &self.relationship_graph
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
        &mut self,
        schema: &Schema,
        context: &mut AnalysisContext,
    ) -> PhaseResult {
        let mut diagnostics = Vec::new();

        // Analyze all relationships in the schema
        self.analyze_schema_relationships(schema, context, &mut diagnostics);

        PhaseResult::new(diagnostics)
    }

    fn dependencies(&self) -> &[&'static str] {
        // Relationship analysis requires symbol collection and type resolution
        &["symbol-collection", "type-resolution"]
    }

    fn supports_parallel_execution(&self) -> bool {
        // Relationship analysis modifies shared state, so no parallelism
        false
    }
}

/// Arguments parsed from a @relation attribute.
#[derive(Debug, Clone)]
struct RelationArguments {
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
        assert!(analyzer.relationship_graph().is_empty());
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

        let mut analyzer = RelationshipAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Empty schema should not have relationship errors
        assert!(result.diagnostics.is_empty());
        assert!(analyzer.relationship_graph().is_empty());
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

        let mut analyzer = RelationshipAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Model without relations should not have errors
        assert!(result.diagnostics.is_empty());
        assert!(analyzer.relationship_graph().is_empty());
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

        let mut analyzer = RelationshipAnalyzer::new();
        let options = AnalyzerOptions::default();
        let mut context = AnalysisContext::new(&options);

        let result = analyzer.analyze(&schema, &mut context);

        // Field without @relation attribute should not create relationships
        assert!(result.diagnostics.is_empty());
        assert!(analyzer.relationship_graph().is_empty());
    }
}
