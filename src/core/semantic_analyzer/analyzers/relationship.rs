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
            "onDelete" => Self::parse_spanned_string_relation_arg(
                named_arg,
                &mut args.on_delete,
                "onDelete",
                diagnostics,
            ),
            "onUpdate" => Self::parse_spanned_string_relation_arg(
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

    /// Parse a string argument for @relation attributes (plain string target).
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

    /// Parse a string argument for @relation attributes (spanned target).
    fn parse_spanned_string_relation_arg(
        named_arg: &crate::core::parser::ast::NamedArg,
        target: &mut Option<ArgWithSpan<String>>,
        arg_name: &str,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Some(value) =
            Self::extract_string_argument_value(&named_arg.value)
        {
            *target = Some(ArgWithSpan {
                value,
                span: named_arg.span.clone(),
            });
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
            && !valid_actions.contains(&on_delete.value.as_str())
        {
            diagnostics.push(SemanticDiagnostic::error(
                on_delete.span.clone(),
                format!(
                    "Invalid onDelete action: '{}'. Valid actions are: {}",
                    on_delete.value,
                    valid_actions.join(", ")
                ),
                DiagnosticCode::InvalidReferentialAction,
            ));
        }

        if let Some(on_update) = &relation_info.on_update
            && !valid_actions.contains(&on_update.value.as_str())
        {
            diagnostics.push(SemanticDiagnostic::error(
                on_update.span.clone(),
                format!(
                    "Invalid onUpdate action: '{}'. Valid actions are: {}",
                    on_update.value,
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
        Self::analyze_schema_relationships_stateless(
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
        schema: &Schema,
        context: &AnalysisContext,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Keep track of processed relationships to avoid duplicates
        let mut processed_relationships = HashSet::new();

        // First pass: collect all @relation attributes and write to shared context
        for declaration in &schema.declarations {
            if let Declaration::Model(model) = declaration {
                Self::analyze_model_relationships_stateless(
                    model,
                    context,
                    &mut processed_relationships,
                    diagnostics,
                );
            }
        }

        // Second pass: validate relationship consistency using shared context
        Self::validate_relationship_consistency_from_context(
            context,
            diagnostics,
        );
    }

    /// Analyze relationships for a single model (stateless version).
    fn analyze_model_relationships_stateless(
        model: &crate::core::parser::ast::ModelDecl,
        context: &AnalysisContext,
        processed_relationships: &mut HashSet<String>,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        for member in &model.members {
            if let ModelMember::Field(field) = member {
                Self::analyze_field_relationships_stateless(
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
                Self::analyze_relation_attribute_stateless(
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
    pub on_delete: Option<ArgWithSpan<String>>,

    /// `OnUpdate` action
    pub on_update: Option<ArgWithSpan<String>>,
}

#[derive(Debug, Clone)]
pub struct ArgWithSpan<T> {
    value: T,
    span: SymbolSpan,
}
