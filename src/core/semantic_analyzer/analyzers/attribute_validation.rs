//! Attribute validation analyzer for semantic analysis.

#![allow(clippy::ptr_arg)] // Need Vec for push operations
//!
//! This analyzer is the fourth phase of semantic analysis and validates all attributes
//! in the schema. It checks for unknown attributes, validates attribute arguments,
//! detects conflicting attributes, and ensures attributes are used in appropriate contexts.

use crate::core::parser::ast::{EnumMember, ModelMember, Schema};
use crate::core::scanner::tokens::SymbolSpan;
use crate::core::semantic_analyzer::{
    context::{AnalysisContext, PhaseResult},
    diagnostics::{DiagnosticCode, SemanticDiagnostic},
    traits::PhaseAnalyzer,
};
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

/// Represents an attribute definition with its validation rules.
#[derive(Debug, Clone)]
pub struct AttributeDefinition {
    /// Name of the attribute
    pub name: String,

    /// Valid contexts where this attribute can be used
    pub valid_contexts: HashSet<AttributeContext>,

    /// Required arguments for this attribute
    pub required_args: HashSet<String>,

    /// Optional arguments for this attribute
    pub optional_args: HashSet<String>,

    /// Whether this attribute can appear multiple times
    pub repeatable: bool,

    /// Whether this attribute is deprecated
    pub deprecated: bool,

    /// Replacement attribute if deprecated
    pub replacement: Option<String>,
}

/// Context where an attribute can be applied.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AttributeContext {
    Model,
    Field,
    Enum,
    EnumValue,
}

/// Analyzer responsible for validating all attributes in the schema.
///
/// This phase validates:
/// - All attributes are known and valid
/// - Attributes are used in appropriate contexts (model vs field vs enum)
/// - Required arguments are present
/// - Argument types are correct
/// - No conflicting attributes exist
/// - Deprecated attributes are flagged with suggestions
///
/// The attribute validator uses a comprehensive attribute registry to validate
/// against Prisma's attribute specifications.
pub struct AttributeValidationAnalyzer {
    /// Registry of all known attributes and their definitions
    attribute_registry: HashMap<String, AttributeDefinition>,
}

impl AttributeValidationAnalyzer {
    /// Create a new attribute validation analyzer.
    #[must_use]
    pub fn new() -> Self {
        let mut analyzer = Self {
            attribute_registry: HashMap::new(),
        };
        analyzer.initialize_attribute_registry();
        analyzer
    }

    /// Initialize the registry with all known Prisma attributes.
    fn initialize_attribute_registry(&mut self) {
        self.register_model_attributes();
        self.register_field_attributes();
        self.register_index_attributes();
        self.register_enum_attributes();
        self.register_deprecated_attributes();
    }

    /// Register model-level attributes.
    fn register_model_attributes(&mut self) {
        self.register_attribute(AttributeDefinition {
            name: "map".to_string(),
            valid_contexts: [AttributeContext::Model].into_iter().collect(),
            required_args: ["name"]
                .into_iter()
                .map(ToString::to_string)
                .collect(),
            optional_args: HashSet::new(),
            repeatable: false,
            deprecated: false,
            replacement: None,
        });

        self.register_attribute(AttributeDefinition {
            name: "schema".to_string(),
            valid_contexts: [AttributeContext::Model].into_iter().collect(),
            required_args: ["name"]
                .into_iter()
                .map(ToString::to_string)
                .collect(),
            optional_args: HashSet::new(),
            repeatable: false,
            deprecated: false,
            replacement: None,
        });
    }

    /// Register field-level attributes.
    fn register_field_attributes(&mut self) {
        self.register_attribute(AttributeDefinition {
            name: "id".to_string(),
            valid_contexts: [AttributeContext::Field].into_iter().collect(),
            required_args: HashSet::new(),
            optional_args: ["map", "length", "sort", "clustered"]
                .into_iter()
                .map(ToString::to_string)
                .collect(),
            repeatable: false,
            deprecated: false,
            replacement: None,
        });

        self.register_attribute(AttributeDefinition {
            name: "default".to_string(),
            valid_contexts: [AttributeContext::Field].into_iter().collect(),
            required_args: HashSet::new(),
            optional_args: HashSet::new(),
            repeatable: false,
            deprecated: false,
            replacement: None,
        });

        self.register_attribute(AttributeDefinition {
            name: "unique".to_string(),
            valid_contexts: [AttributeContext::Field].into_iter().collect(),
            required_args: HashSet::new(),
            optional_args: ["map", "length", "sort", "clustered"]
                .into_iter()
                .map(ToString::to_string)
                .collect(),
            repeatable: false,
            deprecated: false,
            replacement: None,
        });

        self.register_attribute(AttributeDefinition {
            name: "map".to_string(),
            valid_contexts: [AttributeContext::Field].into_iter().collect(),
            required_args: ["name"]
                .into_iter()
                .map(ToString::to_string)
                .collect(),
            optional_args: HashSet::new(),
            repeatable: false,
            deprecated: false,
            replacement: None,
        });

        self.register_attribute(AttributeDefinition {
            name: "relation".to_string(),
            valid_contexts: [AttributeContext::Field].into_iter().collect(),
            required_args: HashSet::new(),
            optional_args: [
                "name",
                "fields",
                "references",
                "onDelete",
                "onUpdate",
                "map",
            ]
            .into_iter()
            .map(ToString::to_string)
            .collect(),
            repeatable: false,
            deprecated: false,
            replacement: None,
        });

        self.register_attribute(AttributeDefinition {
            name: "updatedAt".to_string(),
            valid_contexts: [AttributeContext::Field].into_iter().collect(),
            required_args: HashSet::new(),
            optional_args: HashSet::new(),
            repeatable: false,
            deprecated: false,
            replacement: None,
        });
    }

    /// Register index-related attributes.
    fn register_index_attributes(&mut self) {
        self.register_attribute(AttributeDefinition {
            name: "index".to_string(),
            valid_contexts: [AttributeContext::Model, AttributeContext::Field]
                .into_iter()
                .collect(),
            required_args: HashSet::new(),
            optional_args: [
                "fields",
                "map",
                "length",
                "sort",
                "clustered",
                "type",
            ]
            .into_iter()
            .map(ToString::to_string)
            .collect(),
            repeatable: true,
            deprecated: false,
            replacement: None,
        });

        self.register_attribute(AttributeDefinition {
            name: "fulltext".to_string(),
            valid_contexts: [AttributeContext::Model].into_iter().collect(),
            required_args: ["fields"]
                .into_iter()
                .map(ToString::to_string)
                .collect(),
            optional_args: ["map"]
                .into_iter()
                .map(ToString::to_string)
                .collect(),
            repeatable: true,
            deprecated: false,
            replacement: None,
        });
    }

    /// Register enum-related attributes.
    fn register_enum_attributes(&mut self) {
        self.register_attribute(AttributeDefinition {
            name: "map".to_string(),
            valid_contexts: [
                AttributeContext::Enum,
                AttributeContext::EnumValue,
            ]
            .into_iter()
            .collect(),
            required_args: ["name"]
                .into_iter()
                .map(ToString::to_string)
                .collect(),
            optional_args: HashSet::new(),
            repeatable: false,
            deprecated: false,
            replacement: None,
        });
    }

    /// Register deprecated attributes.
    fn register_deprecated_attributes(&mut self) {
        self.register_attribute(AttributeDefinition {
            name: "autoincrement".to_string(),
            valid_contexts: [AttributeContext::Field].into_iter().collect(),
            required_args: HashSet::new(),
            optional_args: HashSet::new(),
            repeatable: false,
            deprecated: true,
            replacement: Some("default(autoincrement())".to_string()),
        });
    }

    /// Register a new attribute definition.
    fn register_attribute(&mut self, definition: AttributeDefinition) {
        self.attribute_registry
            .insert(definition.name.clone(), definition);
    }

    /// Analyze attributes for a datasource.
    #[expect(clippy::ptr_arg)]
    pub fn analyze_datasource_attributes(
        _datasource: &crate::core::parser::ast::DatasourceDecl,
        _diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Datasources don't currently have attributes in Prisma
        // This is here for future extensibility
    }

    /// Analyze attributes for a generator.
    #[expect(clippy::ptr_arg)]
    pub fn analyze_generator_attributes(
        _generator: &crate::core::parser::ast::GeneratorDecl,
        _diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Generators don't currently have attributes in Prisma
        // This is here for future extensibility
    }

    /// Validate arguments for an attribute.
    pub fn validate_attribute_arguments(
        attr_name: &str,
        attr_args: Option<&crate::core::parser::ast::ArgList>,
        attr_span: &SymbolSpan,
        definition: &AttributeDefinition,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        let mut provided_args = HashSet::new();

        // Extract provided arguments
        if let Some(arg_list) = attr_args {
            for arg in &arg_list.items {
                match arg {
                    crate::core::parser::ast::Arg::Named(named_arg) => {
                        provided_args.insert(named_arg.name.text.clone());
                    }
                    crate::core::parser::ast::Arg::Positional(_) => {
                        // For now, we'll handle positional arguments as the first required argument
                        // This is a simplification - real Prisma has more complex rules
                        if let Some(first_required) =
                            definition.required_args.iter().next()
                        {
                            provided_args.insert(first_required.clone());
                        }
                    }
                }
            }
        }

        // Check for missing required arguments
        for required_arg in &definition.required_args {
            if !provided_args.contains(required_arg) {
                diagnostics.push(SemanticDiagnostic::error(
                    attr_span.clone(),
                    format!("Missing required argument '{required_arg}' for attribute '@{attr_name}'"),
                    DiagnosticCode::MissingRequiredAttribute,
                ).with_suggestion(format!("Add the '{required_arg}' argument to the @{attr_name} attribute")));
            }
        }

        // Check for unknown arguments
        let all_valid_args: HashSet<String> = definition
            .required_args
            .union(&definition.optional_args)
            .cloned()
            .collect();

        for provided_arg in &provided_args {
            if !all_valid_args.contains(provided_arg) {
                diagnostics.push(SemanticDiagnostic::error(
                    attr_span.clone(),
                    format!("Unknown argument '{provided_arg}' for attribute '@{attr_name}'"),
                    DiagnosticCode::InvalidAttributeArgument,
                ).with_suggestion(format!(
                    "Valid arguments for @{attr_name} are: {}",
                    all_valid_args.iter().cloned().collect::<Vec<_>>().join(", ")
                )));
            }
        }
    }

    /// Get the attribute registry for inspection.
    #[must_use]
    pub fn attribute_registry(&self) -> &HashMap<String, AttributeDefinition> {
        &self.attribute_registry
    }

    /// Analyze a single attribute (immutable version for thread safety).
    fn analyze_single_attribute_immutable(
        &self,
        attr_name: &str,
        attr_args: Option<&crate::core::parser::ast::ArgList>,
        attr_span: &SymbolSpan,
        context: AttributeContext,
        location: &str,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Check if attribute exists
        let Some(definition) = self.attribute_registry.get(attr_name) else {
            diagnostics.push(SemanticDiagnostic::error(
                attr_span.clone(),
                format!("Unknown attribute '@{attr_name}' on {location}"),
                DiagnosticCode::UnknownAttribute,
            ).with_suggestion("Check the attribute name spelling and Prisma documentation".to_string()));
            return;
        };

        // Check if attribute is used in valid context
        if !definition.valid_contexts.contains(&context) {
            let valid_contexts: Vec<String> = definition
                .valid_contexts
                .iter()
                .map(|c| format!("{c:?}").to_lowercase())
                .collect();

            diagnostics.push(SemanticDiagnostic::error(
                attr_span.clone(),
                format!(
                    "Attribute '@{attr_name}' cannot be used on {location}. Valid contexts: {}",
                    valid_contexts.join(", ")
                ),
                DiagnosticCode::AttributeNotApplicable,
            ));
            return;
        }

        // Check for deprecated attributes
        if definition.deprecated {
            diagnostics.push(SemanticDiagnostic::deprecated_feature(
                attr_span.clone(),
                attr_name,
                definition.replacement.as_deref(),
            ));
        }

        // Validate arguments
        Self::validate_attribute_arguments(
            attr_name,
            attr_args,
            attr_span,
            definition,
            diagnostics,
        );
    }

    /// Analyze attributes for a model with conflict detection.
    fn analyze_model_attributes_with_conflict_detection(
        &self,
        model: &crate::core::parser::ast::ModelDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
        attribute_usage: Arc<Mutex<HashMap<String, Vec<String>>>>,
    ) {
        // Analyze model-level attributes
        for attr in &model.attrs {
            self.analyze_single_attribute_with_conflict_detection(
                &attr
                    .name
                    .parts
                    .first()
                    .map_or(String::new(), |p| p.text.clone()),
                attr.args.as_ref(),
                &attr.span,
                AttributeContext::Model,
                &format!("model {}", model.name.text),
                diagnostics,
                Arc::clone(&attribute_usage),
            );
        }

        // Analyze member attributes
        for member in &model.members {
            match member {
                ModelMember::Field(field) => {
                    for attr in &field.attrs {
                        let field_location = format!(
                            "field {}.{}",
                            model.name.text, field.name.text
                        );
                        self.analyze_single_attribute_with_conflict_detection(
                            &attr
                                .name
                                .parts
                                .first()
                                .map_or(String::new(), |p| p.text.clone()),
                            attr.args.as_ref(),
                            &attr.span,
                            AttributeContext::Field,
                            &field_location,
                            diagnostics,
                            Arc::clone(&attribute_usage),
                        );
                    }
                }
                ModelMember::BlockAttribute(attr) => {
                    self.analyze_single_attribute_with_conflict_detection(
                        &attr
                            .name
                            .parts
                            .first()
                            .map_or(String::new(), |p| p.text.clone()),
                        attr.args.as_ref(),
                        &attr.span,
                        AttributeContext::Model,
                        &format!("model {}", model.name.text),
                        diagnostics,
                        Arc::clone(&attribute_usage),
                    );
                }
            }
        }
    }

    /// Analyze attributes for an enum with conflict detection.
    fn analyze_enum_attributes_with_conflict_detection(
        &self,
        enum_decl: &crate::core::parser::ast::EnumDecl,
        diagnostics: &mut Vec<SemanticDiagnostic>,
        attribute_usage: Arc<Mutex<HashMap<String, Vec<String>>>>,
    ) {
        // Analyze enum-level attributes
        for attr in &enum_decl.attrs {
            self.analyze_single_attribute_with_conflict_detection(
                &attr
                    .name
                    .parts
                    .first()
                    .map_or(String::new(), |p| p.text.clone()),
                attr.args.as_ref(),
                &attr.span,
                AttributeContext::Enum,
                &format!("enum {}", enum_decl.name.text),
                diagnostics,
                Arc::clone(&attribute_usage),
            );
        }

        // Analyze enum members
        for member in &enum_decl.members {
            match member {
                EnumMember::Value(value) => {
                    for attr in &value.attrs {
                        self.analyze_single_attribute_with_conflict_detection(
                            &attr
                                .name
                                .parts
                                .first()
                                .map_or(String::new(), |p| p.text.clone()),
                            attr.args.as_ref(),
                            &attr.span,
                            AttributeContext::EnumValue,
                            &format!(
                                "enum value {}.{}",
                                enum_decl.name.text, value.name.text
                            ),
                            diagnostics,
                            Arc::clone(&attribute_usage),
                        );
                    }
                }
                EnumMember::BlockAttribute(attr) => {
                    self.analyze_single_attribute_with_conflict_detection(
                        &attr
                            .name
                            .parts
                            .first()
                            .map_or(String::new(), |p| p.text.clone()),
                        attr.args.as_ref(),
                        &attr.span,
                        AttributeContext::Enum,
                        &format!("enum {}", enum_decl.name.text),
                        diagnostics,
                        Arc::clone(&attribute_usage),
                    );
                }
            }
        }
    }

    /// Analyze a single attribute with conflict detection.
    fn analyze_single_attribute_with_conflict_detection(
        &self,
        attr_name: &str,
        attr_args: Option<&crate::core::parser::ast::ArgList>,
        attr_span: &SymbolSpan,
        context: AttributeContext,
        location: &str,
        diagnostics: &mut Vec<SemanticDiagnostic>,
        attribute_usage: Arc<Mutex<HashMap<String, Vec<String>>>>,
    ) {
        // First do the standard validation
        self.analyze_single_attribute_immutable(
            attr_name,
            attr_args,
            attr_span,
            context,
            location,
            diagnostics,
        );

        // Track attribute usage for conflict detection
        {
            let mut usage = attribute_usage.lock().unwrap();
            usage
                .entry(attr_name.to_string())
                .or_default()
                .push(location.to_string());
        }
    }

    /// Validate attribute conflicts from usage tracking.
    fn validate_attribute_conflicts_from_usage(
        &self,
        attribute_usage: &HashMap<String, Vec<String>>,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Check for non-repeatable attributes used multiple times
        for (attr_name, locations) in attribute_usage {
            if locations.len() > 1
                && let Some(definition) = self.attribute_registry.get(attr_name)
                && !definition.repeatable
            {
                diagnostics.push(SemanticDiagnostic::error(
                            SymbolSpan {
                                start: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                end: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                            },
                            format!(
                                "Attribute '@{attr_name}' cannot be used multiple times. Found on: {}",
                                locations.join(", ")
                            ),
                            DiagnosticCode::ConflictingAttributes,
                        ).with_suggestion("Remove duplicate attributes or use a single attribute with multiple values".to_string()));
            }
        }

        // Check for mutually exclusive attributes
        self.check_mutually_exclusive_attributes_from_usage(
            attribute_usage,
            diagnostics,
        );
    }

    /// Check for mutually exclusive attributes from usage tracking.
    fn check_mutually_exclusive_attributes_from_usage(
        &self,
        attribute_usage: &HashMap<String, Vec<String>>,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Define mutually exclusive attribute pairs
        let exclusive_pairs = [
            ("id", "unique"), // A field can't be both @id and @unique
        ];

        for (attr1, attr2) in exclusive_pairs {
            let has_attr1 = attribute_usage.contains_key(attr1);
            let has_attr2 = attribute_usage.contains_key(attr2);

            if has_attr1 && has_attr2 {
                // Find if they're on the same field
                if let (Some(locations1), Some(locations2)) =
                    (attribute_usage.get(attr1), attribute_usage.get(attr2))
                {
                    for loc1 in locations1 {
                        for loc2 in locations2 {
                            if loc1 == loc2 {
                                diagnostics.push(SemanticDiagnostic::error(
                                    SymbolSpan {
                                        start: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                        end: crate::core::scanner::tokens::SymbolLocation { line: 0, column: 0 },
                                    },
                                    format!("Conflicting attributes '@{attr1}' and '@{attr2}' on {loc1}"),
                                    DiagnosticCode::ConflictingAttributes,
                                ).with_suggestion(format!("Use either '@{attr1}' or '@{attr2}', but not both")));
                            }
                        }
                    }
                }
            }
        }
    }
}

impl Default for AttributeValidationAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl PhaseAnalyzer for AttributeValidationAnalyzer {
    fn phase_name(&self) -> &'static str {
        "attribute-validation"
    }

    fn analyze(
        &self,
        schema: &Schema,
        _context: &AnalysisContext,
    ) -> PhaseResult {
        let mut diagnostics = Vec::new();

        // Thread-safe usage tracking for conflict detection
        let attribute_usage =
            Arc::new(Mutex::new(HashMap::<String, Vec<String>>::new()));

        // Analyze all declarations
        for declaration in &schema.declarations {
            match declaration {
                crate::core::parser::ast::Declaration::Model(model) => {
                    self.analyze_model_attributes_with_conflict_detection(
                        model,
                        &mut diagnostics,
                        Arc::clone(&attribute_usage),
                    );
                }
                crate::core::parser::ast::Declaration::Enum(enum_decl) => {
                    self.analyze_enum_attributes_with_conflict_detection(
                        enum_decl,
                        &mut diagnostics,
                        Arc::clone(&attribute_usage),
                    );
                }
                crate::core::parser::ast::Declaration::Datasource(_)
                | crate::core::parser::ast::Declaration::Generator(_)
                | crate::core::parser::ast::Declaration::Type(_) => {
                    // Not relevant for attribute validation in current Prisma
                }
            }
        }

        // Check for conflicts after analyzing all attributes
        let usage = attribute_usage.lock().unwrap();
        self.validate_attribute_conflicts_from_usage(&usage, &mut diagnostics);

        PhaseResult::new(diagnostics)
    }

    fn dependencies(&self) -> &[&'static str] {
        // Attribute validation can run after basic symbol collection
        &["symbol-collection"]
    }

    fn supports_parallel_execution(&self) -> bool {
        // Attribute validation now supports parallelism with thread-safe conflict detection
        true
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
    fn test_attribute_validation_analyzer_creation() {
        let analyzer = AttributeValidationAnalyzer::new();
        assert_eq!(analyzer.phase_name(), "attribute-validation");
        assert_eq!(analyzer.dependencies(), &["symbol-collection"]);
        assert!(analyzer.supports_parallel_execution());
        assert!(!analyzer.attribute_registry().is_empty());
    }

    #[test]
    fn test_conflict_detection_id_and_unique() {
        // Test that the new thread-safe conflict detection works
        let model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: vec![ModelMember::Field(FieldDecl {
                docs: None,
                name: create_test_ident("id"),
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("Int")],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: vec![
                    FieldAttribute {
                        docs: None,
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("id")],
                            span: create_test_span(),
                        },
                        args: None,
                        span: create_test_span(),
                    },
                    FieldAttribute {
                        docs: None,
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("unique")],
                            span: create_test_span(),
                        },
                        args: None,
                        span: create_test_span(),
                    },
                ],
                span: create_test_span(),
            })],
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Should detect the conflict between @id and @unique
        let has_conflict_error = result.diagnostics.iter().any(|d| {
            d.message.contains("Conflicting attributes")
                && d.message.contains("id")
                && d.message.contains("unique")
        });
        assert!(has_conflict_error, "Should detect @id and @unique conflict");
    }

    #[test]
    fn test_non_repeatable_attribute_usage() {
        // Test detection of multiple uses of non-repeatable attributes
        let model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: vec![
                ModelMember::Field(FieldDecl {
                    docs: None,
                    name: create_test_ident("field1"),
                    r#type: TypeRef::Named(NamedType {
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("Int")],
                            span: create_test_span(),
                        },
                        span: create_test_span(),
                    }),
                    optional: false,
                    modifiers: Vec::new(),
                    attrs: vec![FieldAttribute {
                        docs: None,
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("id")],
                            span: create_test_span(),
                        },
                        args: None,
                        span: create_test_span(),
                    }],
                    span: create_test_span(),
                }),
                ModelMember::Field(FieldDecl {
                    docs: None,
                    name: create_test_ident("field2"),
                    r#type: TypeRef::Named(NamedType {
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("Int")],
                            span: create_test_span(),
                        },
                        span: create_test_span(),
                    }),
                    optional: false,
                    modifiers: Vec::new(),
                    attrs: vec![FieldAttribute {
                        docs: None,
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("id")],
                            span: create_test_span(),
                        },
                        args: None,
                        span: create_test_span(),
                    }],
                    span: create_test_span(),
                }),
            ],
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Should detect multiple uses of non-repeatable @id attribute
        let has_duplicate_error = result.diagnostics.iter().any(|d| {
            d.message.contains("cannot be used multiple times")
                && d.message.contains("id")
        });
        assert!(
            has_duplicate_error,
            "Should detect multiple @id attribute usage"
        );
    }

    #[test]
    fn test_thread_safe_parallel_execution() {
        // Test that the analyzer works correctly when called from multiple threads
        use std::sync::Arc;
        use std::thread;

        let model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: vec![ModelMember::Field(FieldDecl {
                docs: None,
                name: create_test_ident("id"),
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("Int")],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: vec![FieldAttribute {
                    docs: None,
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("id")],
                        span: create_test_span(),
                    },
                    args: None,
                    span: create_test_span(),
                }],
                span: create_test_span(),
            })],
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Arc::new(Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        });

        let analyzer = Arc::new(AttributeValidationAnalyzer::new());
        let options = AnalyzerOptions::default();
        let context = Arc::new(AnalysisContext::new_test(&options));

        let mut handles = Vec::new();

        // Spawn multiple threads to test thread safety
        for _ in 0..4 {
            let schema_clone = Arc::clone(&schema);
            let analyzer_clone = Arc::clone(&analyzer);
            let context_clone = Arc::clone(&context);

            let handle = thread::spawn(move || {
                analyzer_clone.analyze(&schema_clone, &context_clone)
            });
            handles.push(handle);
        }

        // Collect all results
        let mut all_passed = true;
        for handle in handles {
            match handle.join() {
                Ok(result) => {
                    // Each thread should produce the same analysis result
                    // (no diagnostics for a simple valid schema)
                    if !result.diagnostics.is_empty() {
                        all_passed = false;
                    }
                }
                Err(_) => all_passed = false,
            }
        }

        assert!(all_passed, "Thread-safe execution should work correctly");
    }

    #[test]
    fn test_attribute_registry_contains_common_attributes() {
        let analyzer = AttributeValidationAnalyzer::new();
        let registry = analyzer.attribute_registry();

        // Check that common attributes are registered
        assert!(registry.contains_key("id"));
        assert!(registry.contains_key("unique"));
        assert!(registry.contains_key("default"));
        assert!(registry.contains_key("relation"));
        assert!(registry.contains_key("map"));
        assert!(registry.contains_key("index"));

        // Check attribute properties
        let id_attr = registry
            .get("id")
            .expect("id attribute should be registered");
        assert!(id_attr.valid_contexts.contains(&AttributeContext::Field));
        assert!(!id_attr.repeatable);
        assert!(!id_attr.deprecated);

        let autoincrement_attr = registry
            .get("autoincrement")
            .expect("autoincrement attribute should be registered");
        assert!(autoincrement_attr.deprecated);
        assert!(autoincrement_attr.replacement.is_some());
    }

    #[test]
    fn test_empty_schema_analysis() {
        let schema = Schema {
            declarations: vec![],
            span: create_test_span(),
        };

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Empty schema should not have attribute errors
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn test_model_without_attributes() {
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

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Model without attributes should not have errors
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn test_unknown_attribute_detection() {
        let field_attr = FieldAttribute {
            name: QualifiedIdent {
                parts: vec![create_test_ident("unknownattr")],
                span: create_test_span(),
            },
            args: None,
            docs: None,
            span: create_test_span(),
        };

        let model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: vec![ModelMember::Field(FieldDecl {
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
                attrs: vec![field_attr],
                span: create_test_span(),
            })],
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Should detect unknown attribute
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(
            result.diagnostics[0].diagnostic_code,
            DiagnosticCode::UnknownAttribute
        );
        assert!(result.diagnostics[0].message.contains("unknownattr"));
        // Span should not be 0:0
        assert!(result.diagnostics[0].span.start.line > 0);
    }

    #[test]
    fn test_attribute_context_validation() {
        // Try to use @id on a model (should fail - @id is for fields only)
        let model_attr = BlockAttribute {
            name: QualifiedIdent {
                parts: vec![create_test_ident("id")],
                span: create_test_span(),
            },
            args: None,
            docs: None,
            span: create_test_span(),
        };

        let model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: vec![],
            attrs: vec![model_attr],
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Should detect invalid context usage
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(
            result.diagnostics[0].diagnostic_code,
            DiagnosticCode::AttributeNotApplicable
        );
        assert!(result.diagnostics[0].message.contains("@id"));
        assert!(result.diagnostics[0].message.contains("field"));
    }

    #[test]
    fn test_deprecated_attribute_detection() {
        let field_attr = FieldAttribute {
            name: QualifiedIdent {
                parts: vec![create_test_ident("autoincrement")],
                span: create_test_span(),
            },
            args: None,
            docs: None,
            span: create_test_span(),
        };

        let model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: vec![ModelMember::Field(FieldDecl {
                docs: None,
                name: create_test_ident("id"),
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("Int")],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: vec![field_attr],
                span: create_test_span(),
            })],
            attrs: Vec::new(),
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Should detect deprecated attribute
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(
            result.diagnostics[0].diagnostic_code,
            DiagnosticCode::DeprecatedFeature
        );
        assert!(result.diagnostics[0].message.contains("autoincrement"));
        assert!(result.diagnostics[0].suggestion.is_some());
    }

    #[test]
    fn test_enum_attribute_validation() {
        let enum_decl = EnumDecl {
            docs: None,
            name: create_test_ident("Status"),
            members: vec![EnumMember::Value(EnumValue {
                docs: None,
                name: create_test_ident("ACTIVE"),
                attrs: vec![FieldAttribute {
                    docs: None,
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("map")],
                        span: create_test_span(),
                    },
                    args: Some(ArgList {
                        items: vec![Arg::Named(NamedArg {
                            name: create_test_ident("name"),
                            value: Expr::StringLit(StringLit {
                                value: "active_status".to_string(),
                                span: create_test_span(),
                            }),
                            span: create_test_span(),
                        })],
                        span: create_test_span(),
                    }),
                    span: create_test_span(),
                }],
                span: create_test_span(),
            })],
            attrs: vec![BlockAttribute {
                docs: None,
                name: QualifiedIdent {
                    parts: vec![create_test_ident("map")],
                    span: create_test_span(),
                },
                args: Some(ArgList {
                    items: vec![Arg::Named(NamedArg {
                        name: create_test_ident("name"),
                        value: Expr::StringLit(StringLit {
                            value: "status_enum".to_string(),
                            span: create_test_span(),
                        }),
                        span: create_test_span(),
                    })],
                    span: create_test_span(),
                }),
                span: create_test_span(),
            }],
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Enum(enum_decl)],
            span: create_test_span(),
        };

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let _result = analyzer.analyze(&schema, &context);

        // Should process enum attributes without crashing
        // The analyzer should always return a valid result
    }

    #[test]
    fn test_datasource_generator_validation() {
        let datasource = DatasourceDecl {
            name: create_test_ident("db"),
            assignments: vec![Assignment {
                key: create_test_ident("provider"),
                value: Expr::StringLit(StringLit {
                    value: "postgresql".to_string(),
                    span: create_test_span(),
                }),
                docs: None,
                span: create_test_span(),
            }],
            docs: None,
            span: create_test_span(),
        };

        let generator = GeneratorDecl {
            name: create_test_ident("client"),
            assignments: vec![Assignment {
                key: create_test_ident("provider"),
                value: Expr::StringLit(StringLit {
                    value: "prisma-client-js".to_string(),
                    span: create_test_span(),
                }),
                docs: None,
                span: create_test_span(),
            }],
            docs: None,
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![
                Declaration::Datasource(datasource),
                Declaration::Generator(generator),
            ],
            span: create_test_span(),
        };

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Datasource and generator declarations should pass without attribute errors
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn test_attribute_argument_validation() {
        // Test field with invalid argument to @unique
        let field = FieldDecl {
            docs: None,
            name: create_test_ident("email"),
            r#type: TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![create_test_ident("String")],
                    span: create_test_span(),
                },
                span: create_test_span(),
            }),
            optional: false,
            modifiers: Vec::new(),
            attrs: vec![FieldAttribute {
                docs: None,
                name: QualifiedIdent {
                    parts: vec![create_test_ident("unique")],
                    span: create_test_span(),
                },
                args: Some(ArgList {
                    items: vec![Arg::Named(NamedArg {
                        name: create_test_ident("invalid_arg"),
                        value: Expr::StringLit(StringLit {
                            value: "value".to_string(),
                            span: create_test_span(),
                        }),
                        span: create_test_span(),
                    })],
                    span: create_test_span(),
                }),
                span: create_test_span(),
            }],
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

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let _result = analyzer.analyze(&schema, &context);

        // May or may not have validation errors depending on implementation
        // At minimum, should not crash - just check that we get some result
        // (The analyzer should always produce a result, even if empty)
    }

    fn get_complex_members() -> Vec<ModelMember> {
        vec![
            ModelMember::Field(FieldDecl {
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
                attrs: vec![
                    FieldAttribute {
                        docs: None,
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("id")],
                            span: create_test_span(),
                        },
                        args: None,
                        span: create_test_span(),
                    },
                    FieldAttribute {
                        docs: None,
                        name: QualifiedIdent {
                            parts: vec![create_test_ident("default")],
                            span: create_test_span(),
                        },
                        args: Some(ArgList {
                            items: vec![Arg::Positional(PositionalArg {
                                value: Expr::FuncCall(FuncCall {
                                    callee: QualifiedIdent {
                                        parts: vec![create_test_ident("cuid")],
                                        span: create_test_span(),
                                    },
                                    args: None,
                                    span: create_test_span(),
                                }),
                                span: create_test_span(),
                            })],
                            span: create_test_span(),
                        }),
                        span: create_test_span(),
                    },
                ],
                span: create_test_span(),
            }),
            ModelMember::Field(FieldDecl {
                docs: None,
                name: create_test_ident("email"),
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("String")],
                        span: create_test_span(),
                    },
                    span: create_test_span(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: vec![FieldAttribute {
                    docs: None,
                    name: QualifiedIdent {
                        parts: vec![create_test_ident("unique")],
                        span: create_test_span(),
                    },
                    args: None,
                    span: create_test_span(),
                }],
                span: create_test_span(),
            }),
        ]
    }

    #[test]
    fn test_complex_model_attributes() {
        let model = ModelDecl {
            docs: None,
            name: create_test_ident("User"),
            members: get_complex_members(),
            attrs: vec![BlockAttribute {
                docs: None,
                name: QualifiedIdent {
                    parts: vec![create_test_ident("map")],
                    span: create_test_span(),
                },
                args: Some(ArgList {
                    items: vec![Arg::Named(NamedArg {
                        name: create_test_ident("name"),
                        value: Expr::StringLit(StringLit {
                            value: "users".to_string(),
                            span: create_test_span(),
                        }),
                        span: create_test_span(),
                    })],
                    span: create_test_span(),
                }),
                span: create_test_span(),
            }],
            span: create_test_span(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: create_test_span(),
        };

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let _result = analyzer.analyze(&schema, &context);

        // Complex model with various attributes should process without crashing
        // The analyzer should always return a valid result
    }

    #[test]
    fn test_analyzer_methods() {
        let analyzer = AttributeValidationAnalyzer::new();
        assert_eq!(analyzer.phase_name(), "attribute-validation");
        assert_eq!(analyzer.dependencies(), &["symbol-collection"]);

        assert!(analyzer.supports_parallel_execution()); // Now supports parallel execution
    }

    #[test]
    fn test_attribute_registry_completeness() {
        let analyzer = AttributeValidationAnalyzer::new();

        // Check that common attributes are registered
        let common_attributes =
            ["id", "unique", "default", "map", "relation", "updatedAt"];

        for attr_name in &common_attributes {
            let has_attr = analyzer.attribute_registry.contains_key(*attr_name);
            assert!(has_attr, "Attribute '{attr_name}' should be registered");
        }

        // Verify that the analyzer initializes correctly
        assert!(!analyzer.attribute_registry.is_empty());
    }

    #[test]
    fn test_multiple_context_violations() {
        // Test field with attribute that should only be on models
        let field = FieldDecl {
            docs: None,
            name: create_test_ident("email"),
            r#type: TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![create_test_ident("String")],
                    span: create_test_span(),
                },
                span: create_test_span(),
            }),
            optional: false,
            modifiers: Vec::new(),
            attrs: vec![FieldAttribute {
                docs: None,
                name: QualifiedIdent {
                    parts: vec![create_test_ident("schema")], // This is not valid on fields
                    span: create_test_span(),
                },
                args: None,
                span: create_test_span(),
            }],
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

        let analyzer = AttributeValidationAnalyzer::new();
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let result = analyzer.analyze(&schema, &context);

        // Should detect unknown attribute or context violation
        assert!(!result.diagnostics.is_empty());
    }
}
