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
    pub fn resolve_schema_types(
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
    pub fn resolve_model_types(
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
    pub fn resolve_field_type(
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
    pub fn validate_resolved_type(
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
    pub fn validate_model_reference(
        model_name: &str,
        type_ref: &TypeRef,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Additional validation could be added here
        // For example, checking if the model has required fields
        _ = (model_name, type_ref, diagnostics);
    }

    /// Convert a type resolution error into a diagnostic.
    pub fn add_type_resolution_error(
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
        let mut diagnostics = Vec::new();

        // Use shared symbol table and resolver from the analysis context
        let (Ok(symbol_table), Ok(mut resolver)) =
            (context.symbol_table.read(), context.type_resolver.write())
        else {
            return PhaseResult::error(SemanticDiagnostic::error(
                schema.span.clone(),
                "Failed to acquire analysis locks".to_string(),
                DiagnosticCode::InternalError,
            ));
        };

        // Resolve all field types and collect diagnostics
        for declaration in &schema.declarations {
            if let Declaration::Model(model) = declaration {
                let current_model_name = model.name.text.clone();
                for member in &model.members {
                    if let ModelMember::Field(field) = member {
                        match resolver
                            .resolve_type(&field.r#type, &symbol_table)
                        {
                            Ok(resolved_ty) => {
                                // track dependencies when a field references another model
                                if let ResolvedType::Model(target) =
                                    &resolved_ty
                                {
                                    resolver.add_type_dependency(
                                        current_model_name.clone(),
                                        target.clone(),
                                    );
                                }
                                Self::validate_resolved_type(
                                    &resolved_ty,
                                    &field.r#type,
                                    &mut diagnostics,
                                );
                            }
                            Err(err) => {
                                Self::add_type_resolution_error(
                                    err,
                                    field.r#type.span(),
                                    &mut diagnostics,
                                );
                            }
                        }
                    }
                }
            }
        }

        // Check for circular dependencies accumulated in the shared resolver
        if let Err(err) = resolver.check_circular_dependencies() {
            Self::add_type_resolution_error(
                err,
                &schema.span,
                &mut diagnostics,
            );
        }

        // Backward-compatibility for tests that add dependencies to self.type_resolver
        // If the analyzer's internal resolver has dependency edges, also check it for cycles.
        if self.type_resolver.stats().dependency_edges > 0
            && let Err(err) = self.type_resolver.check_circular_dependencies()
        {
            Self::add_type_resolution_error(
                err,
                &schema.span,
                &mut diagnostics,
            );
        }

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
