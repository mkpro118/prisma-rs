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
    fn validate_declarations(
        schema: &Schema,
        context: &AnalysisContext,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        // Validate identifiers in all declarations
        for declaration in &schema.declarations {
            match declaration {
                Declaration::Model(model) => {
                    Self::check_model(model, diagnostics);
                }
                Declaration::Enum(enum_decl) => {
                    Self::check_enum(enum_decl, diagnostics);
                }
                Declaration::Datasource(datasource) => {
                    Self::check_datasource(datasource, diagnostics);
                }
                Declaration::Generator(generator) => {
                    Self::check_generator(generator, diagnostics);
                }
                Declaration::Type(type_alias) => {
                    Self::check_type_alias(type_alias, context, diagnostics);
                }
            }
        }
        Self::check_has_datasource(schema, diagnostics);
    }

    fn populate_symbol_table_from_schema(
        schema: &Schema,
        context: &AnalysisContext,
        diagnostics: &mut Vec<SemanticDiagnostic>,
    ) {
        if let Ok(mut symtab) = context.symbol_table.write() {
            for declaration in &schema.declarations {
                match declaration {
                    Declaration::Model(m) => {
                        if let Err(err) = symtab.add_model(m)
                            && let SymbolError::DuplicateSymbol {
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
                    Declaration::Enum(e) => {
                        if let Err(err) = symtab.add_enum(e)
                            && let SymbolError::DuplicateSymbol {
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
                    Declaration::Datasource(d) => {
                        if let Err(err) = symtab.add_datasource(d)
                            && let SymbolError::DuplicateSymbol {
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
                    Declaration::Generator(g) => {
                        if let Err(err) = symtab.add_generator(g)
                            && let SymbolError::DuplicateSymbol {
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
                    Declaration::Type(_t) => {
                        // Type aliases currently not added to the symbol table.
                    }
                }
            }
        }
    }
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

        Self::validate_declarations(schema, context, &mut diagnostics);
        Self::populate_symbol_table_from_schema(
            schema,
            context,
            &mut diagnostics,
        );

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
