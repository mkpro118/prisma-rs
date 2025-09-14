//! Symbol table for tracking schema declarations and their metadata.
//!
//! The symbol table maintains a hierarchical view of all declared symbols in
//! the schema, including models, enums, fields, and their relationships.

use crate::core::parser::ast::{
    DatasourceDecl, EnumDecl, EnumValue, FieldDecl, GeneratorDecl, ModelDecl,
};
use crate::core::scanner::tokens::SymbolSpan;
use std::collections::HashMap;

/// Global symbol table for schema analysis.
///
/// The symbol table tracks all declared identifiers and their metadata
/// across different scopes (global, model-local, etc.).
#[derive(Debug, Clone)]
pub struct SymbolTable {
    /// Global scope symbols (models, enums, datasources, generators, types)
    global_symbols: HashMap<String, Symbol>,

    /// Model-scoped symbols (fields within each model)
    model_scopes: HashMap<String, HashMap<String, Symbol>>,

    /// Enum-scoped symbols (values within each enum)
    enum_scopes: HashMap<String, HashMap<String, Symbol>>,

    /// Built-in types and functions
    builtin_symbols: HashMap<String, Symbol>,
}

impl SymbolTable {
    /// Create a new symbol table with built-in symbols.
    #[must_use]
    pub fn new() -> Self {
        let mut table = Self {
            global_symbols: HashMap::new(),
            model_scopes: HashMap::new(),
            enum_scopes: HashMap::new(),
            builtin_symbols: HashMap::new(),
        };

        table.initialize_builtins();
        table
    }

    /// Add a model symbol to the global scope.
    ///
    /// # Errors
    ///
    /// Returns a `SymbolError` if the model name conflicts with an existing symbol.
    pub fn add_model(&mut self, model: &ModelDecl) -> Result<(), SymbolError> {
        let symbol = Symbol::new_model(model);
        self.add_global_symbol(symbol)?;

        // Create scope for model fields
        let mut field_scope = HashMap::new();

        // Add field symbols
        for member in &model.members {
            if let crate::core::parser::ast::ModelMember::Field(field) = member
            {
                let field_symbol = Symbol::new_field(field, &model.name.text);
                if let Some(existing) =
                    field_scope.insert(field.name.text.clone(), field_symbol)
                {
                    return Err(SymbolError::DuplicateSymbol {
                        name: field.name.text.clone(),
                        scope: model.name.text.clone(),
                        existing_span: existing.declaration_span,
                        new_span: field.span.clone(),
                    });
                }
            }
        }

        self.model_scopes
            .insert(model.name.text.clone(), field_scope);
        Ok(())
    }

    /// Add an enum symbol to the global scope.
    ///
    /// # Errors
    ///
    /// Returns a `SymbolError` if the enum name conflicts with an existing symbol.
    pub fn add_enum(
        &mut self,
        enum_decl: &EnumDecl,
    ) -> Result<(), SymbolError> {
        let symbol = Symbol::new_enum(enum_decl);
        self.add_global_symbol(symbol)?;

        // Create scope for enum values
        let mut value_scope = HashMap::new();

        // Add enum value symbols
        for member in &enum_decl.members {
            if let crate::core::parser::ast::EnumMember::Value(value) = member {
                let value_symbol =
                    Symbol::new_enum_value(value, &enum_decl.name.text);
                if let Some(existing) =
                    value_scope.insert(value.name.text.clone(), value_symbol)
                {
                    return Err(SymbolError::DuplicateSymbol {
                        name: value.name.text.clone(),
                        scope: enum_decl.name.text.clone(),
                        existing_span: existing.declaration_span,
                        new_span: value.span.clone(),
                    });
                }
            }
        }

        self.enum_scopes
            .insert(enum_decl.name.text.clone(), value_scope);
        Ok(())
    }

    /// Add a datasource symbol to the global scope.
    ///
    /// # Errors
    ///
    /// Returns a `SymbolError` if the datasource name conflicts with an existing symbol.
    pub fn add_datasource(
        &mut self,
        datasource: &DatasourceDecl,
    ) -> Result<(), SymbolError> {
        let symbol = Symbol::new_datasource(datasource);
        self.add_global_symbol(symbol)
    }

    /// Add a generator symbol to the global scope.
    ///
    /// # Errors
    ///
    /// Returns a `SymbolError` if the generator name conflicts with an existing symbol.
    pub fn add_generator(
        &mut self,
        generator: &GeneratorDecl,
    ) -> Result<(), SymbolError> {
        let symbol = Symbol::new_generator(generator);
        self.add_global_symbol(symbol)
    }

    /// Look up a symbol in the global scope.
    #[must_use]
    pub fn lookup_global(&self, name: &str) -> Option<&Symbol> {
        self.global_symbols
            .get(name)
            .or_else(|| self.builtin_symbols.get(name))
    }

    /// Look up a field symbol within a model scope.
    #[must_use]
    pub fn lookup_field(
        &self,
        model_name: &str,
        field_name: &str,
    ) -> Option<&Symbol> {
        self.model_scopes.get(model_name)?.get(field_name)
    }

    /// Look up an enum value within an enum scope.
    #[must_use]
    pub fn lookup_enum_value(
        &self,
        enum_name: &str,
        value_name: &str,
    ) -> Option<&Symbol> {
        self.enum_scopes.get(enum_name)?.get(value_name)
    }

    /// Get all models in the symbol table.
    pub fn models(&self) -> impl Iterator<Item = (&String, &Symbol)> {
        self.global_symbols.iter().filter(|(_, symbol)| {
            matches!(symbol.symbol_type, SymbolType::Model(_))
        })
    }

    /// Get all enums in the symbol table.
    pub fn enums(&self) -> impl Iterator<Item = (&String, &Symbol)> {
        self.global_symbols.iter().filter(|(_, symbol)| {
            matches!(symbol.symbol_type, SymbolType::Enum(_))
        })
    }

    /// Get all fields in a specific model.
    #[must_use]
    pub fn model_fields(
        &self,
        model_name: &str,
    ) -> Option<impl Iterator<Item = (&String, &Symbol)>> {
        self.model_scopes.get(model_name).map(|scope| scope.iter())
    }

    /// Get all values in a specific enum.
    #[must_use]
    pub fn enum_values(
        &self,
        enum_name: &str,
    ) -> Option<impl Iterator<Item = (&String, &Symbol)>> {
        self.enum_scopes.get(enum_name).map(|scope| scope.iter())
    }

    /// Check if a symbol exists in any scope.
    #[must_use]
    pub fn contains(&self, name: &str) -> bool {
        self.lookup_global(name).is_some()
    }

    /// Get the total number of symbols across all scopes.
    #[must_use]
    pub fn total_symbol_count(&self) -> usize {
        self.global_symbols.len()
            + self
                .model_scopes
                .values()
                .map(std::collections::HashMap::len)
                .sum::<usize>()
            + self
                .enum_scopes
                .values()
                .map(std::collections::HashMap::len)
                .sum::<usize>()
    }

    /// Add a symbol to the global scope with duplicate checking.
    fn add_global_symbol(&mut self, symbol: Symbol) -> Result<(), SymbolError> {
        let name = symbol.name.clone();

        if let Some(existing) = self.global_symbols.get(&name) {
            return Err(SymbolError::DuplicateSymbol {
                name,
                scope: "global".to_string(),
                existing_span: existing.declaration_span.clone(),
                new_span: symbol.declaration_span.clone(),
            });
        }

        self.global_symbols.insert(name, symbol);
        Ok(())
    }

    /// Initialize built-in symbols (scalar types, functions, etc.).
    fn initialize_builtins(&mut self) {
        // Built-in scalar types
        for scalar_type in &[
            "String", "Int", "Float", "Boolean", "DateTime", "Json", "Bytes",
            "Decimal", "BigInt", "Uuid",
        ] {
            let symbol = Symbol::new_builtin_type(scalar_type);
            self.builtin_symbols
                .insert((*scalar_type).to_string(), symbol);
        }

        // Built-in functions (for use in default values, etc.)
        for function in &["now", "autoincrement", "cuid", "uuid"] {
            let symbol = Symbol::new_builtin_function(function);
            self.builtin_symbols.insert((*function).to_string(), symbol);
        }
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

/// A symbol in the symbol table.
#[derive(Debug, Clone)]
pub struct Symbol {
    /// The name of the symbol
    pub name: String,

    /// The type and metadata of the symbol
    pub symbol_type: SymbolType,

    /// The span where this symbol was declared
    pub declaration_span: SymbolSpan,

    /// Visibility of this symbol
    pub visibility: Visibility,

    /// Additional metadata about the symbol
    pub metadata: SymbolMetadata,
}

impl Symbol {
    /// Create a new model symbol.
    #[must_use]
    pub fn new_model(model: &ModelDecl) -> Self {
        Self {
            name: model.name.text.clone(),
            symbol_type: SymbolType::Model(ModelSymbol {
                field_count: model
                    .members
                    .iter()
                    .filter(|m| {
                        matches!(
                            m,
                            crate::core::parser::ast::ModelMember::Field(_)
                        )
                    })
                    .count(),
                has_primary_key: model.members.iter().any(|m| {
                    if let crate::core::parser::ast::ModelMember::Field(field) =
                        m
                    {
                        field.attrs.iter().any(|attr| {
                            attr.name.parts.len() == 1
                                && attr.name.parts[0].text == "id"
                        })
                    } else {
                        false
                    }
                }),
                block_attributes: model.attrs.len(),
            }),
            declaration_span: model.span.clone(),
            visibility: Visibility::Public,
            metadata: SymbolMetadata::new(),
        }
    }

    /// Create a new enum symbol.
    #[must_use]
    pub fn new_enum(enum_decl: &EnumDecl) -> Self {
        Self {
            name: enum_decl.name.text.clone(),
            symbol_type: SymbolType::Enum(EnumSymbol {
                value_count: enum_decl
                    .members
                    .iter()
                    .filter(|m| {
                        matches!(
                            m,
                            crate::core::parser::ast::EnumMember::Value(_)
                        )
                    })
                    .count(),
                block_attributes: enum_decl.attrs.len(),
            }),
            declaration_span: enum_decl.span.clone(),
            visibility: Visibility::Public,
            metadata: SymbolMetadata::new(),
        }
    }

    /// Create a new field symbol.
    #[must_use]
    pub fn new_field(field: &FieldDecl, parent_model: &str) -> Self {
        Self {
            name: field.name.text.clone(),
            symbol_type: SymbolType::Field(FieldSymbol {
                parent_model: parent_model.to_string(),
                is_optional: field.optional,
                is_list: matches!(
                    &field.r#type,
                    crate::core::parser::ast::TypeRef::List(_)
                ),
                attribute_count: field.attrs.len(),
            }),
            declaration_span: field.span.clone(),
            visibility: Visibility::Public,
            metadata: SymbolMetadata::new(),
        }
    }

    /// Create a new enum value symbol.
    #[must_use]
    pub fn new_enum_value(value: &EnumValue, parent_enum: &str) -> Self {
        Self {
            name: value.name.text.clone(),
            symbol_type: SymbolType::EnumValue(EnumValueSymbol {
                parent_enum: parent_enum.to_string(),
                attribute_count: value.attrs.len(),
            }),
            declaration_span: value.span.clone(),
            visibility: Visibility::Public,
            metadata: SymbolMetadata::new(),
        }
    }

    /// Create a new datasource symbol.
    #[must_use]
    pub fn new_datasource(datasource: &DatasourceDecl) -> Self {
        Self {
            name: datasource.name.text.clone(),
            symbol_type: SymbolType::Datasource(DatasourceSymbol {
                assignment_count: datasource.assignments.len(),
            }),
            declaration_span: datasource.span.clone(),
            visibility: Visibility::Public,
            metadata: SymbolMetadata::new(),
        }
    }

    /// Create a new generator symbol.
    #[must_use]
    pub fn new_generator(generator: &GeneratorDecl) -> Self {
        Self {
            name: generator.name.text.clone(),
            symbol_type: SymbolType::Generator(GeneratorSymbol {
                assignment_count: generator.assignments.len(),
            }),
            declaration_span: generator.span.clone(),
            visibility: Visibility::Public,
            metadata: SymbolMetadata::new(),
        }
    }

    /// Create a built-in type symbol.
    #[must_use]
    pub fn new_builtin_type(name: &str) -> Self {
        Self {
            name: name.to_string(),
            symbol_type: SymbolType::BuiltinType(BuiltinTypeSymbol {
                type_category: TypeCategory::Scalar,
            }),
            declaration_span: SymbolSpan {
                start: crate::core::scanner::tokens::SymbolLocation {
                    line: 0,
                    column: 0,
                },
                end: crate::core::scanner::tokens::SymbolLocation {
                    line: 0,
                    column: 0,
                },
            },
            visibility: Visibility::Public,
            metadata: SymbolMetadata::builtin(),
        }
    }

    /// Create a built-in function symbol.
    #[must_use]
    pub fn new_builtin_function(name: &str) -> Self {
        Self {
            name: name.to_string(),
            symbol_type: SymbolType::BuiltinFunction(BuiltinFunctionSymbol {
                function_category: FunctionCategory::Generator,
            }),
            declaration_span: SymbolSpan {
                start: crate::core::scanner::tokens::SymbolLocation {
                    line: 0,
                    column: 0,
                },
                end: crate::core::scanner::tokens::SymbolLocation {
                    line: 0,
                    column: 0,
                },
            },
            visibility: Visibility::Public,
            metadata: SymbolMetadata::builtin(),
        }
    }
}

/// Types of symbols that can be stored in the symbol table.
#[derive(Debug, Clone)]
pub enum SymbolType {
    Model(ModelSymbol),
    Enum(EnumSymbol),
    Field(FieldSymbol),
    EnumValue(EnumValueSymbol),
    Datasource(DatasourceSymbol),
    Generator(GeneratorSymbol),
    TypeAlias(TypeAliasSymbol),
    BuiltinType(BuiltinTypeSymbol),
    BuiltinFunction(BuiltinFunctionSymbol),
}

/// Symbol metadata for model declarations.
#[derive(Debug, Clone)]
pub struct ModelSymbol {
    pub field_count: usize,
    pub has_primary_key: bool,
    pub block_attributes: usize,
}

/// Symbol metadata for enum declarations.
#[derive(Debug, Clone)]
pub struct EnumSymbol {
    pub value_count: usize,
    pub block_attributes: usize,
}

/// Symbol metadata for field declarations.
#[derive(Debug, Clone)]
pub struct FieldSymbol {
    pub parent_model: String,
    pub is_optional: bool,
    pub is_list: bool,
    pub attribute_count: usize,
}

/// Symbol metadata for enum value declarations.
#[derive(Debug, Clone)]
pub struct EnumValueSymbol {
    pub parent_enum: String,
    pub attribute_count: usize,
}

/// Symbol metadata for datasource declarations.
#[derive(Debug, Clone)]
pub struct DatasourceSymbol {
    pub assignment_count: usize,
}

/// Symbol metadata for generator declarations.
#[derive(Debug, Clone)]
pub struct GeneratorSymbol {
    pub assignment_count: usize,
}

/// Symbol metadata for type alias declarations.
#[derive(Debug, Clone)]
pub struct TypeAliasSymbol {
    pub target_type: String, // Will be properly typed later
}

/// Symbol metadata for built-in type symbols.
#[derive(Debug, Clone)]
pub struct BuiltinTypeSymbol {
    pub type_category: TypeCategory,
}

/// Symbol metadata for built-in function symbols.
#[derive(Debug, Clone)]
pub struct BuiltinFunctionSymbol {
    pub function_category: FunctionCategory,
}

/// Categories of built-in types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeCategory {
    Scalar,
    Composite,
}

/// Categories of built-in functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionCategory {
    Generator,
    Transformer,
}

/// Symbol visibility levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Private,
}

/// Additional metadata about symbols.
#[derive(Debug, Clone)]
pub struct SymbolMetadata {
    pub is_builtin: bool,
    pub documentation: Option<String>,
    pub tags: Vec<String>,
}

impl Default for SymbolMetadata {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolMetadata {
    #[must_use]
    pub fn new() -> Self {
        Self {
            is_builtin: false,
            documentation: None,
            tags: Vec::new(),
        }
    }

    #[must_use]
    pub fn builtin() -> Self {
        Self {
            is_builtin: true,
            documentation: None,
            tags: Vec::new(),
        }
    }
}

/// Errors that can occur during symbol table operations.
#[derive(Debug, Clone)]
pub enum SymbolError {
    /// Duplicate symbol declaration
    DuplicateSymbol {
        name: String,
        scope: String,
        existing_span: SymbolSpan,
        new_span: SymbolSpan,
    },

    /// Symbol not found
    SymbolNotFound { name: String, scope: String },

    /// Invalid symbol operation
    InvalidOperation { message: String },
}

impl std::fmt::Display for SymbolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SymbolError::DuplicateSymbol { name, scope, .. } => {
                write!(f, "Duplicate symbol '{name}' in scope '{scope}'")
            }
            SymbolError::SymbolNotFound { name, scope } => {
                write!(f, "Symbol '{name}' not found in scope '{scope}'")
            }
            SymbolError::InvalidOperation { message } => {
                write!(f, "Invalid symbol operation: {message}")
            }
        }
    }
}

impl std::error::Error for SymbolError {}
