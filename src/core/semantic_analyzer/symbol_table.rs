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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::parser::ast::*;
    use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};

    fn test_span() -> SymbolSpan {
        SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        }
    }

    fn test_ident(name: &str) -> Ident {
        Ident {
            text: name.to_string(),
            span: test_span(),
        }
    }

    fn test_string_expr(value: &str) -> Expr {
        Expr::StringLit(StringLit {
            value: value.to_string(),
            span: test_span(),
        })
    }

    fn test_named_type(name: &str) -> TypeRef {
        TypeRef::Named(NamedType {
            name: QualifiedIdent {
                parts: vec![test_ident(name)],
                span: test_span(),
            },
            span: test_span(),
        })
    }

    fn test_list_type(inner_type: TypeRef) -> TypeRef {
        TypeRef::List(ListType {
            inner: Box::new(inner_type),
            span: test_span(),
        })
    }

    #[test]
    fn test_symbol_table_creation() {
        let table = SymbolTable::new();
        assert!(table.contains("String")); // Built-in type
        assert!(table.contains("now")); // Built-in function
        assert!(!table.contains("NonExistent"));
    }

    #[test]
    fn test_model_symbol_addition() {
        let mut table = SymbolTable::new();

        let model = ModelDecl {
            name: test_ident("User"),
            members: vec![],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        assert!(table.add_model(&model).is_ok());
        assert!(table.contains("User"));

        let Some(symbol) = table.lookup_global("User") else {
            panic!("Should find User symbol")
        };
        assert!(matches!(symbol.symbol_type, SymbolType::Model(_)));
    }

    #[test]
    fn test_duplicate_model_detection() {
        let mut table = SymbolTable::new();

        let model1 = ModelDecl {
            name: test_ident("User"),
            members: vec![],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        let model2 = ModelDecl {
            name: test_ident("User"),
            members: vec![],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        assert!(table.add_model(&model1).is_ok());
        assert!(table.add_model(&model2).is_err());
    }

    #[test]
    fn test_symbol_counting() {
        let mut table = SymbolTable::new();
        let initial_count = table.total_symbol_count();

        let model = ModelDecl {
            name: test_ident("User"),
            members: vec![],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        assert!(
            table.add_model(&model).is_ok(),
            "Should add model successfully"
        );
        assert_eq!(table.total_symbol_count(), initial_count + 1);
    }

    #[test]
    fn test_enum_symbol_addition() {
        let mut table = SymbolTable::new();

        let enum_decl = EnumDecl {
            name: test_ident("Role"),
            members: vec![
                EnumMember::Value(EnumValue {
                    name: test_ident("ADMIN"),
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
                EnumMember::Value(EnumValue {
                    name: test_ident("USER"),
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
            ],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        assert!(table.add_enum(&enum_decl).is_ok());
        assert!(table.contains("Role"));

        let symbol = table.lookup_global("Role").unwrap();
        assert!(matches!(symbol.symbol_type, SymbolType::Enum(_)));

        // Test enum value lookups
        let admin_value = table.lookup_enum_value("Role", "ADMIN");
        assert!(admin_value.is_some());

        let user_value = table.lookup_enum_value("Role", "USER");
        assert!(user_value.is_some());

        let nonexistent = table.lookup_enum_value("Role", "GUEST");
        assert!(nonexistent.is_none());
    }

    #[test]
    fn test_duplicate_enum_values() {
        let mut table = SymbolTable::new();

        let enum_decl = EnumDecl {
            name: test_ident("Status"),
            members: vec![
                EnumMember::Value(EnumValue {
                    name: test_ident("ACTIVE"),
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
                EnumMember::Value(EnumValue {
                    name: test_ident("ACTIVE"), // Duplicate
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
            ],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        let result = table.add_enum(&enum_decl);
        assert!(result.is_err());

        if let Err(SymbolError::DuplicateSymbol { name, scope, .. }) = result {
            assert_eq!(name, "ACTIVE");
            assert_eq!(scope, "Status");
        } else {
            panic!("Expected DuplicateSymbol error");
        }
    }

    #[test]
    fn test_datasource_symbol_addition() {
        let mut table = SymbolTable::new();

        let datasource = DatasourceDecl {
            name: test_ident("db"),
            assignments: vec![
                Assignment {
                    key: test_ident("provider"),
                    value: test_string_expr("postgresql"),
                    docs: None,
                    span: test_span(),
                },
                Assignment {
                    key: test_ident("url"),
                    value: test_string_expr("postgres://..."),
                    docs: None,
                    span: test_span(),
                },
            ],
            docs: None,
            span: test_span(),
        };

        assert!(table.add_datasource(&datasource).is_ok());
        assert!(table.contains("db"));

        let symbol = table.lookup_global("db").unwrap();
        if let SymbolType::Datasource(ds) = &symbol.symbol_type {
            assert_eq!(ds.assignment_count, 2);
        } else {
            panic!("Expected Datasource symbol");
        }
    }

    #[test]
    fn test_generator_symbol_addition() {
        let mut table = SymbolTable::new();

        let generator = GeneratorDecl {
            name: test_ident("client"),
            assignments: vec![Assignment {
                key: test_ident("provider"),
                value: test_string_expr("prisma-client-js"),
                docs: None,
                span: test_span(),
            }],
            docs: None,
            span: test_span(),
        };

        assert!(table.add_generator(&generator).is_ok());
        assert!(table.contains("client"));

        let symbol = table.lookup_global("client").unwrap();
        if let SymbolType::Generator(generator_symbol) = &symbol.symbol_type {
            assert_eq!(generator_symbol.assignment_count, 1);
        } else {
            panic!("Expected Generator symbol");
        }
    }

    #[test]
    fn test_model_with_fields() {
        let mut table = SymbolTable::new();

        let model = ModelDecl {
            name: test_ident("User"),
            members: vec![
                ModelMember::Field(FieldDecl {
                    name: test_ident("id"),
                    r#type: test_named_type("Int"),
                    optional: false,
                    modifiers: vec![],
                    attrs: vec![FieldAttribute {
                        name: QualifiedIdent {
                            parts: vec![test_ident("id")],
                            span: test_span(),
                        },
                        args: None,
                        docs: None,
                        span: test_span(),
                    }],
                    docs: None,
                    span: test_span(),
                }),
                ModelMember::Field(FieldDecl {
                    name: test_ident("name"),
                    r#type: test_named_type("String"),
                    optional: true,
                    modifiers: vec![],
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
                ModelMember::Field(FieldDecl {
                    name: test_ident("tags"),
                    r#type: test_list_type(test_named_type("String")),
                    optional: false,
                    modifiers: vec![],
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
            ],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        assert!(table.add_model(&model).is_ok());

        // Test field lookup
        let id_field = table.lookup_field("User", "id");
        assert!(id_field.is_some());

        let name_field = table.lookup_field("User", "name");
        assert!(name_field.is_some());

        let nonexistent_field = table.lookup_field("User", "email");
        assert!(nonexistent_field.is_none());

        // Test field properties
        if let Some(field) = id_field
            && let SymbolType::Field(field_symbol) = &field.symbol_type
        {
            assert_eq!(field_symbol.parent_model, "User");
            assert!(!field_symbol.is_optional);
            assert!(!field_symbol.is_list);
            assert_eq!(field_symbol.attribute_count, 1);
        }

        if let Some(field) = name_field
            && let SymbolType::Field(field_symbol) = &field.symbol_type
        {
            assert!(field_symbol.is_optional);
            assert!(!field_symbol.is_list);
        }

        let tags_field = table.lookup_field("User", "tags").unwrap();
        if let SymbolType::Field(field_symbol) = &tags_field.symbol_type {
            assert!(field_symbol.is_list);
            assert!(!field_symbol.is_optional);
        }

        // Test model fields iterator
        let fields: Vec<_> = table.model_fields("User").unwrap().collect();
        assert_eq!(fields.len(), 3);

        // Test nonexistent model
        assert!(table.model_fields("NonExistentModel").is_none());
    }

    #[test]
    fn test_duplicate_fields_in_model() {
        let mut table = SymbolTable::new();

        let model = ModelDecl {
            name: test_ident("User"),
            members: vec![
                ModelMember::Field(FieldDecl {
                    name: test_ident("id"),
                    r#type: test_named_type("Int"),
                    optional: false,
                    modifiers: vec![],
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
                ModelMember::Field(FieldDecl {
                    name: test_ident("id"), // Duplicate field name
                    r#type: test_named_type("String"),
                    optional: false,
                    modifiers: vec![],
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
            ],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        let result = table.add_model(&model);
        assert!(result.is_err());

        if let Err(SymbolError::DuplicateSymbol { name, scope, .. }) = result {
            assert_eq!(name, "id");
            assert_eq!(scope, "User");
        } else {
            panic!("Expected DuplicateSymbol error");
        }
    }

    #[test]
    fn test_iterators() {
        let mut table = SymbolTable::new();

        // Add models
        let user_model = ModelDecl {
            name: test_ident("User"),
            members: vec![],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        let post_model = ModelDecl {
            name: test_ident("Post"),
            members: vec![],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        table.add_model(&user_model).unwrap();
        table.add_model(&post_model).unwrap();

        // Add enums
        let role_enum = EnumDecl {
            name: test_ident("Role"),
            members: vec![EnumMember::Value(EnumValue {
                name: test_ident("ADMIN"),
                attrs: vec![],
                docs: None,
                span: test_span(),
            })],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        table.add_enum(&role_enum).unwrap();

        // Test model iterator
        let models: Vec<_> = table.models().collect();
        assert_eq!(models.len(), 2);
        let model_names: Vec<_> =
            models.iter().map(|(name, _)| name.as_str()).collect();
        assert!(model_names.contains(&"User"));
        assert!(model_names.contains(&"Post"));

        // Test enum iterator
        let enums: Vec<_> = table.enums().collect();
        assert_eq!(enums.len(), 1);
        assert_eq!(enums[0].0, "Role");

        // Test enum values iterator
        let role_values: Vec<_> = table.enum_values("Role").unwrap().collect();
        assert_eq!(role_values.len(), 1);
        assert_eq!(role_values[0].0, "ADMIN");
    }

    #[test]
    fn test_symbol_creation_methods() {
        // Test builtin type symbol
        let string_symbol = Symbol::new_builtin_type("String");
        assert_eq!(string_symbol.name, "String");
        assert!(matches!(
            string_symbol.symbol_type,
            SymbolType::BuiltinType(_)
        ));
        assert_eq!(string_symbol.visibility, Visibility::Public);
        assert!(string_symbol.metadata.is_builtin);

        // Test builtin function symbol
        let now_symbol = Symbol::new_builtin_function("now");
        assert_eq!(now_symbol.name, "now");
        assert!(matches!(
            now_symbol.symbol_type,
            SymbolType::BuiltinFunction(_)
        ));
        assert!(now_symbol.metadata.is_builtin);

        // Test enum value symbol
        let enum_value = EnumValue {
            name: test_ident("ADMIN"),
            attrs: vec![],
            docs: None,
            span: test_span(),
        };
        let value_symbol = Symbol::new_enum_value(&enum_value, "Role");
        assert_eq!(value_symbol.name, "ADMIN");
        if let SymbolType::EnumValue(ev) = &value_symbol.symbol_type {
            assert_eq!(ev.parent_enum, "Role");
            assert_eq!(ev.attribute_count, 0);
        }
    }

    #[test]
    fn test_model_primary_key_detection() {
        let mut table = SymbolTable::new();

        // Model with primary key
        let model_with_pk = ModelDecl {
            name: test_ident("User"),
            members: vec![ModelMember::Field(FieldDecl {
                name: test_ident("id"),
                r#type: test_named_type("Int"),
                optional: false,
                modifiers: vec![],
                attrs: vec![FieldAttribute {
                    name: QualifiedIdent {
                        parts: vec![test_ident("id")],
                        span: test_span(),
                    },
                    args: None,
                    docs: None,
                    span: test_span(),
                }],
                docs: None,
                span: test_span(),
            })],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        table.add_model(&model_with_pk).unwrap();
        let symbol = table.lookup_global("User").unwrap();
        if let SymbolType::Model(model_symbol) = &symbol.symbol_type {
            assert!(model_symbol.has_primary_key);
            assert_eq!(model_symbol.field_count, 1);
        }
    }

    #[test]
    fn test_builtin_symbols() {
        let table = SymbolTable::new();

        // Test scalar types
        let scalar_types = [
            "String", "Int", "Float", "Boolean", "DateTime", "Json", "Bytes",
            "Decimal", "BigInt", "Uuid",
        ];
        for scalar_type in &scalar_types {
            assert!(
                table.contains(scalar_type),
                "Should contain {scalar_type}"
            );
            let symbol = table.lookup_global(scalar_type).unwrap();
            assert!(matches!(symbol.symbol_type, SymbolType::BuiltinType(_)));
        }

        // Test built-in functions
        let functions = ["now", "autoincrement", "cuid", "uuid"];
        for function in &functions {
            assert!(table.contains(function), "Should contain {function}");
            let symbol = table.lookup_global(function).unwrap();
            assert!(matches!(
                symbol.symbol_type,
                SymbolType::BuiltinFunction(_)
            ));
        }
    }

    #[test]
    fn test_symbol_metadata() {
        // Test default metadata
        let default_meta = SymbolMetadata::new();
        assert!(!default_meta.is_builtin);
        assert!(default_meta.documentation.is_none());
        assert!(default_meta.tags.is_empty());

        let default_via_trait = SymbolMetadata::default();
        assert!(!default_via_trait.is_builtin);

        // Test builtin metadata
        let builtin_meta = SymbolMetadata::builtin();
        assert!(builtin_meta.is_builtin);
        assert!(builtin_meta.documentation.is_none());
        assert!(builtin_meta.tags.is_empty());
    }

    #[test]
    fn test_symbol_error_display() {
        let duplicate_error = SymbolError::DuplicateSymbol {
            name: "User".to_string(),
            scope: "global".to_string(),
            existing_span: test_span(),
            new_span: test_span(),
        };

        let display_str = format!("{duplicate_error}");
        assert!(
            display_str.contains("Duplicate symbol 'User' in scope 'global'")
        );

        let not_found_error = SymbolError::SymbolNotFound {
            name: "NonExistent".to_string(),
            scope: "global".to_string(),
        };

        let display_str = format!("{not_found_error}");
        assert!(
            display_str
                .contains("Symbol 'NonExistent' not found in scope 'global'")
        );

        let invalid_op_error = SymbolError::InvalidOperation {
            message: "Cannot perform this operation".to_string(),
        };

        let display_str = format!("{invalid_op_error}");
        assert!(display_str.contains(
            "Invalid symbol operation: Cannot perform this operation"
        ));
    }

    #[test]
    fn test_symbol_error_trait() {
        let error = SymbolError::DuplicateSymbol {
            name: "Test".to_string(),
            scope: "global".to_string(),
            existing_span: test_span(),
            new_span: test_span(),
        };

        // Test that it implements std::error::Error
        let _: &dyn std::error::Error = &error;
    }

    #[test]
    fn test_enum_categories() {
        // Test TypeCategory
        assert_eq!(TypeCategory::Scalar, TypeCategory::Scalar);
        assert_ne!(TypeCategory::Scalar, TypeCategory::Composite);

        // Test Debug
        assert_eq!(format!("{:?}", TypeCategory::Scalar), "Scalar");
        assert_eq!(format!("{:?}", TypeCategory::Composite), "Composite");

        // Test FunctionCategory
        assert_eq!(FunctionCategory::Generator, FunctionCategory::Generator);
        assert_ne!(FunctionCategory::Generator, FunctionCategory::Transformer);

        assert_eq!(format!("{:?}", FunctionCategory::Generator), "Generator");
        assert_eq!(
            format!("{:?}", FunctionCategory::Transformer),
            "Transformer"
        );

        // Test Visibility
        assert_eq!(Visibility::Public, Visibility::Public);
        assert_ne!(Visibility::Public, Visibility::Private);

        assert_eq!(format!("{:?}", Visibility::Public), "Public");
        assert_eq!(format!("{:?}", Visibility::Private), "Private");
    }

    #[test]
    fn test_symbol_type_variants() {
        let builtin_type = SymbolType::BuiltinType(BuiltinTypeSymbol {
            type_category: TypeCategory::Scalar,
        });

        let builtin_function =
            SymbolType::BuiltinFunction(BuiltinFunctionSymbol {
                function_category: FunctionCategory::Generator,
            });

        let type_alias = SymbolType::TypeAlias(TypeAliasSymbol {
            target_type: "String".to_string(),
        });

        // Test pattern matching works
        match builtin_type {
            SymbolType::BuiltinType(_) => (),
            _ => panic!("Expected BuiltinType"),
        }

        match builtin_function {
            SymbolType::BuiltinFunction(_) => (),
            _ => panic!("Expected BuiltinFunction"),
        }

        match type_alias {
            SymbolType::TypeAlias(_) => (),
            _ => panic!("Expected TypeAlias"),
        }
    }

    #[test]
    fn test_symbol_table_default() {
        let table1 = SymbolTable::new();
        let table2 = SymbolTable::default();

        // Both should have the same built-in symbols
        assert_eq!(table1.contains("String"), table2.contains("String"));
        assert_eq!(table1.contains("now"), table2.contains("now"));
    }

    #[test]
    fn test_complex_symbol_counting() {
        let mut table = SymbolTable::new();
        let initial_count = table.total_symbol_count();

        // Add a model with fields
        let model = ModelDecl {
            name: test_ident("User"),
            members: vec![
                ModelMember::Field(FieldDecl {
                    name: test_ident("id"),
                    r#type: test_named_type("Int"),
                    optional: false,
                    modifiers: vec![],
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
                ModelMember::Field(FieldDecl {
                    name: test_ident("name"),
                    r#type: test_named_type("String"),
                    optional: true,
                    modifiers: vec![],
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
            ],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        table.add_model(&model).unwrap();

        // Add an enum with values
        let enum_decl = EnumDecl {
            name: test_ident("Role"),
            members: vec![
                EnumMember::Value(EnumValue {
                    name: test_ident("ADMIN"),
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
                EnumMember::Value(EnumValue {
                    name: test_ident("USER"),
                    attrs: vec![],
                    docs: None,
                    span: test_span(),
                }),
            ],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        table.add_enum(&enum_decl).unwrap();

        // Total count should be: initial + 1 model + 2 fields + 1 enum + 2 enum values = initial + 6
        assert_eq!(table.total_symbol_count(), initial_count + 6);
    }
}
