//! Type resolution and validation system.
//!
//! The type resolver handles resolving type references in the schema,
//! building a complete type system, and detecting type-related errors
//! such as circular dependencies and unknown types.

use crate::core::parser::ast::{NamedType, TypeRef};
use crate::core::semantic_analyzer::symbol_table::{SymbolTable, SymbolType};
use std::collections::{HashMap, HashSet};

/// Type resolver for schema analysis.
///
/// The type resolver maintains a cache of resolved types and handles
/// complex type resolution including generic types, constraints,
/// and dependency analysis.
#[derive(Debug, Clone)]
pub struct TypeResolver {
    /// Cache of resolved types
    resolved_types: HashMap<TypeRef, ResolvedType>,

    /// Type dependency graph for circular dependency detection
    type_dependencies: HashMap<String, HashSet<String>>,

    /// Type constraints and validation rules
    type_constraints: HashMap<String, TypeConstraints>,
}

impl TypeResolver {
    /// Create a new type resolver.
    #[must_use]
    pub fn new() -> Self {
        Self {
            resolved_types: HashMap::new(),
            type_dependencies: HashMap::new(),
            type_constraints: HashMap::new(),
        }
    }

    /// Resolve a type reference against the symbol table.
    ///
    /// # Errors
    ///
    /// Returns a `TypeResolutionError` if the type cannot be resolved.
    pub fn resolve_type(
        &mut self,
        type_ref: &TypeRef,
        symbol_table: &SymbolTable,
    ) -> Result<ResolvedType, TypeResolutionError> {
        // Check cache first
        if let Some(resolved) = self.resolved_types.get(type_ref) {
            return Ok(resolved.clone());
        }

        let resolved = self.resolve_type_uncached(type_ref, symbol_table)?;
        self.resolved_types
            .insert(type_ref.clone(), resolved.clone());
        Ok(resolved)
    }

    /// Resolve a type reference without using the cache.
    fn resolve_type_uncached(
        &mut self,
        type_ref: &TypeRef,
        symbol_table: &SymbolTable,
    ) -> Result<ResolvedType, TypeResolutionError> {
        match type_ref {
            TypeRef::Named(named_type) => {
                Self::resolve_named_type(named_type, symbol_table)
            }
            TypeRef::List(list_type) => {
                let element_type =
                    self.resolve_type(&list_type.inner, symbol_table)?;
                Ok(ResolvedType::List(Box::new(element_type)))
            }
        }
    }

    /// Resolve a named type reference.
    fn resolve_named_type(
        named_type: &NamedType,
        symbol_table: &SymbolTable,
    ) -> Result<ResolvedType, TypeResolutionError> {
        let type_name = &named_type.name.parts[0].text;

        // Look up the type in the symbol table
        if let Some(symbol) = symbol_table.lookup_global(type_name) {
            match &symbol.symbol_type {
                SymbolType::Model(_) => {
                    Ok(ResolvedType::Model(type_name.clone()))
                }
                SymbolType::Enum(_) => {
                    Ok(ResolvedType::Enum(type_name.clone()))
                }
                SymbolType::BuiltinType(_) => {
                    // Map to appropriate scalar type
                    let scalar_type = Self::map_builtin_to_scalar(type_name)?;
                    Ok(ResolvedType::Scalar(scalar_type))
                }
                SymbolType::TypeAlias(alias) => {
                    // For now, just resolve to the target type name
                    // Full alias resolution would require recursive resolution
                    Ok(ResolvedType::Alias {
                        name: type_name.clone(),
                        target: alias.target_type.clone(),
                    })
                }
                _ => Err(TypeResolutionError::NotAType {
                    name: type_name.clone(),
                    actual_symbol_type: format!("{:?}", symbol.symbol_type),
                }),
            }
        } else {
            Err(TypeResolutionError::UnknownType {
                name: type_name.clone(),
            })
        }
    }

    /// Map a built-in type name to a scalar type.
    fn map_builtin_to_scalar(
        type_name: &str,
    ) -> Result<ScalarType, TypeResolutionError> {
        match type_name {
            "String" => Ok(ScalarType::String),
            "Int" => Ok(ScalarType::Int),
            "Float" => Ok(ScalarType::Float),
            "Boolean" => Ok(ScalarType::Boolean),
            "DateTime" => Ok(ScalarType::DateTime),
            "Json" => Ok(ScalarType::Json),
            "Bytes" => Ok(ScalarType::Bytes),
            "Decimal" => Ok(ScalarType::Decimal),
            "BigInt" => Ok(ScalarType::BigInt),
            "Uuid" => Ok(ScalarType::Uuid),
            _ => Err(TypeResolutionError::UnknownBuiltinType {
                name: type_name.to_string(),
            }),
        }
    }

    /// Add a type dependency edge for cycle detection.
    pub fn add_type_dependency(&mut self, from: String, to: String) {
        self.type_dependencies.entry(from).or_default().insert(to);
    }

    /// Check for circular type dependencies.
    ///
    /// # Errors
    ///
    /// Returns a `TypeResolutionError` if circular dependencies are detected.
    pub fn check_circular_dependencies(
        &self,
    ) -> Result<(), TypeResolutionError> {
        for start_type in self.type_dependencies.keys() {
            if self.has_circular_dependency(start_type, &mut HashSet::new())? {
                let cycle = self.find_cycle(start_type);
                return Err(TypeResolutionError::CircularDependency { cycle });
            }
        }
        Ok(())
    }

    /// Check if a type has a circular dependency.
    fn has_circular_dependency(
        &self,
        type_name: &str,
        visited: &mut HashSet<String>,
    ) -> Result<bool, TypeResolutionError> {
        if visited.contains(type_name) {
            return Ok(true);
        }

        visited.insert(type_name.to_string());

        if let Some(dependencies) = self.type_dependencies.get(type_name) {
            for dep in dependencies {
                if self.has_circular_dependency(dep, visited)? {
                    return Ok(true);
                }
            }
        }

        visited.remove(type_name);
        Ok(false)
    }

    /// Find the actual cycle path for error reporting.
    fn find_cycle(&self, start_type: &str) -> Vec<String> {
        let mut path = Vec::new();
        let mut visited = HashSet::new();

        if self.find_cycle_path(start_type, &mut path, &mut visited) {
            path
        } else {
            // This shouldn't happen if has_circular_dependency returned true
            vec![start_type.to_string()]
        }
    }

    /// Find the cycle path recursively.
    fn find_cycle_path(
        &self,
        type_name: &str,
        path: &mut Vec<String>,
        visited: &mut HashSet<String>,
    ) -> bool {
        if path.contains(&type_name.to_string()) {
            path.push(type_name.to_string());
            return true;
        }

        if visited.contains(type_name) {
            return false;
        }

        visited.insert(type_name.to_string());
        path.push(type_name.to_string());

        if let Some(dependencies) = self.type_dependencies.get(type_name) {
            for dep in dependencies {
                if self.find_cycle_path(dep, path, visited) {
                    return true;
                }
            }
        }

        path.pop();
        false
    }

    /// Get type constraints for a specific type.
    #[must_use]
    pub fn get_constraints(&self, type_name: &str) -> Option<&TypeConstraints> {
        self.type_constraints.get(type_name)
    }

    /// Set type constraints for a specific type.
    pub fn set_constraints(
        &mut self,
        type_name: String,
        constraints: TypeConstraints,
    ) {
        self.type_constraints.insert(type_name, constraints);
    }

    /// Validate type compatibility between two types.
    #[must_use]
    pub fn are_compatible(from: &ResolvedType, to: &ResolvedType) -> bool {
        match (from, to) {
            // Same types are always compatible
            (a, b) if a == b => true,

            // Optional can accept the inner type
            (inner, ResolvedType::Optional(opt_inner)) => {
                Self::are_compatible(inner, opt_inner)
            }

            // List element compatibility
            (ResolvedType::List(a), ResolvedType::List(b)) => {
                Self::are_compatible(a, b)
            }

            // Scalar type compatibility rules
            (
                ResolvedType::Scalar(ScalarType::Int),
                ResolvedType::Scalar(ScalarType::Float | ScalarType::BigInt),
            ) => true,

            // No other implicit conversions allowed
            _ => false,
        }
    }

    /// Clear the resolution cache.
    pub fn clear_cache(&mut self) {
        self.resolved_types.clear();
    }

    /// Get statistics about the type resolver.
    #[must_use]
    pub fn stats(&self) -> TypeResolverStats {
        TypeResolverStats {
            cached_types: self.resolved_types.len(),
            dependency_edges: self
                .type_dependencies
                .values()
                .map(std::collections::HashSet::len)
                .sum(),
            constraint_count: self.type_constraints.len(),
        }
    }
}

impl Default for TypeResolver {
    fn default() -> Self {
        Self::new()
    }
}

/// A fully resolved type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ResolvedType {
    /// Scalar type (built-in primitive)
    Scalar(ScalarType),

    /// Model reference
    Model(String),

    /// Enum reference
    Enum(String),

    /// List of another type
    List(Box<ResolvedType>),

    /// Optional (nullable) type
    Optional(Box<ResolvedType>),

    /// Type alias
    Alias { name: String, target: String },

    /// Composite type (for complex scenarios)
    Composite(CompositeType),
}

impl ResolvedType {
    /// Check if this type is optional (nullable).
    #[must_use]
    pub fn is_optional(&self) -> bool {
        matches!(self, ResolvedType::Optional(_))
    }

    /// Check if this type is a list.
    #[must_use]
    pub fn is_list(&self) -> bool {
        matches!(self, ResolvedType::List(_))
    }

    /// Check if this type is a scalar.
    #[must_use]
    pub fn is_scalar(&self) -> bool {
        matches!(self, ResolvedType::Scalar(_))
    }

    /// Get the underlying type, removing optional wrapper.
    #[must_use]
    pub fn unwrap_optional(&self) -> &ResolvedType {
        match self {
            ResolvedType::Optional(inner) => inner.unwrap_optional(),
            other => other,
        }
    }

    /// Get a human-readable name for this type.
    #[must_use]
    pub fn display_name(&self) -> String {
        match self {
            ResolvedType::Scalar(scalar) => scalar.display_name(),
            ResolvedType::Model(name)
            | ResolvedType::Enum(name)
            | ResolvedType::Alias { name, .. } => name.clone(),
            ResolvedType::List(inner) => format!("{}[]", inner.display_name()),
            ResolvedType::Optional(inner) => {
                format!("{}?", inner.display_name())
            }
            ResolvedType::Composite(comp) => comp.name.clone(),
        }
    }
}

/// Built-in scalar types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarType {
    String,
    Int,
    Float,
    Boolean,
    DateTime,
    Json,
    Bytes,
    Decimal,
    BigInt,
    Uuid,
}

impl ScalarType {
    /// Get the display name for this scalar type.
    #[must_use]
    pub fn display_name(self) -> String {
        match self {
            ScalarType::String => "String".to_string(),
            ScalarType::Int => "Int".to_string(),
            ScalarType::Float => "Float".to_string(),
            ScalarType::Boolean => "Boolean".to_string(),
            ScalarType::DateTime => "DateTime".to_string(),
            ScalarType::Json => "Json".to_string(),
            ScalarType::Bytes => "Bytes".to_string(),
            ScalarType::Decimal => "Decimal".to_string(),
            ScalarType::BigInt => "BigInt".to_string(),
            ScalarType::Uuid => "Uuid".to_string(),
        }
    }

    /// Check if this scalar type supports null values by default.
    #[must_use]
    pub fn is_nullable_by_default(self) -> bool {
        // In Prisma, most types are non-nullable by default
        false
    }

    /// Get the category of this scalar type.
    #[must_use]
    pub fn category(self) -> ScalarCategory {
        match self {
            ScalarType::String | ScalarType::Uuid => ScalarCategory::Text,
            ScalarType::Int | ScalarType::BigInt => ScalarCategory::Integer,
            ScalarType::Float | ScalarType::Decimal => ScalarCategory::Decimal,
            ScalarType::Boolean => ScalarCategory::Boolean,
            ScalarType::DateTime => ScalarCategory::DateTime,
            ScalarType::Json => ScalarCategory::Json,
            ScalarType::Bytes => ScalarCategory::Binary,
        }
    }
}

/// Categories of scalar types for validation rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarCategory {
    Text,
    Integer,
    Decimal,
    Boolean,
    DateTime,
    Json,
    Binary,
}

/// Composite type for complex scenarios.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CompositeType {
    pub name: String,
    pub fields: Vec<CompositeField>,
}

/// Field in a composite type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CompositeField {
    pub name: String,
    pub field_type: Box<ResolvedType>,
    pub is_optional: bool,
}

/// Type constraints for validation.
#[derive(Debug, Clone)]
pub struct TypeConstraints {
    /// Whether the type can be null
    pub nullable: bool,

    /// Whether the type can be used in lists
    pub listable: bool,

    /// Valid attribute names for this type
    pub valid_attributes: Vec<String>,

    /// Database-specific constraints
    pub database_constraints: HashMap<String, String>,
}

impl Default for TypeConstraints {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeConstraints {
    /// Create default constraints for a type.
    #[must_use]
    pub fn new() -> Self {
        Self {
            nullable: false,
            listable: true,
            valid_attributes: Vec::new(),
            database_constraints: HashMap::new(),
        }
    }

    /// Create constraints for a scalar type.
    #[must_use]
    pub fn for_scalar(scalar: ScalarType) -> Self {
        let mut constraints = Self::new();

        // Add common scalar attributes
        constraints.valid_attributes.extend([
            "id".to_string(),
            "unique".to_string(),
            "default".to_string(),
        ]);

        // Add type-specific attributes
        match scalar {
            ScalarType::String => {
                constraints.valid_attributes.push("db.VarChar".to_string());
                constraints.valid_attributes.push("db.Text".to_string());
            }
            ScalarType::Int | ScalarType::BigInt => {
                constraints.valid_attributes.push("db.Integer".to_string());
                constraints
                    .valid_attributes
                    .push("autoincrement".to_string());
            }
            ScalarType::DateTime => {
                constraints.valid_attributes.push("updatedAt".to_string());
            }
            _ => {}
        }

        constraints
    }
}

/// Statistics about the type resolver.
#[derive(Debug, Clone)]
pub struct TypeResolverStats {
    pub cached_types: usize,
    pub dependency_edges: usize,
    pub constraint_count: usize,
}

/// Errors that can occur during type resolution.
#[derive(Debug, Clone)]
pub enum TypeResolutionError {
    /// Unknown type name
    UnknownType { name: String },

    /// Symbol exists but is not a type
    NotAType {
        name: String,
        actual_symbol_type: String,
    },

    /// Unknown built-in type
    UnknownBuiltinType { name: String },

    /// Circular type dependency
    CircularDependency { cycle: Vec<String> },

    /// Type constraint violation
    ConstraintViolation {
        type_name: String,
        constraint: String,
        message: String,
    },

    /// Incompatible types
    IncompatibleTypes {
        from: String,
        to: String,
        context: String,
    },
}

impl std::fmt::Display for TypeResolutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeResolutionError::UnknownType { name } => {
                write!(f, "Unknown type '{name}'")
            }
            TypeResolutionError::NotAType {
                name,
                actual_symbol_type,
            } => {
                write!(
                    f,
                    "'{name}' is not a type (it's a {actual_symbol_type})"
                )
            }
            TypeResolutionError::UnknownBuiltinType { name } => {
                write!(f, "Unknown built-in type '{name}'")
            }
            TypeResolutionError::CircularDependency { cycle } => {
                write!(f, "Circular type dependency: {}", cycle.join(" -> "))
            }
            TypeResolutionError::ConstraintViolation {
                type_name,
                constraint,
                message,
            } => {
                write!(
                    f,
                    "Type '{type_name}' violates constraint '{constraint}': {message}"
                )
            }
            TypeResolutionError::IncompatibleTypes { from, to, context } => {
                write!(
                    f,
                    "Incompatible types: cannot convert '{from}' to '{to}' in {context}"
                )
            }
        }
    }
}

impl std::error::Error for TypeResolutionError {}
