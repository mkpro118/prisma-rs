//! Abstract Syntax Tree (AST) for Prisma schema parsing.
//!
//! The parser produces a typed, span-carrying AST for downstream
//! analysis and diagnostics. Every node exposes a source `SymbolSpan`
//! and a stable node kind via the `AstNode` interface. Container nodes
//! (blocks, lists, composite expressions) participate in traversal; leaf
//! nodes hold scalar values with spans. Ordering reflects source order.
//!
//! Spans use 1-based line and column. Spans are opaque bounds intended
//! for diagnostics; do not assume inclusive/exclusive semantics beyond
//! ordering guarantees. Nodes own their children; cloning is shallow
//! on containers and deep on leaves where needed.
//!
//! ## Examples
//! Build a minimal schema AST with a single model and field.
//! ```
//! # use prisma_rs::core::parser::ast::*;
//! # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
//! // Helper to make spans for AST Nodes
//! let sp = |s: (u32, u32), e: (u32, u32)| SymbolSpan {
//!     start: SymbolLocation {
//!         line: s.0,
//!         column: s.1,
//!     },
//!     end: SymbolLocation {
//!         line: e.0,
//!         column: e.1,
//!     },
//! };
//!
//! let name = Ident {
//!     text: "User".into(),
//!     span: sp((1, 7), (1, 11)),
//! };
//!
//! let ty = TypeRef::Named(NamedType {
//!     name: QualifiedIdent {
//!         parts: vec![Ident {
//!             text: "String".into(),
//!             span: sp((2, 12), (2, 18)),
//!         }],
//!         span: sp((2, 12), (2, 18)),
//!     },
//!     span: sp((2, 12), (2, 20)),
//! });
//!
//! let field = FieldDecl {
//!     name: Ident {
//!         text: "id".into(),
//!         span: sp((2, 3), (2, 5)),
//!     },
//!     r#type: ty,
//!     optional: false,
//!     modifiers: vec![],
//!     attrs: vec![],
//!     docs: None,
//!     span: sp((2, 3), (2, 20)),
//! };
//!
//! let model = ModelDecl {
//!     name,
//!     members: vec![ModelMember::Field(field)],
//!     attrs: vec![],
//!     docs: None,
//!     span: sp((1, 1), (3, 1)),
//! };
//!
//! let schema = Schema {
//!     declarations: vec![Declaration::Model(model)],
//!     span: sp((1, 1), (3, 1)),
//! };
//!
//! assert_eq!(schema.declarations.len(), 1);
//! ```

use crate::core::scanner::tokens::SymbolSpan;
use crate::{AstContainerNode, AstLeafNode};
use std::fmt::Debug;

/// Marker trait for types that have a span field.
pub trait HasSpan {
    /// Return the source span covered by this value.
    ///
    /// Spans are used to report diagnostics and preserve source mapping.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::parser::ast::*;
    /// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
    /// let span = SymbolSpan {
    ///     start: SymbolLocation { line: 1, column: 1 },
    ///     end: SymbolLocation { line: 1, column: 4 },
    /// };
    /// let id = Ident {
    ///     text: "User".into(),
    ///     span: span.clone(),
    /// };
    /// assert_eq!(id.span(), &span);
    /// ```
    fn span(&self) -> &SymbolSpan;
}

/// Marker trait for types that have a node type name.
pub trait HasNodeType {
    /// Return a stable node-kind name for debugging and traversal.
    fn node_type(&self) -> &'static str;
}

/// Common interface for all AST nodes.
///
/// Provides span access and a stable node kind. Container nodes override
/// `is_container` to signal that they may hold children.
pub trait AstNode: Debug + HasSpan + HasNodeType {
    /// Returns true if this node can contain child nodes.
    fn is_container(&self) -> bool {
        false
    }
}

/// Trait for nodes that support visitor pattern traversal.
///
/// Separated from `AstNode` to keep object safety for the main trait.
pub trait AstVisitable: AstNode {
    /// Accepts a visitor for traversal operations.
    ///
    /// Default implementation does nothing. Container nodes should override
    /// to visit their children in source order.
    fn accept(&self, _visitor: &mut dyn AstVisitor) {}
}

/// Visitor trait for AST traversal operations.
pub trait AstVisitor {
    /// Called when entering any AST node.
    fn visit_node(&mut self, _node: &dyn AstNode) {}
}

/// Boxed `AstNode` for heterogeneous collections and dynamic dispatch.
pub type BoxedAstNode = Box<dyn AstNode>;

/// Represent a complete Prisma schema.
///
/// Contains all top-level declarations in source order and a span over
/// the full input.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// let sp = |s: (u32, u32), e: (u32, u32)| SymbolSpan {
///     start: SymbolLocation {
///         line: s.0,
///         column: s.1,
///     },
///     end: SymbolLocation {
///         line: e.0,
///         column: e.1,
///     },
/// };
/// let schema = Schema {
///     declarations: vec![],
///     span: sp((1, 1), (1, 1)),
/// };
/// assert!(schema.declarations.is_empty());
/// ```
#[derive(Debug, Clone, AstContainerNode)]
pub struct Schema {
    /// All top-level declarations in source order.
    pub declarations: Vec<Declaration>,
    /// The span covering the entire schema.
    pub span: SymbolSpan,
}

/// A top-level schema declaration.
#[derive(Debug, Clone)]
pub enum Declaration {
    /// A model declaration: `model User { ... }`
    Model(ModelDecl),
    /// An enum declaration: `enum Role { ... }`
    Enum(EnumDecl),
    /// A datasource declaration: `datasource db { ... }`
    Datasource(DatasourceDecl),
    /// A generator declaration: `generator client { ... }`
    Generator(GeneratorDecl),
    /// An experimental type alias: `type UserId = String` (gated)
    Type(TypeDecl),
}

impl HasSpan for Declaration {
    fn span(&self) -> &SymbolSpan {
        match self {
            Declaration::Model(decl) => decl.span(),
            Declaration::Enum(decl) => decl.span(),
            Declaration::Datasource(decl) => decl.span(),
            Declaration::Generator(decl) => decl.span(),
            Declaration::Type(decl) => decl.span(),
        }
    }
}

impl HasNodeType for Declaration {
    fn node_type(&self) -> &'static str {
        match self {
            Declaration::Model(_) => "ModelDecl",
            Declaration::Enum(_) => "EnumDecl",
            Declaration::Datasource(_) => "DatasourceDecl",
            Declaration::Generator(_) => "GeneratorDecl",
            Declaration::Type(_) => "TypeDecl",
        }
    }
}

impl AstNode for Declaration {
    fn is_container(&self) -> bool {
        true
    }
}

impl AstVisitable for Declaration {
    fn accept(&self, visitor: &mut dyn AstVisitor) {
        visitor.visit_node(self);
        match self {
            Declaration::Model(decl) => decl.accept(visitor),
            Declaration::Enum(decl) => decl.accept(visitor),
            Declaration::Datasource(decl) => decl.accept(visitor),
            Declaration::Generator(decl) => decl.accept(visitor),
            Declaration::Type(decl) => decl.accept(visitor),
        }
    }
}

/// A model declaration with fields and attributes.
///
/// Holds field members, block attributes, optional docs, and a span covering
/// the whole declaration.
#[derive(Debug, Clone, AstContainerNode)]
pub struct ModelDecl {
    /// The model name.
    pub name: Ident,
    /// Model members (fields and block attributes) in source order.
    pub members: Vec<ModelMember>,
    /// Block-level attributes (`@@` attributes).
    pub attrs: Vec<BlockAttribute>,
    /// Associated documentation comments.
    pub docs: Option<Docs>,
    /// The span covering the entire model declaration.
    pub span: SymbolSpan,
}

/// A member within a model declaration.
#[derive(Debug, Clone)]
pub enum ModelMember {
    /// A field declaration: `id String @id`
    Field(FieldDecl),
    /// A block attribute: `@@unique([name, email])`
    BlockAttribute(BlockAttribute),
}

impl HasSpan for ModelMember {
    fn span(&self) -> &SymbolSpan {
        match self {
            ModelMember::Field(field) => field.span(),
            ModelMember::BlockAttribute(attr) => attr.span(),
        }
    }
}

impl HasNodeType for ModelMember {
    fn node_type(&self) -> &'static str {
        match self {
            ModelMember::Field(_) => "FieldDecl",
            ModelMember::BlockAttribute(_) => "BlockAttribute",
        }
    }
}

impl AstNode for ModelMember {
    fn is_container(&self) -> bool {
        true
    }
}

/// A field declaration within a model.
///
/// Contains name, type, optionality, modifiers, attributes, optional docs,
/// and a span over the field.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// # let sp = |s: (u32,u32), e: (u32,u32)| SymbolSpan {
/// #     start: SymbolLocation{ line: s.0, column: s.1 },
/// #     end: SymbolLocation{ line: e.0, column: e.1 },
/// # };
/// let field = FieldDecl {
///     name: Ident {
///         text: "id".into(),
///         span: sp((1, 3), (1, 5)),
///     },
///     r#type: TypeRef::Named(NamedType {
///         name: QualifiedIdent {
///             parts: vec![Ident {
///                 text: "String".into(),
///                 span: sp((1, 8), (1, 14)),
///             }],
///             span: sp((1, 8), (1, 14)),
///         },
///         span: sp((1, 8), (1, 16)),
///     }),
///     optional: false,
///     modifiers: vec![],
///     attrs: vec![],
///     docs: None,
///     span: sp((1, 3), (1, 16)),
/// };
/// assert_eq!(field.name.text, "id");
/// ```
#[derive(Debug, Clone, AstContainerNode)]
pub struct FieldDecl {
    /// The field name.
    pub name: Ident,
    /// The field type.
    pub r#type: TypeRef,
    /// Whether the field is optional (`?`).
    pub optional: bool,
    /// Field modifiers (reserved for future use).
    pub modifiers: Vec<FieldModifier>,
    /// Field-level attributes (`@` attributes).
    pub attrs: Vec<FieldAttribute>,
    /// Associated documentation comments.
    pub docs: Option<Docs>,
    /// The span covering the entire field declaration.
    pub span: SymbolSpan,
}

/// A field modifier (reserved for future use).
///
/// Parsed for forward-compatibility with future language features. Carries
/// a modifier name and span only; no semantics are attached yet.
#[derive(Debug, Clone, AstContainerNode)]
pub struct FieldModifier {
    /// The modifier name.
    pub name: Ident,
    /// The span of this modifier.
    pub span: SymbolSpan,
}

/// An enum declaration with values and attributes.
///
/// Contains enum values and optional block attributes in source order,
/// optional documentation, and a span covering the entire declaration.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// # let sp = |s:(u32,u32),e:(u32,u32)| SymbolSpan {
/// #     start: SymbolLocation{ line: s.0, column: s.1 },
/// #     end: SymbolLocation{ line: e.0, column: e.1 },
/// # };
/// let value = EnumValue {
///     name: Ident {
///         text: "ADMIN".into(),
///         span: sp((2, 3), (2, 8)),
///     },
///     attrs: vec![],
///     docs: None,
///     span: sp((2, 3), (2, 8)),
/// };
/// let en = EnumDecl {
///     name: Ident {
///         text: "Role".into(),
///         span: sp((1, 6), (1, 10)),
///     },
///     members: vec![EnumMember::Value(value)],
///     attrs: vec![],
///     docs: None,
///     span: sp((1, 1), (3, 1)),
/// };
/// assert_eq!(en.name.text, "Role");
/// ```
#[derive(Debug, Clone, AstContainerNode)]
pub struct EnumDecl {
    /// The enum name.
    pub name: Ident,
    /// Enum members (values and block attributes) in source order.
    pub members: Vec<EnumMember>,
    /// Block-level attributes (`@@` attributes).
    pub attrs: Vec<BlockAttribute>,
    /// Associated documentation comments.
    pub docs: Option<Docs>,
    /// The span covering the entire enum declaration.
    pub span: SymbolSpan,
}

/// A member within an enum declaration.
#[derive(Debug, Clone)]
pub enum EnumMember {
    /// An enum value: `ADMIN @map("admin")`
    Value(EnumValue),
    /// A block attribute: `@@map("user_role")`
    BlockAttribute(BlockAttribute),
}

impl HasSpan for EnumMember {
    fn span(&self) -> &SymbolSpan {
        match self {
            EnumMember::Value(value) => value.span(),
            EnumMember::BlockAttribute(attr) => attr.span(),
        }
    }
}

impl HasNodeType for EnumMember {
    fn node_type(&self) -> &'static str {
        match self {
            EnumMember::Value(_) => "EnumValue",
            EnumMember::BlockAttribute(_) => "BlockAttribute",
        }
    }
}

impl AstNode for EnumMember {
    fn is_container(&self) -> bool {
        true
    }
}

/// An enum value declaration.
///
/// Holds the value name, optional field-level attributes, optional docs,
/// and a span for the value.
#[derive(Debug, Clone, AstContainerNode)]
pub struct EnumValue {
    /// The value name.
    pub name: Ident,
    /// Field-level attributes (`@` attributes).
    pub attrs: Vec<FieldAttribute>,
    /// Associated documentation comments.
    pub docs: Option<Docs>,
    /// The span covering this enum value.
    pub span: SymbolSpan,
}

/// A datasource declaration.
///
/// Represents `datasource` blocks with configuration assignments.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// # let sp = |s: (u32,u32), e: (u32,u32)| SymbolSpan {
/// #     start: SymbolLocation { line:s.0, column:s.1 },
/// #     end: SymbolLocation{ line:e.0, column:e.1 },
/// # };
/// let key = Ident{ text: "provider".into(), span: sp((2,3),(2,11)) };
/// let val = Expr::StringLit(
///     StringLit{ value: "postgresql".into(), span: sp((2,14), (2,26)) }
/// );
/// let assign = Assignment { key, value: val, docs: None, span: sp((2,3),(2,26)) };
/// let ds = DatasourceDecl {
///     name: Ident{ text: "db".into(), span: sp((1,12),(1,14)) },
///     assignments: vec![assign],
///     docs: None,
///     span: sp((1,1),(3,1))
/// };
/// assert_eq!(ds.assignments.len(), 1);
/// ```
#[derive(Debug, Clone, AstContainerNode)]
pub struct DatasourceDecl {
    /// The datasource name.
    pub name: Ident,
    /// Configuration assignments in source order.
    pub assignments: Vec<Assignment>,
    /// Associated documentation comments.
    pub docs: Option<Docs>,
    /// The span covering the entire datasource declaration.
    pub span: SymbolSpan,
}

/// A generator declaration.
///
/// Represents `generator` blocks with configuration assignments.
#[derive(Debug, Clone, AstContainerNode)]
pub struct GeneratorDecl {
    /// The generator name.
    pub name: Ident,
    /// Configuration assignments in source order.
    pub assignments: Vec<Assignment>,
    /// Associated documentation comments.
    pub docs: Option<Docs>,
    /// The span covering the entire generator declaration.
    pub span: SymbolSpan,
}

/// An assignment within a datasource or generator.
///
/// Appears as `key = value` inside `datasource` and `generator` blocks.
/// Values are expressions; keys are identifiers.
#[derive(Debug, Clone, AstContainerNode)]
pub struct Assignment {
    /// The assignment key.
    pub key: Ident,
    /// The assignment value.
    pub value: Expr,
    /// Associated documentation comments.
    pub docs: Option<Docs>,
    /// The span covering this assignment.
    pub span: SymbolSpan,
}

/// An experimental type alias declaration (gated).
///
/// Represents `type Name = Type` declarations. The right-hand side is a
/// `TypeRef` which may be named or a list.
#[derive(Debug, Clone, AstContainerNode)]
pub struct TypeDecl {
    /// The type alias name.
    pub name: Ident,
    /// The aliased type.
    pub rhs: TypeRef,
    /// Associated documentation comments.
    pub docs: Option<Docs>,
    /// The span covering the entire type declaration.
    pub span: SymbolSpan,
}

/// A field-level attribute (`@attribute`).
///
/// Attributes may be qualified (e.g., `db.VarChar`) and can carry optional
/// arguments via `ArgList`.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// # let sp = |s: (u32,u32), e: (u32,u32)| SymbolSpan {
/// #     start: SymbolLocation { line:s.0, column:s.1 },
/// #     end: SymbolLocation{ line:e.0, column:e.1 },
/// # };
/// let name = QualifiedIdent{ parts: vec![
///         Ident { text: "map".into(), span: sp((1,2),(1,5)) }
///     ],
///     span: sp((1,2), (1,5))
/// };
/// let arg = Arg::Named(NamedArg {
///     name: Ident{ text: "name".into(), span: sp((1,6),(1,10)) },
///     value: Expr::StringLit(
///         StringLit{ value: "users".into(), span: sp((1,12),(1,19)) }
///     ),
///     span: sp((1,6),(1,19))
/// });
/// let attr = FieldAttribute{
///     name,
///     args: Some(ArgList{ items: vec![arg], span: sp((1,2),(1,20)) }),
///     docs: None,
///     span: sp((1,1),(1,20))
/// };
/// assert!(attr.args.as_ref().unwrap().items.len() == 1);
/// ```
#[derive(Debug, Clone, AstContainerNode)]
pub struct FieldAttribute {
    /// The attribute name (may be qualified like `db.VarChar`).
    pub name: QualifiedIdent,
    /// Optional argument list.
    pub args: Option<ArgList>,
    /// Associated documentation comments.
    pub docs: Option<Docs>,
    /// The span covering this attribute.
    pub span: SymbolSpan,
}

/// A block-level attribute (`@@attribute`).
///
/// Block attributes apply to models and enums and may be qualified. They
/// can carry optional arguments.
#[derive(Debug, Clone, AstContainerNode)]
pub struct BlockAttribute {
    /// The attribute name (may be qualified like `db.Index`).
    pub name: QualifiedIdent,
    /// Optional argument list.
    pub args: Option<ArgList>,
    /// Associated documentation comments.
    pub docs: Option<Docs>,
    /// The span covering this attribute.
    pub span: SymbolSpan,
}

/// A qualified identifier supporting namespacing (e.g., `db.VarChar`).
///
/// Provides helpers for detecting and extracting simple (single-part) names.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// # let sp = |s: (u32,u32), e: (u32,u32)| SymbolSpan {
/// #     start: SymbolLocation { line:s.0, column:s.1 },
/// #     end: SymbolLocation{ line:e.0, column:e.1 },
/// # };
/// let q = QualifiedIdent { parts: vec![
///         Ident { text: "String".into(), span: sp((1,1),(1,7)) }
///     ],
///     span: sp((1,1),(1,7))
/// };
/// assert!(q.is_simple());
/// assert_eq!(q.as_simple().unwrap().text, "String");
/// ```
#[derive(Debug, Clone, AstContainerNode)]
pub struct QualifiedIdent {
    /// The identifier parts (e.g., `["db", "VarChar"]`).
    pub parts: Vec<Ident>,
    /// The span covering the entire qualified identifier.
    pub span: SymbolSpan,
}

impl QualifiedIdent {
    /// Returns true if this is a simple (non-qualified) identifier.
    #[must_use]
    pub fn is_simple(&self) -> bool {
        self.parts.len() == 1
    }

    /// Returns the simple name if this is a single identifier.
    #[must_use]
    pub fn as_simple(&self) -> Option<&Ident> {
        if self.is_simple() {
            self.parts.first()
        } else {
            None
        }
    }
}

/// A type reference in field declarations or type aliases.
///
/// Either a named type or a list type.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// # let sp = |s: (u32,u32), e: (u32,u32)| SymbolSpan {
/// #     start: SymbolLocation { line:s.0, column:s.1 },
/// #     end: SymbolLocation{ line:e.0, column:e.1 },
/// # };
/// let named = TypeRef::Named(NamedType {
///     name: QualifiedIdent {
///         parts: vec![
///             Ident { text: "Int".into(), span: sp((1,1),(1,4)) }
///         ],
///         span: sp((1,1),(1,4))
///     },
///     span: sp((1,1),(1,4))
/// });
/// let list = TypeRef::List(
///     ListType { inner: Box::new(named.clone()), span: sp((1,1),(1,6)) }
/// );
/// assert_eq!(named.node_type(), "NamedType");
/// assert_eq!(list.node_type(), "ListType");
/// ```
#[derive(Debug, Clone)]
pub enum TypeRef {
    /// A named type (scalar, enum, or model reference).
    Named(NamedType),
    /// A list type (`Type[]`).
    List(ListType),
}

impl HasSpan for TypeRef {
    fn span(&self) -> &SymbolSpan {
        match self {
            TypeRef::Named(named) => named.span(),
            TypeRef::List(list) => list.span(),
        }
    }
}

impl HasNodeType for TypeRef {
    fn node_type(&self) -> &'static str {
        match self {
            TypeRef::Named(_) => "NamedType",
            TypeRef::List(_) => "ListType",
        }
    }
}

impl AstNode for TypeRef {
    fn is_container(&self) -> bool {
        true
    }
}

/// A named type reference.
///
/// Holds a qualified type name and a span over the reference.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// # let sp = |s: (u32,u32), e: (u32,u32)| SymbolSpan {
/// #     start: SymbolLocation { line:s.0, column:s.1 },
/// #     end: SymbolLocation{ line:e.0, column:e.1 },
/// # };
/// let nt = NamedType {
///     name: QualifiedIdent {
///         parts: vec![Ident{ text: "String".into(), span: sp((1,1),(1,7)) }],
///         span: sp((1,1),(1,7))
///     },
///     span: sp((1,1),(1,7))
/// };
/// assert_eq!(nt.node_type(), "NamedType");
/// ```
#[derive(Debug, Clone, AstContainerNode)]
pub struct NamedType {
    /// The type name (may be qualified for built-ins).
    pub name: QualifiedIdent,
    /// The span covering this type reference.
    pub span: SymbolSpan,
}

/// A list type reference (`Type[]`).
///
/// Wraps an inner `TypeRef` and carries a span over the whole list type.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// # let sp = |s: (u32,u32), e: (u32,u32)| SymbolSpan {
/// #     start: SymbolLocation { line:s.0, column:s.1 },
/// #     end: SymbolLocation{ line:e.0, column:e.1 },
/// # };
/// let inner = TypeRef::Named(NamedType {
///     name: QualifiedIdent {
///         parts: vec![Ident{ text: "Int".into(), span: sp((1,1),(1,4)) }],
///         span: sp((1,1),(1,4))
///     },
///     span: sp((1,1),(1,4))
/// });
/// let list = ListType { inner: Box::new(inner), span: sp((1,1),(1,6)) };
/// assert_eq!(list.node_type(), "ListType");
/// ```
#[derive(Debug, Clone, AstContainerNode)]
pub struct ListType {
    /// The inner type.
    pub inner: Box<TypeRef>,
    /// The span covering this list type.
    pub span: SymbolSpan,
}

/// An argument list for attributes or function calls.
///
/// Holds positional and named arguments in source order.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// # let sp = |s: (u32,u32), e: (u32,u32)| SymbolSpan {
/// #     start: SymbolLocation { line:s.0, column:s.1 },
/// #     end: SymbolLocation{ line:e.0, column:e.1 },
/// # };
/// let pos = Arg::Positional(PositionalArg {
///     value: Expr::BoolLit(
///         BoolLit { value: true, span: sp((1,1),(1,5)) }
///     ),
///     span: sp((1,1),(1,5))
/// });
/// let named = Arg::Named(NamedArg {
///     name: Ident{ text: "n".into(), span: sp((1,7),(1,8)) },
///     value: Expr::NullLit(NullLit{ span: sp((1,10),(1,14)) }),
///     span: sp((1,7),(1,14))
/// });
/// let args = ArgList { items: vec![pos, named], span: sp((1,1),(1,15)) };
/// assert_eq!(args.items.len(), 2);
/// ```
#[derive(Debug, Clone, AstContainerNode)]
pub struct ArgList {
    /// The arguments in source order.
    pub items: Vec<Arg>,
    /// The span covering the entire argument list including parentheses.
    pub span: SymbolSpan,
}

/// A single argument (positional or named).
#[derive(Debug, Clone)]
pub enum Arg {
    /// A positional argument: `"value"`
    Positional(PositionalArg),
    /// A named argument: `name: "value"`
    Named(NamedArg),
}

impl HasSpan for Arg {
    fn span(&self) -> &SymbolSpan {
        match self {
            Arg::Positional(arg) => arg.span(),
            Arg::Named(arg) => arg.span(),
        }
    }
}

impl HasNodeType for Arg {
    fn node_type(&self) -> &'static str {
        match self {
            Arg::Positional(_) => "PositionalArg",
            Arg::Named(_) => "NamedArg",
        }
    }
}

impl AstNode for Arg {
    fn is_container(&self) -> bool {
        true
    }
}

/// A positional argument.
///
/// Holds only a value expression and its span.
#[derive(Debug, Clone, AstContainerNode)]
pub struct PositionalArg {
    /// The argument value.
    pub value: Expr,
    /// The span covering this argument.
    pub span: SymbolSpan,
}

/// A named argument.
///
/// Holds a name identifier, a value expression, and a span.
#[derive(Debug, Clone, AstContainerNode)]
pub struct NamedArg {
    /// The argument name.
    pub name: Ident,
    /// The argument value.
    pub value: Expr,
    /// The span covering this named argument.
    pub span: SymbolSpan,
}

/// An expression used in assignments, arguments, and literals.
///
/// Variants include literals, identifier references, function calls,
/// arrays, and objects.
#[derive(Debug, Clone)]
pub enum Expr {
    /// A string literal.
    StringLit(StringLit),
    /// An integer literal.
    IntLit(IntLit),
    /// A floating-point literal.
    FloatLit(FloatLit),
    /// A boolean literal.
    BoolLit(BoolLit),
    /// A null literal.
    NullLit(NullLit),
    /// An identifier reference.
    IdentRef(IdentRef),
    /// A function call: `env("DATABASE_URL")`
    FuncCall(FuncCall),
    /// An array expression: `[1, 2, 3]`
    Array(ArrayExpr),
    /// An object expression: `{key: value}`
    Object(ObjectExpr),
}

impl HasSpan for Expr {
    fn span(&self) -> &SymbolSpan {
        match self {
            Expr::StringLit(lit) => lit.span(),
            Expr::IntLit(lit) => lit.span(),
            Expr::FloatLit(lit) => lit.span(),
            Expr::BoolLit(lit) => lit.span(),
            Expr::NullLit(lit) => lit.span(),
            Expr::IdentRef(ident) => ident.span(),
            Expr::FuncCall(call) => call.span(),
            Expr::Array(array) => array.span(),
            Expr::Object(object) => object.span(),
        }
    }
}

impl HasNodeType for Expr {
    fn node_type(&self) -> &'static str {
        match self {
            Expr::StringLit(_) => "StringLit",
            Expr::IntLit(_) => "IntLit",
            Expr::FloatLit(_) => "FloatLit",
            Expr::BoolLit(_) => "BoolLit",
            Expr::NullLit(_) => "NullLit",
            Expr::IdentRef(_) => "IdentRef",
            Expr::FuncCall(_) => "FuncCall",
            Expr::Array(_) => "ArrayExpr",
            Expr::Object(_) => "ObjectExpr",
        }
    }
}

impl AstNode for Expr {
    fn is_container(&self) -> bool {
        matches!(
            self,
            Expr::FuncCall(_)
                | Expr::Array(_)
                | Expr::Object(_)
                | Expr::IdentRef(_)
        )
    }
}

/// A string literal expression.
///
/// Stores the string without quotes and the span including quotes.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// # let sp = |s: (u32,u32), e: (u32,u32)| SymbolSpan {
/// #     start: SymbolLocation { line:s.0, column:s.1 },
/// #     end: SymbolLocation{ line:e.0, column:e.1 },
/// # };
/// let s = StringLit { value: "hello".into(), span: sp((1,1),(1,8)) };
/// assert_eq!(s.value, "hello");
/// ```
#[derive(Debug, Clone, AstLeafNode)]
pub struct StringLit {
    /// The string value (without quotes).
    pub value: String,
    /// The span including quotes.
    pub span: SymbolSpan,
}

/// An integer literal expression.
#[derive(Debug, Clone, AstLeafNode)]
pub struct IntLit {
    /// The integer value as a string (preserves original representation).
    pub value: String,
    /// The span of this literal.
    pub span: SymbolSpan,
}

/// A floating-point literal expression.
#[derive(Debug, Clone, AstLeafNode)]
pub struct FloatLit {
    /// The float value as a string (preserves original representation).
    pub value: String,
    /// The span of this literal.
    pub span: SymbolSpan,
}

/// A boolean literal expression.
#[derive(Debug, Clone, AstLeafNode)]
pub struct BoolLit {
    /// The boolean value.
    pub value: bool,
    /// The span of this literal.
    pub span: SymbolSpan,
}

/// A null literal expression.
#[derive(Debug, Clone, AstLeafNode)]
pub struct NullLit {
    /// The span of this literal.
    pub span: SymbolSpan,
}

/// An identifier reference expression.
///
/// The name may be qualified; the span covers the full reference.
#[derive(Debug, Clone, AstContainerNode)]
pub struct IdentRef {
    /// The referenced identifier (may be qualified).
    pub name: QualifiedIdent,
    /// The span of this reference.
    pub span: SymbolSpan,
}

/// A function call expression.
///
/// Contains a callee (possibly qualified), optional arguments, and a span.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::*;
/// # use prisma_rs::core::scanner::tokens::{SymbolLocation, SymbolSpan};
/// # let sp = |s: (u32,u32), e: (u32,u32)| SymbolSpan {
/// #     start: SymbolLocation { line:s.0, column:s.1 },
/// #     end: SymbolLocation{ line:e.0, column:e.1 },
/// # };
/// let callee = QualifiedIdent {
///     parts: vec![Ident{ text: "now".into(), span: sp((1,1),(1,4)) }],
///     span: sp((1,1),(1,4))
/// };
/// let call = FuncCall { callee, args: None, span: sp((1,1),(1,6)) };
/// assert_eq!(call.node_type(), "FuncCall");
/// ```
#[derive(Debug, Clone, AstContainerNode)]
pub struct FuncCall {
    /// The function name (may be qualified like `db.VarChar`).
    pub callee: QualifiedIdent,
    /// Optional argument list.
    pub args: Option<ArgList>,
    /// The span covering the entire function call.
    pub span: SymbolSpan,
}

/// An array expression.
///
/// Stores elements in source order and the span including brackets.
#[derive(Debug, Clone, AstContainerNode)]
pub struct ArrayExpr {
    /// The array elements in source order.
    pub elements: Vec<Expr>,
    /// The span including brackets.
    pub span: SymbolSpan,
}

/// An object expression.
///
/// Stores entries in source order and the span including braces.
#[derive(Debug, Clone, AstContainerNode)]
pub struct ObjectExpr {
    /// The object entries in source order.
    pub entries: Vec<ObjectEntry>,
    /// The span including braces.
    pub span: SymbolSpan,
}

/// An object entry (key-value pair).
///
/// Holds a key (identifier or string) and a value expression.
#[derive(Debug, Clone, AstContainerNode)]
pub struct ObjectEntry {
    /// The entry key (identifier or string literal).
    pub key: ObjectKey,
    /// The entry value.
    pub value: Expr,
    /// The span covering this entry.
    pub span: SymbolSpan,
}

/// An object key (identifier or string literal).
#[derive(Debug, Clone)]
pub enum ObjectKey {
    /// An identifier key.
    Ident(Ident),
    /// A string literal key.
    String(StringLit),
}

impl HasSpan for ObjectKey {
    fn span(&self) -> &SymbolSpan {
        match self {
            ObjectKey::Ident(ident) => ident.span(),
            ObjectKey::String(string) => string.span(),
        }
    }
}

impl HasNodeType for ObjectKey {
    fn node_type(&self) -> &'static str {
        match self {
            ObjectKey::Ident(_) => "Ident",
            ObjectKey::String(_) => "StringLit",
        }
    }
}

impl AstNode for ObjectKey {}

/// An identifier with its source text and span.
///
/// Keeps the original identifier text and a span over it.
#[derive(Debug, Clone, AstLeafNode)]
pub struct Ident {
    /// The identifier text.
    pub text: String,
    /// The span of this identifier.
    pub span: SymbolSpan,
}

/// Documentation comments attached to declarations and members.
///
/// Stores raw doc lines as captured and their combined span.
/// Upstream may strip comment markers; this type does not enforce it.
#[derive(Debug, Clone, AstLeafNode)]
pub struct Docs {
    /// The documentation lines (without comment markers).
    pub lines: Vec<String>,
    /// The span covering all documentation lines.
    pub span: SymbolSpan,
}

#[cfg(test)]
mod ast_tests {
    use crate::core::parser::ast::*;
    use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
    use crate::{AstContainerNode, AstLeafNode};

    /// Helper function to create a test span.
    fn test_span() -> SymbolSpan {
        SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        }
    }

    /// Test struct using `AstLeafNode` derive macro.
    #[derive(Debug, Clone, AstLeafNode)]
    struct TestLeafNode {
        pub value: String,
        pub span: SymbolSpan,
    }

    /// Test struct using `AstContainerNode` derive macro.
    #[derive(Debug, Clone, AstContainerNode)]
    struct TestContainerNode {
        #[expect(dead_code)]
        pub children: Vec<TestLeafNode>,
        pub span: SymbolSpan,
    }

    #[test]
    fn ast_leaf_node_derive() {
        let node = TestLeafNode {
            value: "test".to_string(),
            span: test_span(),
        };

        // Test HasSpan implementation
        assert_eq!(node.span().start.line, 1);
        assert_eq!(node.span().start.column, 1);

        // Test HasNodeType implementation
        assert_eq!(node.node_type(), "TestLeafNode");

        // Test AstNode implementation
        assert!(!node.is_container()); // Leaf nodes are not containers

        // Test AstVisitable implementation exists (default does nothing)
        let mut visitor = TestVisitor::new();
        node.accept(&mut visitor);
        assert_eq!(visitor.visited_nodes.len(), 0); // Default implementation does nothing
    }

    #[test]
    fn ast_container_node_derive() {
        let child = TestLeafNode {
            value: "child".to_string(),
            span: test_span(),
        };

        let node = TestContainerNode {
            children: vec![child],
            span: test_span(),
        };

        // Test HasSpan implementation
        assert_eq!(node.span().start.line, 1);
        assert_eq!(node.span().start.column, 1);

        // Test HasNodeType implementation
        assert_eq!(node.node_type(), "TestContainerNode");

        // Test AstNode implementation
        assert!(node.is_container()); // Container nodes should return true

        // Test AstVisitable implementation exists (default does nothing)
        let mut visitor = TestVisitor::new();
        node.accept(&mut visitor);
        assert_eq!(visitor.visited_nodes.len(), 0); // Default implementation does nothing
    }

    #[test]
    fn dynamic_dispatch() {
        let leaf: Box<dyn AstNode> = Box::new(TestLeafNode {
            value: "test".to_string(),
            span: test_span(),
        });

        let container: Box<dyn AstNode> = Box::new(TestContainerNode {
            children: vec![],
            span: test_span(),
        });

        // Test that we can store different AST node types in the same collection
        let nodes: Vec<Box<dyn AstNode>> = vec![leaf, container];

        assert_eq!(nodes.len(), 2);
        assert_eq!(nodes[0].node_type(), "TestLeafNode");
        assert!(!nodes[0].is_container());
        assert_eq!(nodes[1].node_type(), "TestContainerNode");
        assert!(nodes[1].is_container());
    }

    #[test]
    fn heterogeneous_collections() {
        use std::collections::HashMap;

        let mut node_map: HashMap<String, Box<dyn AstNode>> = HashMap::new();

        node_map.insert(
            "leaf".to_string(),
            Box::new(TestLeafNode {
                value: "test".to_string(),
                span: test_span(),
            }),
        );

        node_map.insert(
            "container".to_string(),
            Box::new(TestContainerNode {
                children: vec![],
                span: test_span(),
            }),
        );

        assert_eq!(node_map.len(), 2);
        assert_eq!(node_map["leaf"].node_type(), "TestLeafNode");
        assert_eq!(node_map["container"].node_type(), "TestContainerNode");
    }

    #[test]
    fn real_ast_nodes() {
        // Test with actual AST nodes from the production code
        let ident = Ident {
            text: "userId".to_string(),
            span: test_span(),
        };

        let string_lit = StringLit {
            value: "String".to_string(),
            span: test_span(),
        };

        let qualified_ident = QualifiedIdent {
            parts: vec![ident.clone()],
            span: test_span(),
        };

        // Test trait implementations
        assert_eq!(ident.node_type(), "Ident");
        assert!(!ident.is_container());

        assert_eq!(string_lit.node_type(), "StringLit");
        assert!(!string_lit.is_container());

        assert_eq!(qualified_ident.node_type(), "QualifiedIdent");
        assert!(qualified_ident.is_container());

        // Test dynamic dispatch with real nodes
        let nodes: Vec<Box<dyn AstNode>> = vec![
            Box::new(ident),
            Box::new(string_lit),
            Box::new(qualified_ident),
        ];

        assert_eq!(nodes.len(), 3);
    }

    #[test]
    fn visitor_pattern() {
        let mut visitor = TestVisitor::new();

        let ident = Ident {
            text: "test".to_string(),
            span: test_span(),
        };

        let string_lit = StringLit {
            value: "hello".to_string(),
            span: test_span(),
        };

        // Test visiting individual nodes (default implementations do nothing)
        ident.accept(&mut visitor);
        string_lit.accept(&mut visitor);

        assert_eq!(visitor.visited_nodes.len(), 0); // Default implementations do nothing
    }

    #[test]
    fn visitor_pattern_with_manual_implementation() {
        // Test the visitor pattern with Declaration which has manual implementation
        let mut visitor = TestVisitor::new();

        let model_decl = ModelDecl {
            name: Ident {
                text: "User".to_string(),
                span: test_span(),
            },
            members: vec![],
            attrs: vec![],
            docs: None,
            span: test_span(),
        };

        let declaration = Declaration::Model(model_decl);

        // The Declaration enum has a manual visitor implementation
        declaration.accept(&mut visitor);

        // Should visit the Declaration itself
        assert_eq!(visitor.visited_nodes.len(), 1);
        assert_eq!(visitor.visited_nodes[0], "ModelDecl");
    }

    #[test]
    fn clone_functionality() {
        let original = TestLeafNode {
            value: "original".to_string(),
            span: test_span(),
        };

        let cloned = original.clone();

        assert_eq!(original.value, cloned.value);
        assert_eq!(original.node_type(), cloned.node_type());
        assert_eq!(original.is_container(), cloned.is_container());
    }

    #[test]
    fn debug_formatting() {
        let node = TestLeafNode {
            value: "debug_test".to_string(),
            span: test_span(),
        };

        let debug_output = format!("{node:?}");
        assert!(debug_output.contains("TestLeafNode"));
        assert!(debug_output.contains("debug_test"));
    }

    #[test]
    fn span_consistency() {
        let span1 = SymbolSpan {
            start: SymbolLocation {
                line: 5,
                column: 10,
            },
            end: SymbolLocation {
                line: 5,
                column: 20,
            },
        };

        let node = TestLeafNode {
            value: "span_test".to_string(),
            span: span1.clone(),
        };

        assert_eq!(node.span().start.line, span1.start.line);
        assert_eq!(node.span().start.column, span1.start.column);
        assert_eq!(node.span().end.line, span1.end.line);
        assert_eq!(node.span().end.column, span1.end.column);
    }

    /// Test visitor implementation for validation.
    struct TestVisitor {
        visited_nodes: Vec<String>,
    }

    impl TestVisitor {
        fn new() -> Self {
            Self {
                visited_nodes: Vec::new(),
            }
        }
    }

    impl AstVisitor for TestVisitor {
        fn visit_node(&mut self, node: &dyn AstNode) {
            self.visited_nodes.push(node.node_type().to_string());
        }
    }

    #[test]
    fn expression_types_coverage() {
        let span = SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        };

        // Test all expression types
        let string_lit = StringLit {
            value: "test".to_string(),
            span: span.clone(),
        };
        let int_lit = IntLit {
            value: "42".to_string(),
            span: span.clone(),
        };
        let float_lit = FloatLit {
            value: "3.14".to_string(),
            span: span.clone(),
        };
        let bool_lit = BoolLit {
            value: true,
            span: span.clone(),
        };
        let null_lit = NullLit { span: span.clone() };

        // Test expression enum variants
        let expr_string = Expr::StringLit(string_lit.clone());
        let expr_int = Expr::IntLit(int_lit.clone());
        let expr_float = Expr::FloatLit(float_lit.clone());
        let expr_bool = Expr::BoolLit(bool_lit.clone());
        let expr_null = Expr::NullLit(null_lit.clone());

        // Test spans
        assert_eq!(string_lit.span(), &span);
        assert_eq!(int_lit.span(), &span);
        assert_eq!(float_lit.span(), &span);
        assert_eq!(bool_lit.span(), &span);
        assert_eq!(null_lit.span(), &span);

        // Test expression spans
        assert_eq!(expr_string.span(), &span);
        assert_eq!(expr_int.span(), &span);
        assert_eq!(expr_float.span(), &span);
        assert_eq!(expr_bool.span(), &span);
        assert_eq!(expr_null.span(), &span);

        // Test node types
        assert_eq!(string_lit.node_type(), "StringLit");
        assert_eq!(int_lit.node_type(), "IntLit");
        assert_eq!(float_lit.node_type(), "FloatLit");
        assert_eq!(bool_lit.node_type(), "BoolLit");
        assert_eq!(null_lit.node_type(), "NullLit");
    }

    #[test]
    fn complex_expressions_coverage() {
        let span = SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        };

        let ident = Ident {
            text: "test".to_string(),
            span: span.clone(),
        };

        let qualified_ident = QualifiedIdent {
            parts: vec![ident.clone()],
            span: span.clone(),
        };

        // Test IdentRef
        let ident_ref = IdentRef {
            name: qualified_ident.clone(),
            span: span.clone(),
        };
        let expr_ident = Expr::IdentRef(ident_ref.clone());

        // Test FuncCall
        let func_call = FuncCall {
            callee: qualified_ident.clone(),
            args: None,
            span: span.clone(),
        };
        let expr_func = Expr::FuncCall(func_call.clone());

        // Test ArrayExpr
        let array_expr = ArrayExpr {
            elements: vec![Expr::StringLit(StringLit {
                value: "item".to_string(),
                span: span.clone(),
            })],
            span: span.clone(),
        };
        let expr_array = Expr::Array(array_expr.clone());

        // Test ObjectEntry
        let object_entry = ObjectEntry {
            key: ObjectKey::String(StringLit {
                value: "key".to_string(),
                span: span.clone(),
            }),
            value: Expr::StringLit(StringLit {
                value: "value".to_string(),
                span: span.clone(),
            }),
            span: span.clone(),
        };

        // Test ObjectExpr
        let object_expr = ObjectExpr {
            entries: vec![object_entry.clone()],
            span: span.clone(),
        };
        let expr_object = Expr::Object(object_expr.clone());

        // Test spans
        assert_eq!(ident_ref.span(), &span);
        assert_eq!(func_call.span(), &span);
        assert_eq!(array_expr.span(), &span);
        assert_eq!(object_entry.span(), &span);
        assert_eq!(object_expr.span(), &span);

        // Test expression spans
        assert_eq!(expr_ident.span(), &span);
        assert_eq!(expr_func.span(), &span);
        assert_eq!(expr_array.span(), &span);
        assert_eq!(expr_object.span(), &span);

        // Test node types
        assert_eq!(ident_ref.node_type(), "IdentRef");
        assert_eq!(func_call.node_type(), "FuncCall");
        assert_eq!(array_expr.node_type(), "ArrayExpr");
        assert_eq!(object_entry.node_type(), "ObjectEntry");
        assert_eq!(object_expr.node_type(), "ObjectExpr");

        // Test QualifiedIdent
        assert_eq!(qualified_ident.span(), &span);
        assert_eq!(qualified_ident.node_type(), "QualifiedIdent");
        assert_eq!(qualified_ident.parts.len(), 1);
    }

    #[test]
    fn argument_types_coverage() {
        let span = SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        };

        let ident = Ident {
            text: "arg".to_string(),
            span: span.clone(),
        };

        let expr = Expr::StringLit(StringLit {
            value: "value".to_string(),
            span: span.clone(),
        });

        // Test PositionalArg
        let positional_arg = PositionalArg {
            value: expr.clone(),
            span: span.clone(),
        };

        // Test NamedArg
        let named_arg = NamedArg {
            name: ident.clone(),
            value: expr.clone(),
            span: span.clone(),
        };

        // Test Arg variants
        let arg_positional = Arg::Positional(positional_arg.clone());
        let arg_named = Arg::Named(named_arg.clone());

        // Test ArgList
        let arg_list = ArgList {
            items: vec![arg_positional.clone(), arg_named.clone()],
            span: span.clone(),
        };

        // Test spans
        assert_eq!(positional_arg.span(), &span);
        assert_eq!(named_arg.span(), &span);
        assert_eq!(arg_list.span(), &span);

        // Test argument spans
        assert_eq!(arg_positional.span(), &span);
        assert_eq!(arg_named.span(), &span);

        // Test node types
        assert_eq!(positional_arg.node_type(), "PositionalArg");
        assert_eq!(named_arg.node_type(), "NamedArg");
        assert_eq!(arg_list.node_type(), "ArgList");

        // Test content
        assert_eq!(arg_list.items.len(), 2);
        assert_eq!(named_arg.name.text, "arg");
    }

    #[test]
    fn declaration_types_coverage() {
        let span = SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        };

        let ident = Ident {
            text: "test".to_string(),
            span: span.clone(),
        };

        let assignment = Assignment {
            key: ident.clone(),
            value: Expr::StringLit(StringLit {
                value: "value".to_string(),
                span: span.clone(),
            }),
            docs: None,
            span: span.clone(),
        };

        // Test DatasourceDecl
        let datasource = DatasourceDecl {
            name: ident.clone(),
            assignments: vec![assignment.clone()],
            docs: None,
            span: span.clone(),
        };

        // Test GeneratorDecl
        let generator = GeneratorDecl {
            name: ident.clone(),
            assignments: vec![assignment.clone()],
            docs: None,
            span: span.clone(),
        };

        // Test TypeDecl
        let type_decl = TypeDecl {
            name: ident.clone(),
            rhs: TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![ident.clone()],
                    span: span.clone(),
                },
                span: span.clone(),
            }),
            docs: None,
            span: span.clone(),
        };

        // Test spans
        assert_eq!(assignment.span(), &span);
        assert_eq!(datasource.span(), &span);
        assert_eq!(generator.span(), &span);
        assert_eq!(type_decl.span(), &span);

        // Test node types
        assert_eq!(assignment.node_type(), "Assignment");
        assert_eq!(datasource.node_type(), "DatasourceDecl");
        assert_eq!(generator.node_type(), "GeneratorDecl");
        assert_eq!(type_decl.node_type(), "TypeDecl");

        // Test Declaration enum variants
        let decl_datasource = Declaration::Datasource(datasource.clone());
        let decl_generator = Declaration::Generator(generator.clone());
        let decl_type = Declaration::Type(type_decl.clone());

        assert_eq!(decl_datasource.span(), &span);
        assert_eq!(decl_generator.span(), &span);
        assert_eq!(decl_type.span(), &span);
    }

    #[test]
    fn type_system_coverage() {
        let span = SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        };

        let ident = Ident {
            text: "String".to_string(),
            span: span.clone(),
        };

        let qualified_ident = QualifiedIdent {
            parts: vec![ident.clone()],
            span: span.clone(),
        };

        // Test NamedType
        let named_type = NamedType {
            name: qualified_ident.clone(),
            span: span.clone(),
        };

        // Test ListType
        let list_type = ListType {
            inner: Box::new(TypeRef::Named(named_type.clone())),
            span: span.clone(),
        };

        // Test TypeRef variants
        let type_ref_named = TypeRef::Named(named_type.clone());
        let type_ref_list = TypeRef::List(list_type.clone());

        // Test spans
        assert_eq!(named_type.span(), &span);
        assert_eq!(list_type.span(), &span);
        assert_eq!(type_ref_named.span(), &span);
        assert_eq!(type_ref_list.span(), &span);

        // Test node types
        assert_eq!(named_type.node_type(), "NamedType");
        assert_eq!(list_type.node_type(), "ListType");

        // Test content
        assert_eq!(named_type.name.parts.len(), 1);
        assert_eq!(named_type.name.parts[0].text, "String");
    }

    #[test]
    fn attribute_types_coverage() {
        let span = SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        };

        let ident = Ident {
            text: "id".to_string(),
            span: span.clone(),
        };

        let qualified_ident = QualifiedIdent {
            parts: vec![ident.clone()],
            span: span.clone(),
        };

        let arg_list = ArgList {
            items: vec![],
            span: span.clone(),
        };

        // Test FieldAttribute
        let field_attr = FieldAttribute {
            name: qualified_ident.clone(),
            args: Some(arg_list.clone()),
            docs: None,
            span: span.clone(),
        };

        // Test BlockAttribute
        let block_attr = BlockAttribute {
            name: qualified_ident.clone(),
            args: Some(arg_list.clone()),
            docs: None,
            span: span.clone(),
        };

        // Test spans
        assert_eq!(field_attr.span(), &span);
        assert_eq!(block_attr.span(), &span);

        // Test node types
        assert_eq!(field_attr.node_type(), "FieldAttribute");
        assert_eq!(block_attr.node_type(), "BlockAttribute");

        // Test content
        assert_eq!(field_attr.name.parts.len(), 1);
        assert_eq!(field_attr.name.parts[0].text, "id");
        assert!(field_attr.args.is_some());
    }

    #[test]
    fn schema_and_members_coverage() {
        let span = SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        };

        let ident = Ident {
            text: "User".to_string(),
            span: span.clone(),
        };

        // Test FieldDecl
        let field_decl = FieldDecl {
            name: ident.clone(),
            r#type: TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![Ident {
                        text: "String".to_string(),
                        span: span.clone(),
                    }],
                    span: span.clone(),
                },
                span: span.clone(),
            }),
            optional: false,
            modifiers: vec![],
            attrs: vec![],
            docs: None,
            span: span.clone(),
        };

        // Test EnumValue
        let enum_value = EnumValue {
            name: ident.clone(),
            attrs: vec![],
            docs: None,
            span: span.clone(),
        };

        // Test ModelMember and EnumMember variants
        let model_member = ModelMember::Field(field_decl.clone());
        let enum_member = EnumMember::Value(enum_value.clone());

        // Test ModelDecl
        let model_decl = ModelDecl {
            name: ident.clone(),
            members: vec![model_member.clone()],
            attrs: vec![],
            docs: None,
            span: span.clone(),
        };

        // Test EnumDecl
        let enum_decl = EnumDecl {
            name: ident.clone(),
            members: vec![enum_member.clone()],
            attrs: vec![],
            docs: None,
            span: span.clone(),
        };

        // Test Schema
        let schema = Schema {
            declarations: vec![
                Declaration::Model(model_decl.clone()),
                Declaration::Enum(enum_decl.clone()),
            ],
            span: span.clone(),
        };

        // Test spans
        assert_eq!(field_decl.span(), &span);
        assert_eq!(enum_value.span(), &span);
        assert_eq!(model_member.span(), &span);
        assert_eq!(enum_member.span(), &span);
        assert_eq!(model_decl.span(), &span);
        assert_eq!(enum_decl.span(), &span);
        assert_eq!(schema.span(), &span);

        // Test node types
        assert_eq!(field_decl.node_type(), "FieldDecl");
        assert_eq!(enum_value.node_type(), "EnumValue");
        assert_eq!(model_decl.node_type(), "ModelDecl");
        assert_eq!(enum_decl.node_type(), "EnumDecl");
        assert_eq!(schema.node_type(), "Schema");

        // Test content
        assert_eq!(schema.declarations.len(), 2);
        assert_eq!(model_decl.members.len(), 1);
        assert_eq!(enum_decl.members.len(), 1);
        assert!(!field_decl.optional);
    }

    #[test]
    fn docs_and_identifiers() {
        let span = SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation {
                line: 1,
                column: 10,
            },
        };

        // Test Ident
        let ident = Ident {
            text: "identifier".to_string(),
            span: span.clone(),
        };

        // Test Docs
        let docs = Docs {
            lines: vec!["/// Documentation comment".to_string()],
            span: span.clone(),
        };

        // Test spans
        assert_eq!(ident.span(), &span);
        assert_eq!(docs.span(), &span);

        // Test node types
        assert_eq!(ident.node_type(), "Ident");
        assert_eq!(docs.node_type(), "Docs");

        // Test content
        assert_eq!(ident.text, "identifier");
        assert_eq!(docs.lines, vec!["/// Documentation comment".to_string()]);
    }
}
