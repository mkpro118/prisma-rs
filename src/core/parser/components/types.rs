//! Parse type references: named types and list types.
//!
//! These components recognize type references in field declarations and type
//! aliases. A named type is a single identifier (optionally qualified) such
//! as `String`, `User`, or `db.VarChar` and becomes a `NamedType` AST node.
//! A list type appends one or more list markers `[]`, producing nested
//! `ListType` nodes where the span covers the inner type through the list
//! marker.
//!
//! Parsing strategy: first read a base named type, then consume trailing
//! list markers and wrap the base accordingly. `can_parse` is conservative
//! and skips comments (via underlying primitives) when checking the start.
//!
//! ## Examples
//! Parse `String`, `db.VarChar`, and `Int[]`.
//! ```
//! # use prisma_rs::core::parser::components::types::{NamedTypeParser, TypeRefParser};
//! # use prisma_rs::core::parser::traits::Parser;
//! # use prisma_rs::core::parser::stream::VectorTokenStream;
//! # use prisma_rs::core::parser::config::ParserOptions;
//! # use prisma_rs::core::scanner::tokens::{Token, TokenType};
//! # use prisma_rs::core::parser::ast::HasNodeType;
//! // Named type via identifier
//! let mut s = VectorTokenStream::new(
//!     vec![Token::new(TokenType::Identifier("String".into()), (1,1), (1,7))]
//!  );
//! let mut np = NamedTypeParser::new();
//! let nt = np.parse(&mut s, &ParserOptions::default()).value.unwrap();
//! assert_eq!(nt.node_type(), "NamedType");
//!
//! // Qualified name
//! let mut s = VectorTokenStream::new(vec![
//!     Token::new(TokenType::Identifier("db".into()), (1,1), (1,3)),
//!     Token::new(TokenType::Dot, (1,3), (1,3)),
//!     Token::new(TokenType::Identifier("VarChar".into()), (1,4), (1,11)),
//! ]);
//! let nt = np.parse(&mut s, &ParserOptions::default()).value.unwrap();
//! assert_eq!(nt.name.parts.len(), 2);
//!
//! // List type
//! let mut s = VectorTokenStream::new(vec![
//!     Token::new(TokenType::Int, (1,1), (1,4)),
//!     Token::new(TokenType::List, (1,5), (1,6)),
//! ]);
//! let mut tp = TypeRefParser::new();
//! let tr = tp.parse(&mut s, &ParserOptions::default()).value.unwrap();
//! assert_eq!(tr.node_type(), "ListType");
//! ```

use crate::core::parser::components::primitives::QualifiedIdentParser;
use crate::core::parser::stream::TokenStreamExt;
use crate::core::parser::{
    ast::{HasSpan, ListType, NamedType, TypeRef},
    config::{Diagnostic, ParseResult, ParserOptions},
    traits::{Parser, TokenStream},
};
use crate::core::scanner::tokens::{SymbolSpan, TokenType};

/// Parse a named type reference (e.g., `String`, `User`, `db.VarChar`).
///
/// Uses `QualifiedIdentParser` to parse identifier-based type names,
/// optionally qualified (e.g., `db.VarChar`).
///
/// ## Errors
/// Returns an error diagnostic when no identifier or scalar type is present
/// at the current position.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::components::types::NamedTypeParser;
/// # use prisma_rs::core::parser::traits::Parser;
/// # use prisma_rs::core::parser::stream::VectorTokenStream;
/// # use prisma_rs::core::parser::config::ParserOptions;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// # use prisma_rs::core::parser::ast::HasNodeType;
/// let mut s = VectorTokenStream::new(vec![Token::new(
///     TokenType::Identifier("User".into()),
///     (1, 1),
///     (1, 5),
/// )]);
/// let mut p = NamedTypeParser::new();
/// let named = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
/// assert_eq!(named.name.parts[0].text, "User");
/// ```
#[derive(Debug, Default)]
pub struct NamedTypeParser {
    qualified_ident_parser: QualifiedIdentParser,
}

impl NamedTypeParser {
    /// Create a new named type parser.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl Parser<NamedType> for NamedTypeParser {
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<NamedType> {
        // Fast path: handle scalar keywords as named types
        if let Some(tok) = stream.peek() {
            let is_scalar = matches!(
                tok.r#type(),
                TokenType::String
                    | TokenType::Int
                    | TokenType::Float
                    | TokenType::Boolean
                    | TokenType::DateTime
                    | TokenType::Json
                    | TokenType::Bytes
                    | TokenType::Decimal
            );

            if is_scalar {
                let Some(tok) = stream.next() else {
                    unreachable!("peek returned Some but next returned None");
                };
                let ident = crate::core::parser::ast::Ident {
                    text: tok.r#type().name().to_string(),
                    span: tok.span().clone(),
                };
                let qname = crate::core::parser::ast::QualifiedIdent {
                    parts: vec![ident],
                    span: tok.span().clone(),
                };
                return ParseResult::success(NamedType {
                    name: qname,
                    span: tok.span().clone(),
                });
            }
        }

        // Otherwise, fall back to qualified identifiers
        match self.qualified_ident_parser.parse(stream, options) {
            ParseResult {
                value: Some(name),
                diagnostics,
            } => {
                let span = name.span.clone();
                let mut result = ParseResult::success(NamedType { name, span });
                result.diagnostics = diagnostics;
                result
            }
            ParseResult {
                value: None,
                diagnostics,
            } => {
                let mut result = ParseResult::error(Diagnostic::error(
                    stream.peek().map_or_else(
                        || SymbolSpan {
                            start:
                                crate::core::scanner::tokens::SymbolLocation {
                                    line: 1,
                                    column: 1,
                                },
                            end: crate::core::scanner::tokens::SymbolLocation {
                                line: 1,
                                column: 1,
                            },
                        },
                        |t| t.span().clone(),
                    ),
                    "Expected type name",
                ));
                result.diagnostics.extend(diagnostics);
                result
            }
        }
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        self.qualified_ident_parser.can_parse(stream)
            || Self::is_scalar_type(stream)
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::Comma,
            TokenType::RightBrace,
            TokenType::RightParen,
            TokenType::Optional,
        ]
    }
}

impl NamedTypeParser {
    /// Check if the current token is a scalar type keyword.
    fn is_scalar_type(stream: &dyn TokenStream) -> bool {
        matches!(
            stream
                .peek_non_comment()
                .map(crate::core::scanner::tokens::Token::r#type),
            Some(
                TokenType::String
                    | TokenType::Int
                    | TokenType::Float
                    | TokenType::Boolean
                    | TokenType::DateTime
                    | TokenType::Json
                    | TokenType::Bytes
                    | TokenType::Decimal
            )
        )
    }
}

/// Parse complete type references including list types.
///
/// After parsing a base named type, this parser consumes consecutive list
/// markers (`[]`) and wraps the base to produce nested `ListType` nodes.
/// The final span of each `ListType` covers from the start of the inner type
/// to the end of the list marker.
///
/// ## Errors
/// Returns an error diagnostic when a base type cannot be parsed at the
/// current position.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::ast::HasNodeType;
/// # use prisma_rs::core::parser::components::types::TypeRefParser;
/// # use prisma_rs::core::parser::traits::Parser;
/// # use prisma_rs::core::parser::stream::VectorTokenStream;
/// # use prisma_rs::core::parser::config::ParserOptions;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::Identifier("Post".into()), (1, 1), (1, 5)),
///     Token::new(TokenType::List, (1, 6), (1, 7)),
///     Token::new(TokenType::List, (1, 8), (1, 9)),
/// ]);
/// let mut p = TypeRefParser::new();
/// let t = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
/// assert_eq!(t.node_type(), "ListType");
/// ```
#[derive(Debug, Default)]
pub struct TypeRefParser {
    named_type_parser: NamedTypeParser,
}

impl TypeRefParser {
    /// Create a new type reference parser.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl Parser<TypeRef> for TypeRefParser {
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<TypeRef> {
        // Parse the base type first
        match self.named_type_parser.parse(stream, options) {
            ParseResult {
                value: Some(named_type),
                diagnostics,
            } => {
                let mut current_type = TypeRef::Named(named_type);
                let result_diagnostics = diagnostics;

                // Check for list marker(s) and build nested list types
                while let Some(token) = stream.peek()
                    && matches!(token.r#type(), TokenType::List)
                {
                    if let Some(list_token) = stream.next() {
                        // Create the list type span covering the inner type and list marker
                        let start_span = current_type.span().start.clone();
                        let end_span = list_token.span().end.clone();
                        let list_span = SymbolSpan {
                            start: start_span,
                            end: end_span,
                        };

                        current_type = TypeRef::List(ListType {
                            inner: Box::new(current_type),
                            span: list_span,
                        });
                    } else {
                        unreachable!(
                            "Token should exist since peek returned Some"
                        )
                    }
                }

                let mut result = ParseResult::success(current_type);
                result.diagnostics = result_diagnostics;
                result
            }
            ParseResult {
                value: None,
                diagnostics,
            } => {
                let mut result = ParseResult::error(Diagnostic::error(
                    stream.peek().map_or_else(
                        || SymbolSpan {
                            start:
                                crate::core::scanner::tokens::SymbolLocation {
                                    line: 1,
                                    column: 1,
                                },
                            end: crate::core::scanner::tokens::SymbolLocation {
                                line: 1,
                                column: 1,
                            },
                        },
                        |t| t.span().clone(),
                    ),
                    "Expected type reference",
                ));
                result.diagnostics.extend(diagnostics);
                result
            }
        }
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        self.named_type_parser.can_parse(stream)
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::Comma,
            TokenType::RightBrace,
            TokenType::RightParen,
            TokenType::Optional,
            TokenType::At,
        ]
    }
}

#[cfg(test)]
mod tests {
    use crate::core::parser::components::types::{
        NamedTypeParser, TypeRefParser,
    };
    use crate::core::parser::stream::VectorTokenStream;
    use crate::core::parser::{
        ast::TypeRef,
        config::ParserOptions,
        traits::{Parser, TokenStream},
    };
    use crate::core::scanner::tokens::Token;
    use crate::core::scanner::tokens::TokenType;

    fn create_test_token(token_type: TokenType) -> Token {
        Token::new(token_type, (1, 1), (1, 2))
    }

    #[test]
    fn named_type_simple_identifier() {
        let tokens =
            vec![create_test_token(TokenType::Identifier("User".to_string()))];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = NamedTypeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let named_type = result.value.unwrap();
        assert_eq!(named_type.name.parts.len(), 1);
        assert_eq!(named_type.name.parts[0].text, "User");
    }

    #[test]
    fn named_type_qualified() {
        let tokens = vec![
            create_test_token(TokenType::Identifier("db".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("VarChar".to_string())),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = NamedTypeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let named_type = result.value.unwrap();
        assert_eq!(named_type.name.parts.len(), 2);
        assert_eq!(named_type.name.parts[0].text, "db");
        assert_eq!(named_type.name.parts[1].text, "VarChar");
    }

    #[test]
    fn named_type_scalar_types() {
        let scalar_types = vec![
            TokenType::String,
            TokenType::Int,
            TokenType::Float,
            TokenType::Boolean,
            TokenType::DateTime,
            TokenType::Json,
            TokenType::Bytes,
            TokenType::Decimal,
        ];

        for scalar_type in scalar_types {
            let tokens = vec![create_test_token(scalar_type.clone())];
            let stream = VectorTokenStream::new(tokens);
            let parser = NamedTypeParser::new();

            assert!(
                parser.can_parse(&stream),
                "Should be able to parse {scalar_type:?}"
            );
        }
    }

    #[test]
    fn type_ref_simple() {
        let tokens = vec![create_test_token(TokenType::Identifier(
            "String".to_string(),
        ))];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = TypeRefParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(TypeRef::Named(named_type)) = result.value {
            assert_eq!(named_type.name.parts.len(), 1);
            assert_eq!(named_type.name.parts[0].text, "String");
        } else {
            panic!("Expected named type");
        }
    }

    #[test]
    fn type_ref_list() {
        let tokens = vec![
            create_test_token(TokenType::Identifier("String".to_string())),
            create_test_token(TokenType::List),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = TypeRefParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(TypeRef::List(list_type)) = result.value {
            if let TypeRef::Named(named_type) = list_type.inner.as_ref() {
                assert_eq!(named_type.name.parts[0].text, "String");
            } else {
                panic!("Expected inner type to be named type");
            }
        } else {
            panic!("Expected list type");
        }
    }

    #[test]
    fn type_ref_nested_list() {
        let tokens = vec![
            create_test_token(TokenType::Identifier("Int".to_string())),
            create_test_token(TokenType::List),
            create_test_token(TokenType::List),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = TypeRefParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(TypeRef::List(outer_list)) = result.value {
            if let TypeRef::List(inner_list) = outer_list.inner.as_ref() {
                if let TypeRef::Named(named_type) = inner_list.inner.as_ref() {
                    assert_eq!(named_type.name.parts[0].text, "Int");
                } else {
                    panic!("Expected innermost type to be named type");
                }
            } else {
                panic!("Expected inner type to be list type");
            }
        } else {
            panic!("Expected outer type to be list type");
        }
    }

    #[test]
    fn type_ref_qualified_list() {
        let tokens = vec![
            create_test_token(TokenType::Identifier("db".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("Text".to_string())),
            create_test_token(TokenType::List),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = TypeRefParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(TypeRef::List(list_type)) = result.value {
            if let TypeRef::Named(named_type) = list_type.inner.as_ref() {
                assert_eq!(named_type.name.parts.len(), 2);
                assert_eq!(named_type.name.parts[0].text, "db");
                assert_eq!(named_type.name.parts[1].text, "Text");
            } else {
                panic!("Expected inner type to be named type");
            }
        } else {
            panic!("Expected list type");
        }
    }

    #[test]
    fn type_ref_can_parse() {
        let parser = TypeRefParser::new();

        // Test identifiers
        let tokens =
            vec![create_test_token(TokenType::Identifier("Test".to_string()))];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));

        // Test scalar types
        let tokens = vec![create_test_token(TokenType::String)];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));

        // Test non-type tokens
        let tokens = vec![create_test_token(TokenType::Model)];
        let stream = VectorTokenStream::new(tokens);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn type_ref_can_parse_with_comments() {
        let parser = TypeRefParser::new();

        // Test identifiers with comments
        let tokens = vec![
            create_test_token(TokenType::Comment("// comment".to_string())),
            create_test_token(TokenType::DocComment(
                "/// doc comment".to_string(),
            )),
            create_test_token(TokenType::Identifier("Test".to_string())),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));

        // Test scalar types with comments
        let tokens = vec![
            create_test_token(TokenType::Comment("// comment".to_string())),
            create_test_token(TokenType::DocComment(
                "/// doc comment".to_string(),
            )),
            create_test_token(TokenType::String),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));

        // Test non-type tokens with comments
        let tokens = vec![
            create_test_token(TokenType::Comment("// comment".to_string())),
            create_test_token(TokenType::DocComment(
                "/// doc comment".to_string(),
            )),
            create_test_token(TokenType::Model),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn type_ref_error_handling() {
        let tokens = vec![create_test_token(TokenType::Model)];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = TypeRefParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(!result.is_success());
        assert!(result.has_errors());
        assert!(result.value.is_none());
    }

    #[test]
    fn type_ref_scalar_types() {
        // Scalar type regular
        let mut s = VectorTokenStream::new(vec![Token::new(
            TokenType::Int,
            (1, 1),
            (1, 4),
        )]);
        let mut np = TypeRefParser::new();
        let out = np.parse(&mut s, &ParserOptions::default());
        assert!(out.is_success(), "Int should parse as type ref");

        // Scalar type optional
        let mut s = VectorTokenStream::new(vec![
            Token::new(TokenType::Decimal, (1, 1), (1, 7)),
            Token::new(TokenType::Optional, (1, 8), (1, 9)),
        ]);
        let mut np = TypeRefParser::new();
        let out = np.parse(&mut s, &ParserOptions::default());
        assert!(out.is_success(), "Decimal should parse before optional");
        // Ensure the optional remains for downstream parsing
        assert!(matches!(
            s.peek().map(Token::r#type),
            Some(TokenType::Optional)
        ));

        // List type
        let mut s = VectorTokenStream::new(vec![
            Token::new(TokenType::Int, (1, 1), (1, 4)),
            Token::new(TokenType::List, (1, 5), (1, 6)),
        ]);
        let mut tp = TypeRefParser::new();
        let tr = tp
            .parse(&mut s, &ParserOptions::default())
            .value
            .expect("list type should parse");
        match tr {
            TypeRef::List(list) => match list.inner.as_ref() {
                TypeRef::Named(n) => {
                    assert_eq!(n.name.parts.len(), 1);
                    assert_eq!(n.name.parts[0].text, "Int");
                }
                other @ TypeRef::List(_) => {
                    panic!("expected inner NamedType, got {other:?}")
                }
            },
            other @ TypeRef::Named(_) => {
                panic!("expected ListType, got {other:?}")
            }
        }
    }
}
