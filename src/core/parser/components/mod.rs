//! Pluggable parser components for Prisma schema parsing.
//!
//! These components implement the grammar from `src/core/parser/grammar/v1.md`
//! in small, composable units. Each component focuses on a single family of
//! constructs (primitives, types, expressions, attributes, members,
//! declarations) and exposes a `Parser<T>` implementation with:
//!
//! - `parse(&mut self, stream, options) -> ParseResult<T>`: produces an AST
//!   node or diagnostics while preserving spans.
//! - `can_parse(&self, stream) -> bool`: fast, conservative lookahead using
//!   non-comment helpers for dispatch in composite parsers.
//! - `sync_tokens(&self) -> &[TokenType]`: recovery points for error handling.
//!
//! Spans are preserved end-to-end and use 1‑based line/column. Components
//! skip over regular comments in lookahead and use
//! `helpers::parse_leading_docs` to greedily associate preceding
//! documentation comments (`DocComment`) with the next parsed item.
//!
//! Parsing strategy is bottom‑up and layered:
//!
//! - `primitives`: identifiers and qualified identifiers.
//! - `types`: named and list types; scalar keywords and qualified names.
//! - `expressions`: literals, identifier refs, function calls, arrays, objects.
//! - `attributes`: field (`@`) and block (`@@`) attributes with argument lists.
//! - `members`: fields, enum values, assignments; model/enum member dispatch.
//! - `declarations`: top‑level blocks (`model`, `enum`, `datasource`,
//!   `generator`, and gated `type` aliases).
//!
//! Trailing comma policy follows the grammar: argument lists, arrays, and
//! objects may contain a trailing comma; type and member lists do not. The
//! scanner guarantees exactly one `EOF`, linear‑time tokenization, and that
//! `DocComment` content excludes leading slashes and newlines.
//!
//! ## Examples
//! Parse a field declaration `id String` directly with the component parser.
//! ```
//! # use prisma_rs::core::parser::components::members::FieldDeclParser;
//! # use prisma_rs::core::parser::traits::Parser;
//! # use prisma_rs::core::parser::stream::VectorTokenStream;
//! # use prisma_rs::core::parser::config::ParserOptions;
//! # use prisma_rs::core::parser::ast::TypeRef;
//! # use prisma_rs::core::scanner::tokens::{Token, TokenType};
//! let mut s = VectorTokenStream::new(vec![
//!     Token::new(TokenType::Identifier("id".into()), (1, 1), (1, 2)),
//!     Token::new(TokenType::String, (1, 4), (1, 9)),
//! ]);
//! let mut p = FieldDeclParser::default();
//! let f = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
//! assert_eq!(f.name.text, "id");
//! match f.r#type {
//!     TypeRef::Named(n) => assert_eq!(n.name.parts[0].text, "String"),
//!     _ => unreachable!(),
//! }
//! ```
//!
//! Parse an attribute with an argument list: `@id(fields: [id])`.
//! ```
//! # use prisma_rs::core::parser::components::attributes::FieldAttributeParser;
//! # use prisma_rs::core::parser::traits::Parser;
//! # use prisma_rs::core::parser::stream::VectorTokenStream;
//! # use prisma_rs::core::parser::config::ParserOptions;
//! # use prisma_rs::core::scanner::tokens::{Token, TokenType};
//! let mut s = VectorTokenStream::new(vec![
//!     Token::new(TokenType::At, (1,1), (1,1)),
//!     Token::new(TokenType::Identifier("id".into()), (1,2), (1,3)),
//!     Token::new(TokenType::LeftParen, (1,4), (1,4)),
//!     Token::new(TokenType::Identifier("fields".into()), (1,5), (1,10)),
//!     Token::new(TokenType::Colon, (1,11), (1,11)),
//!     Token::new(TokenType::LeftBracket, (1,13), (1,13)),
//!     Token::new(TokenType::Identifier("id".into()), (1,14), (1,15)),
//!     Token::new(TokenType::RightBracket, (1,16), (1,16)),
//!     Token::new(TokenType::RightParen, (1,17), (1,17)),
//! ]);
//! let mut p = FieldAttributeParser::default();
//! let a = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
//! assert_eq!(a.name.parts[0].text, "id");
//! assert!(a.args.is_some());
//! ```

pub mod attributes;
pub mod declarations;
pub mod expressions;
pub mod helpers;
pub mod members;
pub mod primitives;
pub mod types;
