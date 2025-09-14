//! Parse primitive language constructs: identifiers and qualified names.
//!
//! These components provide small, focused parsers for tokens that appear
//! throughout the grammar. They are designed to be composed by higher-level
//! parsers, respect comment-skipping behavior in `can_parse`, and return
//! precise spans for diagnostics.
//!
//! Identifiers are parsed as `Ident` AST nodes. Qualified identifiers are
//! dot-separated sequences of identifiers (for namespacing and built-ins)
//! parsed to `QualifiedIdent`. Spans cover the full construct from the first
//! character of the first part to the last character of the final part.
//!
//! ## Examples
//! Parse an identifier and a qualified identifier from tokens.
//! ```
//! # use prisma_rs::core::parser::components::primitives::{IdentParser, QualifiedIdentParser};
//! # use prisma_rs::core::parser::traits::Parser;
//! # use prisma_rs::core::parser::stream::VectorTokenStream;
//! # use prisma_rs::core::parser::config::ParserOptions;
//! # use prisma_rs::core::scanner::tokens::{Token, TokenType};
//! // Identifier
//! let mut s = VectorTokenStream::new(vec![
//!     Token::new(TokenType::Identifier("User".into()), (1,1), (1,5)),
//! ]);
//! let mut p = IdentParser::new();
//! let ident = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
//! assert_eq!(ident.text, "User");
//!
//! // Qualified identifier: db.VarChar
//! let mut s = VectorTokenStream::new(vec![
//!     Token::new(TokenType::Identifier("db".into()), (1,1), (1,3)),
//!     Token::new(TokenType::Dot, (1,3), (1,3)),
//!     Token::new(TokenType::Identifier("VarChar".into()), (1,4), (1,11)),
//! ]);
//! let mut qp = QualifiedIdentParser::new();
//! let q = qp.parse(&mut s, &ParserOptions::default()).value.unwrap();
//! assert_eq!(q.parts.len(), 2);
//! assert_eq!(q.parts[0].text, "db");
//! ```

use crate::core::parser::stream::TokenStreamExt;
use crate::core::parser::{
    ast::{Ident, QualifiedIdent},
    config::{Diagnostic, ParseResult, ParserOptions},
    traits::{Parser, TokenStream},
};
use crate::core::scanner::tokens::{SymbolSpan, TokenType};

/// Parse a single identifier into an `Ident` AST node.
///
/// Returns the identifier text and its span. `can_parse` ignores leading
/// comments; `parse` expects the current token to be an identifier.
///
/// ## Errors
/// Returns an error diagnostic when the current token is missing or not an
/// identifier. The error span points to the unexpected token or end-of-input.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::components::primitives::IdentParser;
/// # use prisma_rs::core::parser::traits::Parser;
/// # use prisma_rs::core::parser::stream::VectorTokenStream;
/// # use prisma_rs::core::parser::config::ParserOptions;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// let mut s = VectorTokenStream::new(vec![Token::new(
///     TokenType::Identifier("A".into()),
///     (1, 1),
///     (1, 2),
/// )]);
/// let mut p = IdentParser::new();
/// let out = p.parse(&mut s, &ParserOptions::default());
/// assert!(out.is_success());
/// ```
#[derive(Debug, Default)]
pub struct IdentParser;

impl IdentParser {
    /// Create a new identifier parser.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl Parser<Ident> for IdentParser {
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        _options: &ParserOptions,
    ) -> ParseResult<Ident> {
        match stream.peek() {
            Some(token)
                if matches!(token.r#type(), TokenType::Identifier(_)) =>
            {
                if let Some(token) = stream.next() {
                    if let TokenType::Identifier(text) = token.r#type() {
                        ParseResult::success(Ident {
                            text: text.clone(),
                            span: token.span().clone(),
                        })
                    } else {
                        unreachable!("Token type was checked above")
                    }
                } else {
                    unreachable!("Token should exist since peek returned Some")
                }
            }
            Some(token) => ParseResult::error(Diagnostic::error(
                token.span().clone(),
                format!("Expected identifier, found {:?}", token.r#type()),
            )),
            None => {
                // Create a dummy span at the end of input
                let span = SymbolSpan {
                    start: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 1,
                    },
                    end: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 1,
                    },
                };
                ParseResult::error(Diagnostic::error(
                    span,
                    "Unexpected end of input, expected identifier",
                ))
            }
        }
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        matches!(
            stream
                .peek_non_comment()
                .map(crate::core::scanner::tokens::Token::r#type),
            Some(TokenType::Identifier(_))
        )
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::Comma,
            TokenType::RightBrace,
            TokenType::RightParen,
        ]
    }
}

/// Parse a qualified identifier (e.g., `db.VarChar` or `simple`).
///
/// Recognizes a dot-separated sequence of identifiers and returns a
/// `QualifiedIdent` whose span covers the full sequence. `can_parse` delegates
/// to `IdentParser` to check the first part.
///
/// ## Errors
/// Emits an error diagnostic if a dot is not followed by an identifier, or if
/// the first token is not an identifier.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::components::primitives::QualifiedIdentParser;
/// # use prisma_rs::core::parser::traits::Parser;
/// # use prisma_rs::core::parser::stream::VectorTokenStream;
/// # use prisma_rs::core::parser::config::ParserOptions;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::Identifier("ns".into()), (1,1), (1,3)),
///     Token::new(TokenType::Dot, (1,3), (1,3)),
///     Token::new(TokenType::Identifier("Name".into()), (1,4), (1,8)),
/// ]);
/// let mut p = QualifiedIdentParser::new();
/// let q = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
/// assert_eq!(q.parts.len(), 2);
/// assert_eq!(q.parts[1].text, "Name");
/// ```
#[derive(Debug, Default)]
pub struct QualifiedIdentParser {
    ident_parser: IdentParser,
}

impl QualifiedIdentParser {
    /// Create a new qualified identifier parser.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl Parser<QualifiedIdent> for QualifiedIdentParser {
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<QualifiedIdent> {
        let mut parts = Vec::new();
        let mut result_diagnostics = Vec::new();

        // Parse the first identifier
        match self.ident_parser.parse(stream, options) {
            ParseResult {
                value: Some(ident),
                diagnostics,
            } => {
                let start_span = ident.span.clone();
                parts.push(ident);
                result_diagnostics.extend(diagnostics);

                // Parse additional dotted parts
                while let Some(token) = stream.peek()
                    && matches!(token.r#type(), TokenType::Dot)
                {
                    // Consume the dot
                    stream.next();

                    // Parse the next identifier
                    match self.ident_parser.parse(stream, options) {
                        ParseResult {
                            value: Some(ident),
                            diagnostics,
                        } => {
                            parts.push(ident);
                            result_diagnostics.extend(diagnostics);
                        }
                        ParseResult {
                            value: None,
                            diagnostics,
                        } => {
                            result_diagnostics.extend(diagnostics);
                            // Create error result with collected diagnostics
                            let mut result = ParseResult::error(
                                Diagnostic::error(
                                    stream.peek().map_or_else(
                                        || start_span.clone(),
                                        |t| t.span().clone(),
                                    ),
                                    "Expected identifier after dot in qualified name",
                                ),
                            );
                            result.diagnostics.extend(result_diagnostics);
                            return result;
                        }
                    }
                }

                // Create the span covering all parts
                let end_span = parts
                    .last()
                    .map_or_else(|| start_span.clone(), |p| p.span.clone());
                let span = SymbolSpan {
                    start: start_span.start,
                    end: end_span.end,
                };

                let mut result =
                    ParseResult::success(QualifiedIdent { parts, span });
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
                    "Expected qualified identifier",
                ));
                result.diagnostics.extend(diagnostics);
                result
            }
        }
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        self.ident_parser.can_parse(stream)
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::Comma,
            TokenType::RightBrace,
            TokenType::RightParen,
            TokenType::Assign,
        ]
    }
}

#[cfg(test)]
mod tests {
    #![expect(clippy::unwrap_used)]

    use crate::core::parser::components::primitives::{
        IdentParser, QualifiedIdentParser,
    };
    use crate::core::parser::config::ParserOptions;
    use crate::core::parser::stream::VectorTokenStream;
    use crate::core::parser::traits::Parser;
    use crate::core::scanner::tokens::{Token, TokenType};

    fn create_test_token(token_type: TokenType) -> Token {
        Token::new(token_type, (1, 1), (1, 2))
    }

    #[test]
    fn ident_parser_success() {
        let tokens =
            vec![create_test_token(TokenType::Identifier("test".to_string()))];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = IdentParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        assert_eq!(result.value.unwrap().text, "test");
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn ident_parser_wrong_token() {
        let tokens = vec![create_test_token(TokenType::Model)];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = IdentParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(!result.is_success());
        assert!(result.value.is_none());
        assert!(result.has_errors());
    }

    #[test]
    fn ident_parser_can_parse() {
        let tokens =
            vec![create_test_token(TokenType::Identifier("test".to_string()))];
        let stream = VectorTokenStream::new(tokens);
        let parser = IdentParser::new();

        assert!(parser.can_parse(&stream));

        let tokens = vec![create_test_token(TokenType::Model)];
        let stream = VectorTokenStream::new(tokens);

        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn qualified_ident_simple() {
        let tokens = vec![create_test_token(TokenType::Identifier(
            "simple".to_string(),
        ))];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = QualifiedIdentParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let qualified = result.value.unwrap();
        assert_eq!(qualified.parts.len(), 1);
        assert_eq!(qualified.parts[0].text, "simple");
        assert!(qualified.is_simple());
    }

    #[test]
    fn qualified_ident_dotted() {
        let tokens = vec![
            create_test_token(TokenType::Identifier("db".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("VarChar".to_string())),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = QualifiedIdentParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let qualified = result.value.unwrap();
        assert_eq!(qualified.parts.len(), 2);
        assert_eq!(qualified.parts[0].text, "db");
        assert_eq!(qualified.parts[1].text, "VarChar");
        assert!(!qualified.is_simple());
    }

    #[test]
    fn qualified_ident_incomplete_dot() {
        let tokens = vec![
            create_test_token(TokenType::Identifier("db".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Model), // Wrong token after dot
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = QualifiedIdentParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(!result.is_success());
        assert!(result.has_errors());
    }

    #[test]
    fn qualified_ident_multiple_dots() {
        let tokens = vec![
            create_test_token(TokenType::Identifier("a".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("b".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("c".to_string())),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = QualifiedIdentParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let qualified = result.value.unwrap();
        assert_eq!(qualified.parts.len(), 3);
        assert_eq!(qualified.parts[0].text, "a");
        assert_eq!(qualified.parts[1].text, "b");
        assert_eq!(qualified.parts[2].text, "c");
    }

    #[test]
    fn qualified_ident_can_parse() {
        let tokens =
            vec![create_test_token(TokenType::Identifier("test".to_string()))];
        let stream = VectorTokenStream::new(tokens);
        let parser = QualifiedIdentParser::new();

        assert!(parser.can_parse(&stream));

        let tokens = vec![create_test_token(TokenType::Model)];
        let stream = VectorTokenStream::new(tokens);

        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn qualified_ident_can_parse_with_comments() {
        let tokens = vec![
            create_test_token(TokenType::Comment("// comment".to_string())),
            create_test_token(TokenType::DocComment(
                "/// doc comment".to_string(),
            )),
            create_test_token(TokenType::Identifier("test".to_string())),
        ];
        let stream = VectorTokenStream::new(tokens);
        let parser = QualifiedIdentParser::new();

        assert!(parser.can_parse(&stream));

        let tokens = vec![
            create_test_token(TokenType::Comment("// comment".to_string())),
            create_test_token(TokenType::Model),
        ];
        let stream = VectorTokenStream::new(tokens);

        assert!(!parser.can_parse(&stream));
    }
}
