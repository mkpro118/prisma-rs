//! Parse attributes and argument lists.
//!
//! Implements high-performance parsers for Prisma schema attributes,
//! including field attributes (`@attr`), block attributes (`@@attr`), and
//! argument lists. Parsers preserve spans, skip comments where appropriate,
//! and accept trailing commas in argument lists.

use crate::core::parser::components::{
    expressions::ExpressionParser, helpers::parse_leading_docs,
    primitives::QualifiedIdentParser,
};
use crate::core::parser::stream::TokenStreamExt;
use crate::core::parser::{
    ast::{
        Arg, ArgList, BlockAttribute, FieldAttribute, HasSpan, NamedArg,
        PositionalArg,
    },
    config::{Diagnostic, ParseResult, ParserOptions},
    traits::{Parser, TokenStream},
};
use crate::core::scanner::tokens::{SymbolSpan, Token, TokenType};

/// Parse argument lists for attributes.
///
/// Supports positional and named arguments, comma-separated with an optional
/// trailing comma. Spans cover the full `(...)` list.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::components::attributes::ArgListParser;
/// # use prisma_rs::core::parser::traits::Parser;
/// # use prisma_rs::core::parser::stream::VectorTokenStream;
/// # use prisma_rs::core::parser::config::ParserOptions;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::LeftParen, (1, 1), (1, 1)),
///     Token::new(TokenType::Literal("1".into()), (1, 2), (1, 2)),
///     Token::new(TokenType::Comma, (1, 3), (1, 3)),
///     Token::new(TokenType::Literal("2".into()), (1, 5), (1, 5)),
///     Token::new(TokenType::RightParen, (1, 6), (1, 6)),
/// ]);
/// let mut p = ArgListParser::new();
/// let args = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
/// assert_eq!(args.items.len(), 2);
/// ```
#[derive(Debug, Default)]
pub struct ArgListParser {
    expression_parser: ExpressionParser,
    qualified_ident_parser: QualifiedIdentParser,
}

impl ArgListParser {
    /// Create a new argument list parser.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a single argument (positional or named).
    ///
    /// Internal helper used by the list parser.
    fn parse_single_arg(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Arg> {
        // Check if this is a named argument by looking for qualified identifier followed by colon
        let checkpoint = stream.checkpoint();

        // Try to parse as named argument first
        if let Some(token) = stream.peek()
            && matches!(token.r#type(), TokenType::Identifier(_))
        {
            // Look ahead for colon, potentially after a qualified identifier
            let mut lookahead_offset = 1;

            // Skip over potential dots and identifiers in qualified name
            loop {
                match stream.peek_ahead(lookahead_offset) {
                    Some(token) if matches!(token.r#type(), TokenType::Dot) => {
                        lookahead_offset += 1;
                        // Expect identifier after dot
                        if let Some(next_token) =
                            stream.peek_ahead(lookahead_offset)
                            && matches!(
                                next_token.r#type(),
                                TokenType::Identifier(_)
                            )
                        {
                            lookahead_offset += 1;
                        } else {
                            break;
                        }
                    }
                    Some(token)
                        if matches!(token.r#type(), TokenType::Colon) =>
                    {
                        // Found colon, this is a named argument
                        return self.parse_named_arg(stream, options);
                    }
                    _ => break,
                }
            }
        }

        // Fall back to positional argument
        stream.restore(checkpoint);
        self.parse_positional_arg(stream, options)
    }

    /// Finalize a named argument once the value is parsed.
    ///
    /// Builds `Arg::Named` or emits an error if the value is missing.
    fn finalize_named_arg(
        expression_result: ParseResult<crate::core::parser::ast::Expr>,
        name: crate::core::parser::ast::Ident,
        start_span: crate::core::scanner::tokens::SymbolLocation,
        name_diags: Vec<Diagnostic>,
        stream: &mut dyn TokenStream,
    ) -> ParseResult<Arg> {
        match expression_result {
            ParseResult {
                value: Some(value),
                diagnostics: value_diags,
            } => {
                let end_span = value.span().end.clone();
                let arg_span = SymbolSpan {
                    start: start_span,
                    end: end_span,
                };

                let mut result = ParseResult::success(Arg::Named(NamedArg {
                    name,
                    value,
                    span: arg_span,
                }));
                result.diagnostics.extend(name_diags);
                result.diagnostics.extend(value_diags);
                result
            }
            ParseResult {
                value: None,
                diagnostics: value_diags,
            } => {
                let mut result = ParseResult::error(Diagnostic::error(
                    stream.peek().map_or_else(
                        || SymbolSpan {
                            start: start_span.clone(),
                            end: start_span,
                        },
                        |t| t.span().clone(),
                    ),
                    "Expected expression after ':' in named argument",
                ));
                result.diagnostics.extend(name_diags);
                result.diagnostics.extend(value_diags);
                result
            }
        }
    }

    /// Parse `:` and the value expression for a named argument.
    fn parse_named_arg_value(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
        name: crate::core::parser::ast::Ident,
        start_span: crate::core::scanner::tokens::SymbolLocation,
        name_diags: Vec<Diagnostic>,
    ) -> ParseResult<Arg> {
        // Expect colon
        match stream.peek() {
            Some(token) if matches!(token.r#type(), TokenType::Colon) => {
                stream.next(); // consume ':'

                // Parse the value expression
                let expression_result =
                    self.expression_parser.parse(stream, options);
                Self::finalize_named_arg(
                    expression_result,
                    name,
                    start_span,
                    name_diags,
                    stream,
                )
            }
            Some(token) => ParseResult::error(Diagnostic::error(
                token.span().clone(),
                "Expected ':' after argument name",
            )),
            None => ParseResult::error(Diagnostic::error(
                SymbolSpan {
                    start: start_span.clone(),
                    end: start_span,
                },
                "Unexpected end of input, expected ':'",
            )),
        }
    }

    /// Parse a named argument: `name: value`.
    fn parse_named_arg(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Arg> {
        // Parse the name
        match self.qualified_ident_parser.parse(stream, options) {
            ParseResult {
                value: Some(qualified_name),
                diagnostics: name_diags,
            } => {
                // For named args, we expect a simple identifier, but QualifiedIdent is more flexible
                let name = if let Some(simple_name) = qualified_name.as_simple()
                {
                    simple_name.clone()
                } else {
                    // Create a simple identifier from the qualified one
                    crate::core::parser::ast::Ident {
                        text: qualified_name
                            .parts
                            .iter()
                            .map(|part| part.text.as_str())
                            .collect::<Vec<&str>>()
                            .join("."),
                        span: qualified_name.span.clone(),
                    }
                };

                let start_span = name.span.start.clone();
                self.parse_named_arg_value(
                    stream, options, name, start_span, name_diags,
                )
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
                    "Expected argument name",
                ));
                result.diagnostics.extend(diagnostics);
                result
            }
        }
    }

    /// Parse a positional argument: `value`.
    fn parse_positional_arg(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Arg> {
        match self.expression_parser.parse(stream, options) {
            ParseResult {
                value: Some(value),
                diagnostics,
            } => {
                let span = value.span().clone();
                let mut result =
                    ParseResult::success(Arg::Positional(PositionalArg {
                        value,
                        span,
                    }));
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
                    "Expected expression in argument",
                ));
                result.diagnostics.extend(diagnostics);
                result
            }
        }
    }

    /// Parse zero or more comma-separated arguments until `)`.
    ///
    /// Accepts a trailing comma before the closing parenthesis.
    fn parse_arg_list_loop(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
        start_span: &crate::core::scanner::tokens::SymbolLocation,
    ) -> ParseResult<Vec<Arg>> {
        let mut args = Vec::with_capacity(4); // Preallocate for common case
        let mut all_diagnostics = Vec::new();

        loop {
            let Some(token) = stream.peek() else {
                break;
            };

            if matches!(token.r#type(), TokenType::RightParen) {
                break;
            }

            if !args.is_empty() {
                // Expect comma between arguments
                if matches!(token.r#type(), TokenType::Comma) {
                    stream.next(); // consume comma

                    // Check for trailing comma
                    if let Some(next_token) = stream.peek()
                        && matches!(next_token.r#type(), TokenType::RightParen)
                    {
                        break;
                    }
                } else {
                    return ParseResult::error(Diagnostic::error(
                        token.span().clone(),
                        "Expected ',' between arguments",
                    ));
                }
            }

            // Parse the argument
            match self.parse_single_arg(stream, options) {
                ParseResult {
                    value: Some(arg),
                    diagnostics: arg_diags,
                } => {
                    args.push(arg);
                    all_diagnostics.extend(arg_diags);
                }
                ParseResult {
                    value: None,
                    diagnostics: arg_diags,
                } => {
                    let mut result = ParseResult::error(Diagnostic::error(
                        stream.peek().map_or_else(
                            || SymbolSpan {
                                start: start_span.clone(),
                                end: start_span.clone(),
                            },
                            |t| t.span().clone(),
                        ),
                        "Failed to parse argument",
                    ));
                    result.diagnostics.extend(all_diagnostics);
                    result.diagnostics.extend(arg_diags);
                    return result;
                }
            }
        }
        let mut result = ParseResult::success(args);
        result.diagnostics = all_diagnostics;
        result
    }

    /// Build the `ArgList` after consuming the closing ')'.
    ///
    /// Returns an error if no closing `)` is found at the current position.
    fn finalize_arg_list(
        stream: &mut dyn TokenStream,
        start_span: crate::core::scanner::tokens::SymbolLocation,
        args: Vec<Arg>,
        diagnostics: Vec<Diagnostic>,
    ) -> ParseResult<ArgList> {
        match stream.peek() {
            Some(token) if matches!(token.r#type(), TokenType::RightParen) => {
                if let Some(close_token) = stream.next() {
                    let end_span = close_token.span().end.clone();

                    let mut result = ParseResult::success(ArgList {
                        items: args,
                        span: SymbolSpan {
                            start: start_span,
                            end: end_span,
                        },
                    });
                    result.diagnostics = diagnostics;
                    result
                } else {
                    ParseResult::error(Diagnostic::error(
                        SymbolSpan {
                            start: start_span.clone(),
                            end: start_span,
                        },
                        "Unexpected end of input, expected ')'",
                    ))
                }
            }
            Some(token) => ParseResult::error(Diagnostic::error(
                token.span().clone(),
                "Expected ')' after argument list",
            )),
            None => ParseResult::error(Diagnostic::error(
                SymbolSpan {
                    start: start_span.clone(),
                    end: start_span,
                },
                "Unexpected end of input, expected ')'",
            )),
        }
    }
}

impl Parser<ArgList> for ArgListParser {
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<ArgList> {
        // Expect opening parenthesis
        let Some(start_token) = stream.next() else {
            return ParseResult::error(Diagnostic::error(
                SymbolSpan {
                    start: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 1,
                    },
                    end: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 1,
                    },
                },
                "Unexpected end of input, expected '('",
            ));
        };

        if !matches!(start_token.r#type(), TokenType::LeftParen) {
            return ParseResult::error(Diagnostic::error(
                start_token.span().clone(),
                "Expected '(' to start argument list",
            ));
        }

        let start_span = start_token.span().start.clone();

        let args_result =
            self.parse_arg_list_loop(stream, options, &start_span);
        let (args, all_diagnostics) = if let Some(args) = args_result.value {
            (args, args_result.diagnostics)
        } else {
            return ParseResult {
                value: None,
                diagnostics: args_result.diagnostics,
            };
        };

        Self::finalize_arg_list(stream, start_span, args, all_diagnostics)
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        matches!(
            stream.peek_non_comment().map(Token::r#type),
            Some(TokenType::LeftParen)
        )
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::RightParen,
            TokenType::Comma,
            TokenType::At,
            TokenType::DoubleAt,
        ]
    }
}

/// Parse field attributes: `@qualified_ident arglist?`.
///
/// Parses the name and an optional argument list. Spans cover from `@` to the
/// end of the name or argument list.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::components::attributes::FieldAttributeParser;
/// # use prisma_rs::core::parser::traits::Parser;
/// # use prisma_rs::core::parser::stream::VectorTokenStream;
/// # use prisma_rs::core::parser::config::ParserOptions;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::At, (1,1), (1,1)),
///     Token::new(TokenType::Identifier("id".into()), (1,2), (1,3)),
/// ]);
/// let mut p = FieldAttributeParser::new();
/// let a = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
/// assert_eq!(a.name.parts[0].text, "id");
/// ```
#[derive(Debug, Default)]
pub struct FieldAttributeParser {
    qualified_ident_parser: QualifiedIdentParser,
    arg_list_parser: ArgListParser,
}

impl FieldAttributeParser {
    /// Create a new field attribute parser.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl Parser<FieldAttribute> for FieldAttributeParser {
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<FieldAttribute> {
        // Parse leading documentation comments
        let docs = parse_leading_docs(stream);

        // Expect @ token
        let Some(at_token) = stream.next() else {
            return ParseResult::error(Diagnostic::error(
                SymbolSpan {
                    start: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 1,
                    },
                    end: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 1,
                    },
                },
                "Unexpected end of input, expected '@'",
            ));
        };

        if !matches!(at_token.r#type(), TokenType::At) {
            return ParseResult::error(Diagnostic::error(
                at_token.span().clone(),
                "Expected '@' to start field attribute",
            ));
        }

        let start_span = at_token.span().start.clone();

        // Parse attribute name
        match self.qualified_ident_parser.parse(stream, options) {
            ParseResult {
                value: Some(name),
                diagnostics: name_diags,
            } => {
                let mut all_diagnostics = name_diags;

                // Check for optional argument list
                let args = if self.arg_list_parser.can_parse(stream) {
                    match self.arg_list_parser.parse(stream, options) {
                        ParseResult {
                            value: Some(args),
                            diagnostics: args_diags,
                        } => {
                            all_diagnostics.extend(args_diags);
                            Some(args)
                        }
                        ParseResult {
                            value: None,
                            diagnostics: args_diags,
                        } => {
                            all_diagnostics.extend(args_diags);
                            None // Continue without args if parsing fails
                        }
                    }
                } else {
                    None
                };

                // Calculate end span
                let end_span = args.as_ref().map_or_else(
                    || name.span.end.clone(),
                    |a| a.span.end.clone(),
                );

                let attribute_span = SymbolSpan {
                    start: start_span,
                    end: end_span,
                };

                let mut result = ParseResult::success(FieldAttribute {
                    name,
                    args,
                    docs,
                    span: attribute_span,
                });
                result.diagnostics = all_diagnostics;
                result
            }
            ParseResult {
                value: None,
                diagnostics,
            } => {
                let mut result = ParseResult::error(Diagnostic::error(
                    stream.peek().map_or_else(
                        || SymbolSpan {
                            start: start_span.clone(),
                            end: start_span,
                        },
                        |t| t.span().clone(),
                    ),
                    "Expected attribute name after '@'",
                ));
                result.diagnostics.extend(diagnostics);
                result
            }
        }
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        matches!(
            stream.peek_non_comment().map(Token::r#type),
            Some(TokenType::At)
        )
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::At,
            TokenType::DoubleAt,
            TokenType::Comma,
            TokenType::RightBrace,
        ]
    }
}

/// Parse block attributes: `@@qualified_ident arglist?`.
///
/// Parses the name and an optional argument list. Spans cover from `@@` to
/// the end of the name or argument list.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::components::attributes::BlockAttributeParser;
/// # use prisma_rs::core::parser::traits::Parser;
/// # use prisma_rs::core::parser::stream::VectorTokenStream;
/// # use prisma_rs::core::parser::config::ParserOptions;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::DoubleAt, (1,1), (1,2)),
///     Token::new(TokenType::Identifier("index".into()), (1,3), (1,7)),
///     Token::new(TokenType::LeftParen, (1,8), (1,8)),
///     Token::new(TokenType::Identifier("name".into()), (1,9), (1,12)),
///     Token::new(TokenType::Colon, (1,13), (1,13)),
///     Token::new(TokenType::Literal("\"idx\"".into()), (1,15), (1,19)),
///     Token::new(TokenType::RightParen, (1,20), (1,20)),
/// ]);
/// let mut p = BlockAttributeParser::new();
/// let a = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
/// assert_eq!(a.name.parts[0].text, "index");
/// assert!(a.args.is_some());
/// ```
#[derive(Debug, Default)]
pub struct BlockAttributeParser {
    qualified_ident_parser: QualifiedIdentParser,
    arg_list_parser: ArgListParser,
}

impl BlockAttributeParser {
    /// Create a new block attribute parser.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl Parser<BlockAttribute> for BlockAttributeParser {
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<BlockAttribute> {
        // Parse leading documentation comments
        let docs = parse_leading_docs(stream);

        // Expect @@ token
        let Some(double_at_token) = stream.next() else {
            return ParseResult::error(Diagnostic::error(
                SymbolSpan {
                    start: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 1,
                    },
                    end: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 1,
                    },
                },
                "Unexpected end of input, expected '@@'",
            ));
        };

        if !matches!(double_at_token.r#type(), TokenType::DoubleAt) {
            return ParseResult::error(Diagnostic::error(
                double_at_token.span().clone(),
                "Expected '@@' to start block attribute",
            ));
        }

        let start_span = double_at_token.span().start.clone();

        // Parse attribute name
        match self.qualified_ident_parser.parse(stream, options) {
            ParseResult {
                value: Some(name),
                diagnostics: name_diags,
            } => {
                let mut all_diagnostics = name_diags;

                // Check for optional argument list
                let args = if self.arg_list_parser.can_parse(stream) {
                    match self.arg_list_parser.parse(stream, options) {
                        ParseResult {
                            value: Some(args),
                            diagnostics: args_diags,
                        } => {
                            all_diagnostics.extend(args_diags);
                            Some(args)
                        }
                        ParseResult {
                            value: None,
                            diagnostics: args_diags,
                        } => {
                            all_diagnostics.extend(args_diags);
                            None // Continue without args if parsing fails
                        }
                    }
                } else {
                    None
                };

                // Calculate end span
                let end_span = args.as_ref().map_or_else(
                    || name.span.end.clone(),
                    |a| a.span.end.clone(),
                );

                let attribute_span = SymbolSpan {
                    start: start_span,
                    end: end_span,
                };

                let mut result = ParseResult::success(BlockAttribute {
                    name,
                    args,
                    docs,
                    span: attribute_span,
                });
                result.diagnostics = all_diagnostics;
                result
            }
            ParseResult {
                value: None,
                diagnostics,
            } => {
                let mut result = ParseResult::error(Diagnostic::error(
                    stream.peek().map_or_else(
                        || SymbolSpan {
                            start: start_span.clone(),
                            end: start_span,
                        },
                        |t| t.span().clone(),
                    ),
                    "Expected attribute name after '@@'",
                ));
                result.diagnostics.extend(diagnostics);
                result
            }
        }
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        matches!(
            stream.peek_non_comment().map(Token::r#type),
            Some(TokenType::DoubleAt)
        )
    }
}

#[cfg(test)]
mod tests {
    #![expect(clippy::unwrap_used)]

    use crate::core::parser::ParserOptions;
    use crate::core::parser::VectorTokenStream;
    use crate::core::parser::ast::Arg;
    use crate::core::parser::components::attributes::ArgListParser;
    use crate::core::parser::components::attributes::BlockAttributeParser;
    use crate::core::parser::components::attributes::FieldAttributeParser;
    use crate::core::parser::traits::Parser;
    use crate::core::scanner::tokens::Token;
    use crate::core::scanner::tokens::TokenType;

    fn create_test_token(token_type: TokenType) -> Token {
        Token::new(token_type, (1, 1), (1, 10))
    }

    #[test]
    fn empty_arg_list() {
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let arg_list = result.value.unwrap();
        assert_eq!(arg_list.items.len(), 0);
    }

    #[test]
    fn positional_args() {
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Literal("\"hello\"".to_string())),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Literal("42".to_string())),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let arg_list = result.value.unwrap();
        assert_eq!(arg_list.items.len(), 2);
        assert!(matches!(arg_list.items[0], Arg::Positional(_)));
        assert!(matches!(arg_list.items[1], Arg::Positional(_)));
    }

    #[test]
    fn named_args() {
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Identifier("name".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Literal("\"John\"".to_string())),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let arg_list = result.value.unwrap();
        assert_eq!(arg_list.items.len(), 1);
        if let Arg::Named(named_arg) = &arg_list.items[0] {
            assert_eq!(named_arg.name.text, "name");
        } else {
            panic!("Expected named argument");
        }
    }

    #[test]
    fn mixed_args() {
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Literal("\"positional\"".to_string())),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Identifier("key".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Literal("\"value\"".to_string())),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let arg_list = result.value.unwrap();
        assert_eq!(arg_list.items.len(), 2);
        assert!(matches!(arg_list.items[0], Arg::Positional(_)));
        assert!(matches!(arg_list.items[1], Arg::Named(_)));
    }

    #[test]
    fn field_attribute_simple() {
        let tokens = vec![
            create_test_token(TokenType::At),
            create_test_token(TokenType::Identifier("id".to_string())),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = FieldAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts.len(), 1);
        assert_eq!(attr.name.parts[0].text, "id");
        assert!(attr.args.is_none());
    }

    #[test]
    fn field_attribute_with_args() {
        let tokens = vec![
            create_test_token(TokenType::At),
            create_test_token(TokenType::Identifier("default".to_string())),
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Identifier("cuid".to_string())),
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::RightParen),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = FieldAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts[0].text, "default");
        assert!(attr.args.is_some());
        assert_eq!(attr.args.unwrap().items.len(), 1);
    }

    #[test]
    fn field_attribute_qualified() {
        let tokens = vec![
            create_test_token(TokenType::At),
            create_test_token(TokenType::Identifier("db".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("VarChar".to_string())),
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Literal("255".to_string())),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = FieldAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts.len(), 2);
        assert_eq!(attr.name.parts[0].text, "db");
        assert_eq!(attr.name.parts[1].text, "VarChar");
        assert!(attr.args.is_some());
    }

    #[test]
    fn block_attribute_simple() {
        let tokens = vec![
            create_test_token(TokenType::DoubleAt),
            create_test_token(TokenType::Identifier("unique".to_string())),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = BlockAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts.len(), 1);
        assert_eq!(attr.name.parts[0].text, "unique");
        assert!(attr.args.is_none());
    }

    #[test]
    fn block_attribute_with_args() {
        let tokens = vec![
            create_test_token(TokenType::DoubleAt),
            create_test_token(TokenType::Identifier("index".to_string())),
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::LeftBracket),
            create_test_token(TokenType::Identifier("name".to_string())),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Identifier("email".to_string())),
            create_test_token(TokenType::RightBracket),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = BlockAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts[0].text, "index");
        assert!(attr.args.is_some());
        assert_eq!(attr.args.unwrap().items.len(), 1); // Array expression as one argument
    }

    #[test]
    fn arg_list_can_parse() {
        let parser = ArgListParser::new();

        // Test valid tokens
        let tokens = vec![create_test_token(TokenType::LeftParen)];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));

        // Test invalid tokens
        let tokens = vec![create_test_token(TokenType::At)];
        let stream = VectorTokenStream::new(tokens);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn field_attribute_can_parse() {
        let parser = FieldAttributeParser::new();

        // Test valid tokens
        let tokens = vec![create_test_token(TokenType::At)];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));

        // Test invalid tokens
        let tokens = vec![create_test_token(TokenType::DoubleAt)];
        let stream = VectorTokenStream::new(tokens);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn field_attribute_can_parse_with_comments() {
        let parser = FieldAttributeParser::new();

        // Test with leading comments
        let tokens = vec![
            create_test_token(TokenType::Comment(
                " // some comment ".to_string(),
            )),
            create_test_token(TokenType::DocComment(
                " /// some doc comment ".to_string(),
            )),
            create_test_token(TokenType::At),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));

        // Test with comments but wrong token
        let tokens = vec![
            create_test_token(TokenType::Comment(
                " // some comment ".to_string(),
            )),
            create_test_token(TokenType::LeftParen),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn block_attribute_can_parse() {
        let parser = BlockAttributeParser::new();

        // Test valid tokens
        let tokens = vec![create_test_token(TokenType::DoubleAt)];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));

        // Test invalid tokens
        let tokens = vec![create_test_token(TokenType::At)];
        let stream = VectorTokenStream::new(tokens);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn trailing_comma_in_args() {
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Literal("\"value1\"".to_string())),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Literal("\"value2\"".to_string())),
            create_test_token(TokenType::Comma), // Trailing comma
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let arg_list = result.value.unwrap();
        assert_eq!(arg_list.items.len(), 2); // Should ignore trailing comma
    }

    // ========== BATTLE-TESTING: Complex Real-World Scenarios ==========

    #[test]
    fn complex_db_attribute_with_multiple_args() {
        // @db.VarChar(255, collate: "utf8_general_ci", charset: "utf8")
        let tokens = vec![
            create_test_token(TokenType::At),
            create_test_token(TokenType::Identifier("db".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("VarChar".to_string())),
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Literal("255".to_string())), // positional
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Identifier("collate".to_string())), // named
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Literal(
                "\"utf8_general_ci\"".to_string(),
            )),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Identifier("charset".to_string())), // named
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Literal("\"utf8\"".to_string())),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = FieldAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts.len(), 2);
        assert_eq!(attr.name.parts[0].text, "db");
        assert_eq!(attr.name.parts[1].text, "VarChar");

        let args = attr.args.unwrap();
        assert_eq!(args.items.len(), 3);

        // First arg should be positional
        assert!(matches!(args.items[0], Arg::Positional(_)));
        // Second and third should be named
        assert!(matches!(args.items[1], Arg::Named(_)));
        assert!(matches!(args.items[2], Arg::Named(_)));

        if let Arg::Named(ref named) = args.items[1] {
            assert_eq!(named.name.text, "collate");
        }
        if let Arg::Named(ref named) = args.items[2] {
            assert_eq!(named.name.text, "charset");
        }
    }

    #[test]
    fn complex_index_attribute_with_array_and_options() {
        // @@index([userId, createdAt], name: "user_created_idx", type: Hash)
        let tokens = vec![
            create_test_token(TokenType::DoubleAt),
            create_test_token(TokenType::Identifier("index".to_string())),
            create_test_token(TokenType::LeftParen),
            // Array argument
            create_test_token(TokenType::LeftBracket),
            create_test_token(TokenType::Identifier("userId".to_string())),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Identifier("createdAt".to_string())),
            create_test_token(TokenType::RightBracket),
            create_test_token(TokenType::Comma),
            // Named arguments
            create_test_token(TokenType::Identifier("name".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Literal(
                "\"user_created_idx\"".to_string(),
            )),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Identifier("type".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Identifier("Hash".to_string())),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = BlockAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts[0].text, "index");

        let args = attr.args.unwrap();
        assert_eq!(args.items.len(), 3);

        // First should be positional (array)
        assert!(matches!(args.items[0], Arg::Positional(_)));
        // Others should be named
        assert!(matches!(args.items[1], Arg::Named(_)));
        assert!(matches!(args.items[2], Arg::Named(_)));
    }

    #[test]
    fn default_attribute_with_function_call() {
        // @default(now())
        let tokens = vec![
            create_test_token(TokenType::At),
            create_test_token(TokenType::Identifier("default".to_string())),
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Identifier("now".to_string())),
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::RightParen),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = FieldAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts[0].text, "default");

        let args = attr.args.unwrap();
        assert_eq!(args.items.len(), 1);

        // Should be a function call expression
        if let Arg::Positional(ref pos) = args.items[0] {
            assert!(matches!(
                pos.value,
                crate::core::parser::ast::Expr::FuncCall(_)
            ));
        }
    }

    #[test]
    fn relation_attribute_with_complex_args() {
        // @relation("UserPosts", fields: [authorId], references: [id], onDelete: Cascade)
        let tokens = vec![
            create_test_token(TokenType::At),
            create_test_token(TokenType::Identifier("relation".to_string())),
            create_test_token(TokenType::LeftParen),
            // Positional string arg
            create_test_token(TokenType::Literal("\"UserPosts\"".to_string())),
            create_test_token(TokenType::Comma),
            // fields: [authorId]
            create_test_token(TokenType::Identifier("fields".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::LeftBracket),
            create_test_token(TokenType::Identifier("authorId".to_string())),
            create_test_token(TokenType::RightBracket),
            create_test_token(TokenType::Comma),
            // references: [id]
            create_test_token(TokenType::Identifier("references".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::LeftBracket),
            create_test_token(TokenType::Identifier("id".to_string())),
            create_test_token(TokenType::RightBracket),
            create_test_token(TokenType::Comma),
            // onDelete: Cascade
            create_test_token(TokenType::Identifier("onDelete".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Identifier("Cascade".to_string())),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = FieldAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts[0].text, "relation");

        let args = attr.args.unwrap();
        assert_eq!(args.items.len(), 4);

        // First should be positional string
        assert!(matches!(args.items[0], Arg::Positional(_)));
        // Others should be named
        for i in 1..4 {
            assert!(matches!(args.items[i], Arg::Named(_)));
        }

        // Verify named arg names
        if let Arg::Named(ref named) = args.items[1] {
            assert_eq!(named.name.text, "fields");
        }
        if let Arg::Named(ref named) = args.items[2] {
            assert_eq!(named.name.text, "references");
        }
        if let Arg::Named(ref named) = args.items[3] {
            assert_eq!(named.name.text, "onDelete");
        }
    }

    #[test]
    fn nested_object_in_attribute() {
        // @attr({key: "value", nested: {inner: true}})
        let tokens = vec![
            create_test_token(TokenType::At),
            create_test_token(TokenType::Identifier("attr".to_string())),
            create_test_token(TokenType::LeftParen),
            // Object expression
            create_test_token(TokenType::LeftBrace),
            create_test_token(TokenType::Identifier("key".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Literal("\"value\"".to_string())),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Identifier("nested".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::LeftBrace),
            create_test_token(TokenType::Identifier("inner".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Literal("true".to_string())),
            create_test_token(TokenType::RightBrace),
            create_test_token(TokenType::RightBrace),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = FieldAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts[0].text, "attr");

        let args = attr.args.unwrap();
        assert_eq!(args.items.len(), 1);

        // Should be an object expression
        if let Arg::Positional(ref pos) = args.items[0] {
            assert!(matches!(
                pos.value,
                crate::core::parser::ast::Expr::Object(_)
            ));
        }
    }

    // ========== ERROR HANDLING TESTS ==========

    #[test]
    fn malformed_arg_list_missing_closing_paren() {
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Literal("\"value\"".to_string())),
            // Missing RightParen
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(!result.is_success());
        assert!(result.has_errors());
    }

    #[test]
    fn malformed_arg_list_missing_comma() {
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Literal("\"value1\"".to_string())),
            create_test_token(TokenType::Literal("\"value2\"".to_string())), // Missing comma
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(!result.is_success());
        assert!(result.has_errors());
    }

    #[test]
    fn malformed_named_arg_missing_colon() {
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Identifier("name".to_string())),
            create_test_token(TokenType::Literal("\"value\"".to_string())), // Missing colon
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(!result.is_success());
        assert!(result.has_errors());
    }

    #[test]
    fn malformed_named_arg_missing_value() {
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Identifier("name".to_string())),
            create_test_token(TokenType::Colon),
            // Missing value
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(!result.is_success());
        assert!(result.has_errors());
    }

    #[test]
    fn attribute_without_name() {
        let tokens = vec![
            create_test_token(TokenType::At),
            // Missing attribute name
            create_test_token(TokenType::LeftParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = FieldAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(!result.is_success());
        assert!(result.has_errors());
    }

    #[test]
    fn block_attribute_without_name() {
        let tokens = vec![
            create_test_token(TokenType::DoubleAt),
            // Missing attribute name
            create_test_token(TokenType::LeftParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = BlockAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(!result.is_success());
        assert!(result.has_errors());
    }

    // ========== EDGE CASES ==========

    #[test]
    fn empty_qualified_name_in_named_arg() {
        // Tests the qualified identifier to simple identifier conversion
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Identifier("a".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("b".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Literal("\"value\"".to_string())),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let arg_list = result.value.unwrap();
        assert_eq!(arg_list.items.len(), 1);

        if let Arg::Named(ref named) = arg_list.items[0] {
            // Should join qualified parts with dots
            assert_eq!(named.name.text, "a.b");
        }
    }

    #[test]
    fn very_long_qualified_attribute_name() {
        // @a.b.c.d.e.f.g
        let tokens = vec![
            create_test_token(TokenType::At),
            create_test_token(TokenType::Identifier("a".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("b".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("c".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("d".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("e".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("f".to_string())),
            create_test_token(TokenType::Dot),
            create_test_token(TokenType::Identifier("g".to_string())),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = FieldAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts.len(), 7);
        assert_eq!(attr.name.parts[0].text, "a");
        assert_eq!(attr.name.parts[6].text, "g");
    }

    #[test]
    fn attribute_with_empty_arg_list() {
        // @attr()
        let tokens = vec![
            create_test_token(TokenType::At),
            create_test_token(TokenType::Identifier("attr".to_string())),
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = FieldAttributeParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let attr = result.value.unwrap();
        assert_eq!(attr.name.parts[0].text, "attr");

        let args = attr.args.unwrap();
        assert_eq!(args.items.len(), 0); // Empty arg list
    }

    #[test]
    fn large_number_of_arguments() {
        // Test with 10 arguments to stress-test the parser
        let mut tokens = vec![create_test_token(TokenType::LeftParen)];

        for i in 0..10 {
            if i > 0 {
                tokens.push(create_test_token(TokenType::Comma));
            }
            tokens.push(create_test_token(TokenType::Literal(format!(
                "\"arg{i}\""
            ))));
        }
        tokens.push(create_test_token(TokenType::RightParen));

        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let arg_list = result.value.unwrap();
        assert_eq!(arg_list.items.len(), 10);

        // All should be positional
        for arg in &arg_list.items {
            assert!(matches!(arg, Arg::Positional(_)));
        }
    }

    #[test]
    fn mixed_expressions_in_args() {
        // Test different expression types: string, int, bool, null, array, object
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Literal("\"string\"".to_string())),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Literal("42".to_string())),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Literal("true".to_string())),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Literal("null".to_string())),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::LeftBracket),
            create_test_token(TokenType::Literal("1".to_string())),
            create_test_token(TokenType::RightBracket),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::LeftBrace),
            create_test_token(TokenType::Identifier("key".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Literal("\"value\"".to_string())),
            create_test_token(TokenType::RightBrace),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ArgListParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        let arg_list = result.value.unwrap();
        assert_eq!(arg_list.items.len(), 6);

        // Verify expression types
        let expressions: Vec<_> = arg_list
            .items
            .iter()
            .map(|arg| {
                if let Arg::Positional(pos) = arg {
                    &pos.value
                } else {
                    panic!("Expected positional arg");
                }
            })
            .collect();

        assert!(matches!(
            expressions[0],
            crate::core::parser::ast::Expr::StringLit(_)
        ));
        assert!(matches!(
            expressions[1],
            crate::core::parser::ast::Expr::IntLit(_)
        ));
        assert!(matches!(
            expressions[2],
            crate::core::parser::ast::Expr::BoolLit(_)
        ));
        assert!(matches!(
            expressions[3],
            crate::core::parser::ast::Expr::NullLit(_)
        ));
        assert!(matches!(
            expressions[4],
            crate::core::parser::ast::Expr::Array(_)
        ));
        assert!(matches!(
            expressions[5],
            crate::core::parser::ast::Expr::Object(_)
        ));
    }
}
