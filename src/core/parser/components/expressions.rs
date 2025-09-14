//! Parse expressions with a Pratt parser.
//!
//! Implements a high-performance Pratt parser for Prisma schema expressions:
//! literals, identifier references, function calls, arrays, and objects.
//! Spans are preserved, comments are ignored for lookahead where relevant,
//! and trailing commas are accepted in arrays and objects.

use crate::core::parser::components::primitives::QualifiedIdentParser;
use crate::core::parser::stream::TokenStreamExt;
use crate::core::parser::{
    ast::{
        ArrayExpr, BoolLit, Expr, FloatLit, FuncCall, HasSpan, IdentRef,
        IntLit, NullLit, ObjectEntry, ObjectExpr, ObjectKey, StringLit,
    },
    config::{Diagnostic, ParseResult, ParserOptions},
    traits::{Parser, TokenStream},
};
use crate::core::scanner::tokens::{SymbolSpan, Token, TokenType};

/// Parse Prisma expressions into `Expr` nodes.
///
/// Optimized for minimal allocations and efficient token handling.
/// Supports literals (string, int, float, bool, null), identifier
/// references, function calls, arrays, and objects.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::components::expressions::ExpressionParser;
/// # use prisma_rs::core::parser::traits::Parser;
/// # use prisma_rs::core::parser::stream::VectorTokenStream;
/// # use prisma_rs::core::parser::config::ParserOptions;
/// # use prisma_rs::core::parser::ast::Expr;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// // Numeric literal
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::Literal("42".into()), (1,1), (1,2)),
/// ]);
/// let mut p = ExpressionParser::new();
/// let e = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
/// assert!(matches!(e, Expr::IntLit(_)));
///
/// // Array literal
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::LeftBracket, (1,1), (1,1)),
///     Token::new(TokenType::Literal("1".into()), (1,2), (1,2)),
///     Token::new(TokenType::Comma, (1,3), (1,3)),
///     Token::new(TokenType::Literal("2".into()), (1,5), (1,5)),
///     Token::new(TokenType::RightBracket, (1,6), (1,6)),
/// ]);
/// let e = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
/// assert!(matches!(e, Expr::Array(_)));
///
/// // Function call: env("DATABASE_URL")
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::Identifier("env".into()), (1,1), (1,4)),
///     Token::new(TokenType::LeftParen, (1,5), (1,5)),
///     Token::new(TokenType::Literal("\"DATABASE_URL\"".into()), (1,6), (1,20)),
///     Token::new(TokenType::RightParen, (1,21), (1,21)),
/// ]);
/// let e = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
/// assert!(matches!(e, Expr::FuncCall(_)));
///
/// // Object literal: { x: 1 }
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::LeftBrace, (1,1), (1,1)),
///     Token::new(TokenType::Identifier("x".into()), (1,2), (1,2)),
///     Token::new(TokenType::Colon, (1,3), (1,3)),
///     Token::new(TokenType::Literal("1".into()), (1,4), (1,4)),
///     Token::new(TokenType::RightBrace, (1,5), (1,5)),
/// ]);
/// let e = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
/// assert!(matches!(e, Expr::Object(_)));
/// ```
#[derive(Debug, Default)]
pub struct ExpressionParser {
    qualified_ident_parser: QualifiedIdentParser,
}

impl ExpressionParser {
    /// Create a new expression parser.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a string literal efficiently.
    fn parse_string_literal(stream: &mut dyn TokenStream) -> ParseResult<Expr> {
        if let Some(token) = stream.next() {
            if let TokenType::Literal(value) = token.r#type() {
                // Remove quotes efficiently without allocation if possible
                let unquoted = if value.len() >= 2
                    && value.starts_with('"')
                    && value.ends_with('"')
                {
                    value[1..value.len() - 1].to_string()
                } else {
                    value.clone()
                };

                ParseResult::success(Expr::StringLit(StringLit {
                    value: unquoted,
                    span: token.span().clone(),
                }))
            } else {
                unreachable!("Token type was checked by caller")
            }
        } else {
            ParseResult::error(Diagnostic::error(
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
                "Unexpected end of input",
            ))
        }
    }

    /// Parse a numeric literal efficiently.
    fn parse_numeric_literal(
        stream: &mut dyn TokenStream,
    ) -> ParseResult<Expr> {
        if let Some(token) = stream.next() {
            if let TokenType::Literal(value) = token.r#type() {
                let span = token.span().clone();

                // Efficient numeric type detection
                if value.contains('.') {
                    ParseResult::success(Expr::FloatLit(FloatLit {
                        value: value.clone(),
                        span,
                    }))
                } else {
                    ParseResult::success(Expr::IntLit(IntLit {
                        value: value.clone(),
                        span,
                    }))
                }
            } else {
                unreachable!("Token type was checked by caller")
            }
        } else {
            ParseResult::error(Diagnostic::error(
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
                "Unexpected end of input",
            ))
        }
    }

    /// Parse boolean and null literals.
    fn parse_bool_or_null_literal(
        stream: &mut dyn TokenStream,
    ) -> ParseResult<Expr> {
        if let Some(token) = stream.next() {
            if let TokenType::Literal(value) = token.r#type() {
                let span = token.span().clone();
                match value.as_str() {
                    "true" | "false" => {
                        let bool_value = value == "true";
                        ParseResult::success(Expr::BoolLit(BoolLit {
                            value: bool_value,
                            span,
                        }))
                    }
                    "null" => {
                        ParseResult::success(Expr::NullLit(NullLit { span }))
                    }
                    _ => unreachable!("Value was checked by caller"),
                }
            } else {
                unreachable!("Token type was checked by caller")
            }
        } else {
            ParseResult::error(Diagnostic::error(
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
                "Unexpected end of input",
            ))
        }
    }

    /// Parse a parenthesized expression.
    fn parse_parenthesized_expr(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Expr> {
        stream.next(); // consume '('
        let inner_result = self.parse(stream, options);

        // Expect closing parenthesis
        match stream.peek() {
            Some(token) if matches!(token.r#type(), TokenType::RightParen) => {
                stream.next(); // consume ')'
                inner_result
            }
            Some(token) => ParseResult::error(Diagnostic::error(
                token.span().clone(),
                "Expected ')' after expression",
            )),
            None => ParseResult::error(Diagnostic::error(
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
                "Unexpected end of input, expected ')'",
            )),
        }
    }

    /// Parse a primary expression.
    ///
    /// Recognizes literals, arrays, objects, parentheses, identifiers, and
    /// function calls.
    fn parse_primary(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Expr> {
        // Fast path: check token type without consuming
        let Some(token) = stream.peek() else {
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
                "Unexpected end of input, expected expression",
            ));
        };

        match token.r#type() {
            // String literals - fast path
            TokenType::Literal(value) if value.starts_with('"') => {
                Self::parse_string_literal(stream)
            }

            // Numeric literals - detect and parse efficiently
            TokenType::Literal(value) if Self::is_numeric(value) => {
                Self::parse_numeric_literal(stream)
            }

            // Boolean and null literals (stored as TokenType::Literal)
            TokenType::Literal(value)
                if matches!(value.as_str(), "true" | "false" | "null") =>
            {
                Self::parse_bool_or_null_literal(stream)
            }

            // Array expressions - optimized for common case
            TokenType::LeftBracket => self.parse_array_expr(stream, options),

            // Object expressions
            TokenType::LeftBrace => self.parse_object_expr(stream, options),

            // Parenthesized expressions
            TokenType::LeftParen => {
                self.parse_parenthesized_expr(stream, options)
            }

            // Identifiers - could be simple references or function calls
            TokenType::Identifier(_) => {
                self.parse_ident_or_func_call(stream, options)
            }

            _ => ParseResult::error(Diagnostic::error(
                token.span().clone(),
                format!("Unexpected token in expression: {:?}", token.r#type()),
            )),
        }
    }

    /// Parse function arguments efficiently.
    fn parse_function_args(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Option<crate::core::parser::ast::ArgList>> {
        // Parse arguments efficiently - preallocate for common case
        let mut args = Vec::with_capacity(4);

        // Parse argument list
        loop {
            let Some(token) = stream.peek() else {
                break;
            };

            if matches!(token.r#type(), TokenType::RightParen) {
                break;
            }

            if !args.is_empty() {
                // Expect comma between arguments
                if !matches!(token.r#type(), TokenType::Comma) {
                    return ParseResult::error(Diagnostic::error(
                        token.span().clone(),
                        "Expected ',' between function arguments",
                    ));
                }
                stream.next(); // consume comma

                // Check for trailing comma
                if let Some(next_token) = stream.peek()
                    && matches!(next_token.r#type(), TokenType::RightParen)
                {
                    break;
                }
            }

            // Parse the argument expression
            match self.parse(stream, options) {
                ParseResult {
                    value: Some(expr),
                    diagnostics: _arg_diags,
                } => {
                    args.push(crate::core::parser::ast::Arg::Positional(
                        crate::core::parser::ast::PositionalArg {
                            span: expr.span().clone(),
                            value: expr,
                        },
                    ));
                }
                ParseResult {
                    value: None,
                    diagnostics: _arg_diags,
                } => {
                    return ParseResult::error(Diagnostic::error(
                        stream.peek().map_or_else(
                            || SymbolSpan {
                                start: crate::core::scanner::tokens::SymbolLocation { line: 1, column: 1 },
                                end: crate::core::scanner::tokens::SymbolLocation { line: 1, column: 1 },
                            },
                            |t| t.span().clone()
                        ),
                        "Expected expression in function argument",
                    ));
                }
            }
        }

        if args.is_empty() {
            ParseResult::success(None)
        } else {
            // Create span from first to last arg
            let start_span = args[0].span().start.clone();
            let end_span = args[args.len() - 1].span().end.clone();
            ParseResult::success(Some(crate::core::parser::ast::ArgList {
                items: args,
                span: SymbolSpan {
                    start: start_span,
                    end: end_span,
                },
            }))
        }
    }

    fn parse_func_call(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
        name: crate::core::parser::ast::QualifiedIdent,
        start_span: crate::core::scanner::tokens::SymbolLocation,
        diagnostics: Vec<Diagnostic>,
    ) -> ParseResult<Expr> {
        // Parse as function call
        stream.next(); // consume '('

        let args_result = self.parse_function_args(stream, options);

        // Expect closing parenthesis
        match stream.peek() {
            Some(token) if matches!(token.r#type(), TokenType::RightParen) => {
                if let Some(close_token) = stream.next() {
                    let end_span = close_token.span().end.clone();

                    let func_span = SymbolSpan {
                        start: start_span,
                        end: end_span,
                    };
                    let arg_list = match args_result {
                        ParseResult {
                            value: Some(args),
                            diagnostics: _,
                        } => args,
                        ParseResult {
                            value: None,
                            diagnostics: _,
                        } => None,
                    };

                    let mut result =
                        ParseResult::success(Expr::FuncCall(FuncCall {
                            callee: name,
                            args: arg_list,
                            span: func_span,
                        }));
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
                "Expected ')' after function arguments",
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

    /// Parse identifier reference or function call efficiently.
    fn parse_ident_or_func_call(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Expr> {
        // Parse the identifier first
        match self.qualified_ident_parser.parse(stream, options) {
            ParseResult {
                value: Some(name),
                diagnostics,
            } => {
                let start_span = name.span.start.clone();

                // Check if this is a function call (peek for '(')
                if let Some(token) = stream.peek()
                    && matches!(token.r#type(), TokenType::LeftParen)
                {
                    self.parse_func_call(
                        stream,
                        options,
                        name,
                        start_span,
                        diagnostics,
                    )
                } else {
                    // Simple identifier reference
                    let span = name.span.clone();
                    let mut result =
                        ParseResult::success(Expr::IdentRef(IdentRef {
                            name,
                            span,
                        }));
                    result.diagnostics = diagnostics;
                    result
                }
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
                    "Expected identifier in expression",
                ));
                result.diagnostics.extend(diagnostics);
                result
            }
        }
    }

    /// Parse array elements efficiently.
    fn parse_array_elements(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Vec<Expr>> {
        let mut elements = Vec::with_capacity(8);

        loop {
            let Some(token) = stream.peek() else {
                break;
            };

            if matches!(token.r#type(), TokenType::RightBracket) {
                break;
            }

            if !elements.is_empty() {
                // Expect comma between elements
                if matches!(token.r#type(), TokenType::Comma) {
                    stream.next(); // consume comma

                    // Check for trailing comma
                    if let Some(next_token) = stream.peek()
                        && matches!(
                            next_token.r#type(),
                            TokenType::RightBracket
                        )
                    {
                        break;
                    }
                } else {
                    return ParseResult::error(Diagnostic::error(
                        token.span().clone(),
                        "Expected ',' between array elements",
                    ));
                }
            }

            // Parse array element
            match self.parse(stream, options) {
                ParseResult {
                    value: Some(expr),
                    diagnostics: _,
                } => {
                    elements.push(expr);
                }
                ParseResult {
                    value: None,
                    diagnostics: _,
                } => {
                    return ParseResult::error(Diagnostic::error(
                        stream.peek().map_or_else(
                            || SymbolSpan {
                                start: crate::core::scanner::tokens::SymbolLocation { line: 1, column: 1 },
                                end: crate::core::scanner::tokens::SymbolLocation { line: 1, column: 1 },
                            },
                            |t| t.span().clone()
                        ),
                        "Expected expression in array",
                    ));
                }
            }
        }

        ParseResult::success(elements)
    }

    /// Parse array expression with performance optimizations.
    fn parse_array_expr(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Expr> {
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
                "Unexpected end of input",
            ));
        };
        let start_span = start_token.span().start.clone();

        // Parse elements
        let elements_result = self.parse_array_elements(stream, options);
        let elements = match elements_result {
            ParseResult {
                value: Some(elems),
                diagnostics: _,
            } => elems,
            ParseResult {
                value: None,
                diagnostics: _,
            } => {
                return ParseResult::error(Diagnostic::error(
                    SymbolSpan {
                        start: start_span.clone(),
                        end: start_span,
                    },
                    "Failed to parse array elements",
                ));
            }
        };

        // Expect closing bracket
        match stream.peek() {
            Some(token)
                if matches!(token.r#type(), TokenType::RightBracket) =>
            {
                if let Some(close_token) = stream.next() {
                    let end_span = close_token.span().end.clone();

                    ParseResult::success(Expr::Array(ArrayExpr {
                        elements,
                        span: SymbolSpan {
                            start: start_span,
                            end: end_span,
                        },
                    }))
                } else {
                    ParseResult::error(Diagnostic::error(
                        SymbolSpan {
                            start: start_span.clone(),
                            end: start_span,
                        },
                        "Unexpected end of input, expected ']'",
                    ))
                }
            }
            Some(token) => ParseResult::error(Diagnostic::error(
                token.span().clone(),
                "Expected ']' after array elements",
            )),
            None => ParseResult::error(Diagnostic::error(
                SymbolSpan {
                    start: start_span.clone(),
                    end: start_span,
                },
                "Unexpected end of input, expected ']'",
            )),
        }
    }

    /// Parse a single object key.
    fn parse_object_key(
        stream: &mut dyn TokenStream,
    ) -> ParseResult<ObjectKey> {
        match stream.peek() {
            Some(token)
                if matches!(token.r#type(), TokenType::Identifier(_)) =>
            {
                if let Some(token) = stream.next() {
                    if let TokenType::Identifier(text) = token.r#type() {
                        ParseResult::success(ObjectKey::Ident(
                            crate::core::parser::ast::Ident {
                                text: text.clone(),
                                span: token.span().clone(),
                            },
                        ))
                    } else {
                        unreachable!("Token type was checked")
                    }
                } else {
                    ParseResult::error(Diagnostic::error(
                        SymbolSpan {
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
                        "Unexpected end of input",
                    ))
                }
            }
            Some(token) if matches!(token.r#type(), TokenType::Literal(value) if value.starts_with('"')) => {
                if let Some(token) = stream.next() {
                    if let TokenType::Literal(value) = token.r#type() {
                        let unquoted = if value.len() >= 2
                            && value.starts_with('"')
                            && value.ends_with('"')
                        {
                            value[1..value.len() - 1].to_string()
                        } else {
                            value.clone()
                        };
                        ParseResult::success(ObjectKey::String(StringLit {
                            value: unquoted,
                            span: token.span().clone(),
                        }))
                    } else {
                        unreachable!("Token type was checked")
                    }
                } else {
                    ParseResult::error(Diagnostic::error(
                        SymbolSpan {
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
                        "Unexpected end of input",
                    ))
                }
            }
            Some(token) => ParseResult::error(Diagnostic::error(
                token.span().clone(),
                "Expected identifier or string literal as object key",
            )),
            None => ParseResult::error(Diagnostic::error(
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
                "Unexpected end of input, expected object key",
            )),
        }
    }

    fn parse_single_object_entry(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<ObjectEntry> {
        // Parse key
        let key_result = Self::parse_object_key(stream);
        let key = match key_result {
            ParseResult {
                value: Some(k),
                diagnostics: _,
            } => k,
            ParseResult {
                value: None,
                diagnostics,
            } => {
                return ParseResult {
                    value: None,
                    diagnostics,
                };
            }
        };

        // Expect colon
        match stream.peek() {
            Some(token) if matches!(token.r#type(), TokenType::Colon) => {
                stream.next(); // consume ':'
            }
            Some(token) => {
                return ParseResult::error(Diagnostic::error(
                    token.span().clone(),
                    "Expected ':' after object key",
                ));
            }
            None => {
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
                    "Unexpected end of input, expected ':'",
                ));
            }
        }

        // Parse value
        match self.parse(stream, options) {
            ParseResult {
                value: Some(value),
                diagnostics,
            } => {
                let entry_span = SymbolSpan {
                    start: key.span().start.clone(),
                    end: value.span().end.clone(),
                };
                let mut result = ParseResult::success(ObjectEntry {
                    key,
                    value,
                    span: entry_span,
                });
                result.diagnostics = diagnostics;
                result
            }
            ParseResult {
                value: None,
                diagnostics,
            } => ParseResult {
                value: None,
                diagnostics,
            },
        }
    }

    /// Parse object entries efficiently.
    fn parse_object_entries(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Vec<ObjectEntry>> {
        let mut entries = Vec::with_capacity(4);

        loop {
            let Some(token) = stream.peek() else {
                break;
            };

            if matches!(token.r#type(), TokenType::RightBrace) {
                break;
            }

            if !entries.is_empty() {
                // Expect comma between entries
                if matches!(token.r#type(), TokenType::Comma) {
                    stream.next(); // consume comma

                    // Check for trailing comma
                    if let Some(next_token) = stream.peek()
                        && matches!(next_token.r#type(), TokenType::RightBrace)
                    {
                        break;
                    }
                } else {
                    return ParseResult::error(Diagnostic::error(
                        token.span().clone(),
                        "Expected ',' between object entries",
                    ));
                }
            }

            // Parse the entry
            match self.parse_single_object_entry(stream, options) {
                ParseResult {
                    value: Some(entry),
                    diagnostics: _,
                } => {
                    entries.push(entry);
                }
                ParseResult {
                    value: None,
                    diagnostics,
                } => {
                    return ParseResult {
                        value: None,
                        diagnostics,
                    };
                }
            }
        }

        ParseResult::success(entries)
    }

    /// Parse object expression efficiently.
    fn parse_object_expr(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Expr> {
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
                "Unexpected end of input",
            ));
        };
        let start_span = start_token.span().start.clone();

        // Parse entries
        let entries_result = self.parse_object_entries(stream, options);
        let entries = match entries_result {
            ParseResult {
                value: Some(entries),
                diagnostics: _,
            } => entries,
            ParseResult {
                value: None,
                diagnostics: _,
            } => {
                return ParseResult::error(Diagnostic::error(
                    SymbolSpan {
                        start: start_span.clone(),
                        end: start_span,
                    },
                    "Failed to parse object entries",
                ));
            }
        };

        // Expect closing brace
        match stream.peek() {
            Some(token) if matches!(token.r#type(), TokenType::RightBrace) => {
                if let Some(close_token) = stream.next() {
                    let end_span = close_token.span().end.clone();

                    ParseResult::success(Expr::Object(ObjectExpr {
                        entries,
                        span: SymbolSpan {
                            start: start_span,
                            end: end_span,
                        },
                    }))
                } else {
                    ParseResult::error(Diagnostic::error(
                        SymbolSpan {
                            start: start_span.clone(),
                            end: start_span,
                        },
                        "Unexpected end of input, expected '}'",
                    ))
                }
            }
            Some(token) => ParseResult::error(Diagnostic::error(
                token.span().clone(),
                "Expected '}' after object entries",
            )),
            None => ParseResult::error(Diagnostic::error(
                SymbolSpan {
                    start: start_span.clone(),
                    end: start_span,
                },
                "Unexpected end of input, expected '}'",
            )),
        }
    }

    /// Fast numeric detection without regex.
    #[must_use]
    pub fn is_numeric(value: &str) -> bool {
        !value.is_empty()
            && (value.chars().all(|c| c.is_ascii_digit())
                || (value.contains('.')
                    && value.chars().all(|c| c.is_ascii_digit() || c == '.')))
    }
}

impl Parser<Expr> for ExpressionParser {
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Expr> {
        // For Prisma expressions, there are no infix operators, so we can directly parse primary expressions
        self.parse_primary(stream, options)
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        matches!(
            stream.peek_non_comment().map(Token::r#type),
            Some(
                TokenType::Literal(_)
                    | TokenType::Identifier(_)
                    | TokenType::LeftBracket
                    | TokenType::LeftBrace
                    | TokenType::LeftParen
            )
        )
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::Comma,
            TokenType::RightBrace,
            TokenType::RightParen,
            TokenType::RightBracket,
        ]
    }
}

#[cfg(test)]
mod tests {
    use crate::core::parser::components::expressions::ExpressionParser;
    use crate::core::parser::components::helpers::{
        extract_doc_text, parse_leading_docs,
    };
    use crate::core::parser::stream::VectorTokenStream;
    use crate::core::parser::traits::TokenStream;
    use crate::core::parser::{
        ast::Expr, config::ParserOptions, traits::Parser,
    };
    use crate::core::scanner::tokens::{Token, TokenType};

    fn create_test_token(token_type: TokenType) -> Token {
        Token::new(token_type, (1, 1), (1, 10))
    }

    #[test]
    fn string_literal() {
        let tokens = vec![create_test_token(TokenType::Literal(
            "\"hello\"".to_string(),
        ))];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::StringLit(lit)) = result.value {
            assert_eq!(lit.value, "hello");
        } else {
            panic!("Expected string literal");
        }
    }

    #[test]
    fn integer_literal() {
        let tokens =
            vec![create_test_token(TokenType::Literal("42".to_string()))];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::IntLit(lit)) = result.value {
            assert_eq!(lit.value, "42");
        } else {
            panic!("Expected integer literal");
        }
    }

    #[test]
    fn float_literal() {
        let tokens =
            vec![create_test_token(TokenType::Literal("3.14".to_string()))];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::FloatLit(lit)) = result.value {
            assert_eq!(lit.value, "3.14");
        } else {
            panic!("Expected float literal");
        }
    }

    #[test]
    fn boolean_literal_true() {
        let tokens =
            vec![create_test_token(TokenType::Literal("true".to_string()))];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::BoolLit(lit)) = result.value {
            assert!(lit.value);
        } else {
            panic!("Expected boolean literal");
        }
    }

    #[test]
    fn boolean_literal_false() {
        let tokens =
            vec![create_test_token(TokenType::Literal("false".to_string()))];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::BoolLit(lit)) = result.value {
            assert!(!lit.value);
        } else {
            panic!("Expected boolean literal");
        }
    }

    #[test]
    fn null_literal() {
        let tokens =
            vec![create_test_token(TokenType::Literal("null".to_string()))];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::NullLit(_)) = result.value {
            // Success
        } else {
            panic!("Expected null literal");
        }
    }

    #[test]
    fn identifier_reference() {
        let tokens = vec![create_test_token(TokenType::Identifier(
            "myVar".to_string(),
        ))];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::IdentRef(ident_ref)) = result.value {
            assert_eq!(ident_ref.name.parts.len(), 1);
            assert_eq!(ident_ref.name.parts[0].text, "myVar");
        } else {
            panic!("Expected identifier reference");
        }
    }

    #[test]
    fn function_call_no_args() {
        let tokens = vec![
            create_test_token(TokenType::Identifier("cuid".to_string())),
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::FuncCall(call)) = result.value {
            assert_eq!(call.callee.parts[0].text, "cuid");
            assert!(call.args.is_none());
        } else {
            panic!("Expected function call");
        }
    }

    #[test]
    fn function_args_missing_comma_errors() {
        let tokens = vec![
            create_test_token(TokenType::Identifier("f".into())),
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Literal("1".into())),
            // Missing comma before next arg
            create_test_token(TokenType::Literal("2".into())),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);
        assert!(!result.is_success());
    }

    #[test]
    fn array_missing_closing_bracket_errors() {
        let tokens = vec![
            create_test_token(TokenType::LeftBracket),
            create_test_token(TokenType::Literal("1".into())),
            // No closing bracket
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();
        let result = parser.parse(&mut stream, &options);
        assert!(!result.is_success());
    }

    #[test]
    fn object_missing_colon_errors() {
        let tokens = vec![
            create_test_token(TokenType::LeftBrace),
            create_test_token(TokenType::Identifier("x".into())),
            // Missing colon here
            create_test_token(TokenType::Literal("1".into())),
            create_test_token(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();
        let result = parser.parse(&mut stream, &options);
        assert!(!result.is_success());
    }

    #[test]
    fn function_call_with_args() {
        let tokens = vec![
            create_test_token(TokenType::Identifier("env".to_string())),
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Literal(
                "\"DATABASE_URL\"".to_string(),
            )),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::FuncCall(call)) = result.value {
            assert_eq!(call.callee.parts[0].text, "env");
            assert!(call.args.is_some());
            assert_eq!(call.args.unwrap().items.len(), 1);
        } else {
            panic!("Expected function call with arguments");
        }
    }

    #[test]
    fn empty_array() {
        let tokens = vec![
            create_test_token(TokenType::LeftBracket),
            create_test_token(TokenType::RightBracket),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::Array(array)) = result.value {
            assert_eq!(array.elements.len(), 0);
        } else {
            panic!("Expected array expression");
        }
    }

    #[test]
    fn array_with_elements() {
        let tokens = vec![
            create_test_token(TokenType::LeftBracket),
            create_test_token(TokenType::Literal("1".to_string())),
            create_test_token(TokenType::Comma),
            create_test_token(TokenType::Literal("2".to_string())),
            create_test_token(TokenType::RightBracket),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::Array(array)) = result.value {
            assert_eq!(array.elements.len(), 2);
        } else {
            panic!("Expected array expression");
        }
    }

    #[test]
    fn empty_object() {
        let tokens = vec![
            create_test_token(TokenType::LeftBrace),
            create_test_token(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::Object(obj)) = result.value {
            assert_eq!(obj.entries.len(), 0);
        } else {
            panic!("Expected object expression");
        }
    }

    #[test]
    fn object_with_entries() {
        let tokens = vec![
            create_test_token(TokenType::LeftBrace),
            create_test_token(TokenType::Identifier("key".to_string())),
            create_test_token(TokenType::Colon),
            create_test_token(TokenType::Literal("\"value\"".to_string())),
            create_test_token(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::Object(obj)) = result.value {
            assert_eq!(obj.entries.len(), 1);
        } else {
            panic!("Expected object expression");
        }
    }

    #[test]
    fn can_parse() {
        let parser = ExpressionParser::new();

        // Test valid expression tokens
        let valid_tokens = [
            TokenType::Literal("test".to_string()),
            TokenType::Literal("42".to_string()),
            TokenType::Literal("true".to_string()),
            TokenType::Literal("null".to_string()),
            TokenType::Identifier("test".to_string()),
            TokenType::LeftBracket,
            TokenType::LeftBrace,
            TokenType::LeftParen,
        ];

        for token_type in valid_tokens {
            let tokens = vec![create_test_token(token_type)];
            let stream = VectorTokenStream::new(tokens);
            assert!(parser.can_parse(&stream));
        }

        // Test invalid expression tokens
        let tokens = vec![create_test_token(TokenType::Model)];
        let stream = VectorTokenStream::new(tokens);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn can_parse_with_comments() {
        let parser = ExpressionParser::new();

        // Test with leading comments
        let tokens = vec![
            create_test_token(TokenType::Comment("// comment".to_string())),
            create_test_token(TokenType::DocComment(
                "/// doc comment".to_string(),
            )),
            create_test_token(TokenType::Literal("42".to_string())),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));

        // Test with comments but wrong token
        let tokens = vec![
            create_test_token(TokenType::Comment("// comment".to_string())),
            create_test_token(TokenType::Model),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn parenthesized_expression() {
        let tokens = vec![
            create_test_token(TokenType::LeftParen),
            create_test_token(TokenType::Literal("42".to_string())),
            create_test_token(TokenType::RightParen),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let mut parser = ExpressionParser::new();
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.is_success());
        if let Some(Expr::IntLit(lit)) = result.value {
            assert_eq!(lit.value, "42");
        } else {
            panic!("Expected integer literal from parenthesized expression");
        }
    }

    #[test]
    fn is_numeric() {
        assert!(ExpressionParser::is_numeric("42"));
        assert!(ExpressionParser::is_numeric("3.14"));
        assert!(ExpressionParser::is_numeric("0"));
        assert!(!ExpressionParser::is_numeric("hello"));
        assert!(!ExpressionParser::is_numeric(""));
        assert!(!ExpressionParser::is_numeric("42a"));
    }

    /// Helper to create a `DocComment` token.
    fn doc_comment_token(
        text: &str,
        line: u32,
        start_col: u32,
        end_col: u32,
    ) -> Token {
        Token::new(
            TokenType::DocComment(text.to_string()),
            (line, start_col),
            (line, end_col),
        )
    }

    /// Helper to create an identifier token.
    fn ident_token(
        name: &str,
        line: u32,
        start_col: u32,
        end_col: u32,
    ) -> Token {
        Token::new(
            TokenType::Identifier(name.to_string()),
            (line, start_col),
            (line, end_col),
        )
    }

    /// Helper to create a model token.
    fn model_token(line: u32, start_col: u32, end_col: u32) -> Token {
        Token::new(TokenType::Model, (line, start_col), (line, end_col))
    }

    #[test]
    fn parse_leading_docs_no_docs() {
        let tokens = vec![ident_token("User", 1, 1, 5)];
        let mut stream = VectorTokenStream::new(tokens);

        let result = parse_leading_docs(&mut stream);

        assert!(result.is_none());
        // Stream should be unchanged
        assert!(stream.peek().is_some());
        assert!(matches!(
            stream.peek().unwrap().r#type(),
            TokenType::Identifier(_)
        ));
    }

    #[test]
    fn parse_leading_docs_single_doc() {
        let tokens = vec![
            doc_comment_token(" User model for authentication", 1, 1, 30),
            ident_token("User", 2, 1, 5),
        ];
        let mut stream = VectorTokenStream::new(tokens);

        let result = parse_leading_docs(&mut stream);

        assert!(result.is_some());
        let docs = result.unwrap();
        assert_eq!(docs.lines.len(), 1);
        assert_eq!(docs.lines[0], "User model for authentication");

        // Stream should now be at the identifier
        assert!(stream.peek().is_some());
        assert!(matches!(
            stream.peek().unwrap().r#type(),
            TokenType::Identifier(_)
        ));
    }

    #[test]
    fn parse_leading_docs_multiple_docs() {
        let tokens = vec![
            doc_comment_token(" User model", 1, 1, 12),
            doc_comment_token(" Used for authentication", 2, 1, 25),
            doc_comment_token(" and authorization", 3, 1, 19),
            model_token(4, 1, 6),
            ident_token("User", 4, 7, 11),
        ];
        let mut stream = VectorTokenStream::new(tokens);

        let result = parse_leading_docs(&mut stream);

        assert!(result.is_some());
        let docs = result.unwrap();
        assert_eq!(docs.lines.len(), 3);
        assert_eq!(docs.lines[0], "User model");
        assert_eq!(docs.lines[1], "Used for authentication");
        assert_eq!(docs.lines[2], "and authorization");

        // Stream should now be at the model keyword
        assert!(stream.peek().is_some());
        assert!(matches!(stream.peek().unwrap().r#type(), TokenType::Model));
    }

    #[test]
    fn parse_leading_docs_empty_stream() {
        let tokens = vec![];
        let mut stream = VectorTokenStream::new(tokens);

        let result = parse_leading_docs(&mut stream);

        assert!(result.is_none());
        assert!(stream.peek().is_none());
    }

    #[test]
    fn parse_leading_docs_stops_at_other_tokens() {
        let tokens = vec![
            doc_comment_token(" First doc", 1, 1, 11),
            doc_comment_token(" Second doc", 2, 1, 12),
            ident_token("User", 3, 1, 5), // Should stop here
            doc_comment_token(" Third doc", 4, 1, 11), // This should not be consumed
        ];
        let mut stream = VectorTokenStream::new(tokens);

        let result = parse_leading_docs(&mut stream);

        assert!(result.is_some());
        let docs = result.unwrap();
        assert_eq!(docs.lines.len(), 2);
        assert_eq!(docs.lines[0], "First doc");
        assert_eq!(docs.lines[1], "Second doc");

        // Stream should be at the identifier, not the third doc comment
        assert!(stream.peek().is_some());
        assert!(matches!(
            stream.peek().unwrap().r#type(),
            TokenType::Identifier(_)
        ));

        // Advance past identifier and verify the third doc comment is still there
        let _ = stream.next();
        assert!(stream.peek().is_some());
        assert!(matches!(
            stream.peek().unwrap().r#type(),
            TokenType::DocComment(_)
        ));
    }

    #[test]
    fn parse_leading_docs_span_calculation() {
        let tokens = vec![
            doc_comment_token(" First line", 1, 5, 16),
            doc_comment_token(" Second line", 2, 3, 15),
            doc_comment_token(" Third line", 3, 1, 12),
            ident_token("User", 4, 1, 5),
        ];
        let mut stream = VectorTokenStream::new(tokens);

        let result = parse_leading_docs(&mut stream);

        assert!(result.is_some());
        let docs = result.unwrap();

        // Span should start from the first token and end at the last token
        assert_eq!(docs.span.start.line, 1);
        assert_eq!(docs.span.start.column, 5);
        assert_eq!(docs.span.end.line, 3);
        assert_eq!(docs.span.end.column, 12);

        // Content should be correctly extracted
        assert_eq!(docs.lines.len(), 3);
        assert_eq!(docs.lines[0], "First line");
        assert_eq!(docs.lines[1], "Second line");
        assert_eq!(docs.lines[2], "Third line");
    }

    #[test]
    fn parse_leading_docs_with_empty_doc_comments() {
        let tokens = vec![
            doc_comment_token("", 1, 1, 4), // Empty doc comment
            doc_comment_token(" Content", 2, 1, 8),
            doc_comment_token("", 3, 1, 4), // Another empty one
            ident_token("User", 4, 1, 5),
        ];
        let mut stream = VectorTokenStream::new(tokens);

        let result = parse_leading_docs(&mut stream);

        assert!(result.is_some());
        let docs = result.unwrap();
        assert_eq!(docs.lines.len(), 3);
        assert_eq!(docs.lines[0], ""); // Empty line
        assert_eq!(docs.lines[1], "Content");
        assert_eq!(docs.lines[2], ""); // Another empty line
    }

    #[test]
    fn parse_leading_docs_with_whitespace_only() {
        let tokens = vec![
            doc_comment_token("   ", 1, 1, 6), // Whitespace only
            doc_comment_token(" Real content", 2, 1, 14),
            doc_comment_token("     ", 3, 1, 8), // More whitespace
            ident_token("User", 4, 1, 5),
        ];
        let mut stream = VectorTokenStream::new(tokens);

        let result = parse_leading_docs(&mut stream);

        assert!(result.is_some());
        let docs = result.unwrap();
        assert_eq!(docs.lines.len(), 3);
        // Only a single leading space is removed; remaining spaces preserved
        assert_eq!(docs.lines[0], "  ");
        assert_eq!(docs.lines[1], "Real content");
        assert_eq!(docs.lines[2], "    ");
    }

    #[test]
    fn parse_leading_docs_realistic_example() {
        let tokens = vec![
            doc_comment_token(
                " The User model represents application users.",
                1,
                1,
                46,
            ),
            doc_comment_token("", 2, 1, 4),
            doc_comment_token(
                " This model contains authentication and profile",
                3,
                1,
                48,
            ),
            doc_comment_token(
                " information for each user in the system.",
                4,
                1,
                42,
            ),
            model_token(5, 1, 6),
            ident_token("User", 5, 7, 11),
        ];
        let mut stream = VectorTokenStream::new(tokens);

        let result = parse_leading_docs(&mut stream);

        assert!(result.is_some());
        let docs = result.unwrap();
        assert_eq!(docs.lines.len(), 4);
        assert_eq!(
            docs.lines[0],
            "The User model represents application users."
        );
        assert_eq!(docs.lines[1], "");
        assert_eq!(
            docs.lines[2],
            "This model contains authentication and profile"
        );
        assert_eq!(docs.lines[3], "information for each user in the system.");

        // Verify span encompasses all doc comments
        assert_eq!(docs.span.start.line, 1);
        assert_eq!(docs.span.start.column, 1);
        assert_eq!(docs.span.end.line, 4);
        assert_eq!(docs.span.end.column, 42);

        // Stream should be positioned at model keyword
        assert!(stream.peek().is_some());
        assert!(matches!(stream.peek().unwrap().r#type(), TokenType::Model));
    }

    #[test]
    fn extract_doc_text_with_prefix() {
        let token = Token::new(
            TokenType::DocComment(" This is documentation".to_string()),
            (1, 1),
            (1, 25),
        );

        let result = extract_doc_text(&token);
        assert_eq!(result, Some("This is documentation".to_string()));
    }

    #[test]
    fn extract_doc_text_without_prefix() {
        let token = Token::new(
            TokenType::DocComment("This is documentation".to_string()),
            (1, 1),
            (1, 21),
        );

        let result = extract_doc_text(&token);
        assert_eq!(result, Some("This is documentation".to_string()));
    }

    #[test]
    fn extract_doc_text_with_extra_whitespace() {
        let token = Token::new(
            TokenType::DocComment("   This has extra spaces   ".to_string()),
            (1, 1),
            (1, 31),
        );

        let result = extract_doc_text(&token);
        // Only a single leading space is removed; preserve the rest
        assert_eq!(result, Some("  This has extra spaces   ".to_string()));
    }

    #[test]
    fn extract_doc_text_non_doc_comment() {
        let token = Token::new(
            TokenType::Identifier("not_a_doc".to_string()),
            (1, 1),
            (1, 10),
        );

        let result = extract_doc_text(&token);
        assert!(result.is_none());
    }

    #[test]
    fn docs_span_calculation() {
        let tokens = vec![
            Token::new(
                TokenType::DocComment(" First".to_string()),
                (1, 1),
                (1, 10),
            ),
            Token::new(
                TokenType::DocComment(" Second".to_string()),
                (2, 1),
                (2, 11),
            ),
            Token::new(
                TokenType::DocComment(" Third".to_string()),
                (3, 1),
                (3, 10),
            ),
        ];
        let mut stream = VectorTokenStream::new(tokens);

        let result = parse_leading_docs(&mut stream);

        assert!(result.is_some());
        let docs = result.unwrap();

        // Span should start from the first token and end at the last token
        assert_eq!(docs.span.start.line, 1);
        assert_eq!(docs.span.start.column, 1);
        assert_eq!(docs.span.end.line, 3);
        assert_eq!(docs.span.end.column, 10);
    }
}
