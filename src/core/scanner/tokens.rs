//! Define token kinds and spans produced by the lexer.
//!
//! These types capture what the scanner recognized and where it occurred.
//! `TokenType` names the kind, `SymbolLocation` and `SymbolSpan` mark the
//! position, and `Token` pairs the two for downstream consumers.
//!
//! Line and column are 1-based in the lexer’s coordinate space. Treat spans
//! as opaque bounds; only ordering is guaranteed.
//!
//! ## Examples
//! ```
//! # use prisma_rs::core::scanner::*;
//! let tok = Token::new(TokenType::Model, (1, 1), (1, 6));
//! assert!(matches!(tok.r#type(), TokenType::Model));
//! assert_eq!(tok.span().start.line, 1);
//! ```

use std::fmt::Display;

use compiler_macros::EnumKindName;

/// Describe what the lexer recognized at a span.
///
/// Variants with `String` retain source text for that token. String literal
/// content is stored without surrounding quotes.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::scanner::TokenType;
/// let kw = TokenType::Model;
/// let ident = TokenType::Identifier("User".to_string());
/// let lit = TokenType::Literal("42".to_string());
/// ```
#[derive(Debug, PartialEq, Clone, EnumKindName)]
pub enum TokenType {
    // Keywords
    /// The `generator` keyword.
    Generator,
    /// The `datasource` keyword.
    DataSource,
    /// The `model` keyword.
    Model,
    /// The `enum` keyword.
    Enum,
    /// The `type` keyword.
    Type,

    // Types
    /// The `String` type keyword.
    String,
    /// The `Int` type keyword.
    Int,
    /// The `Float` type keyword.
    Float,
    /// The `Boolean` type keyword.
    Boolean,
    /// The `DateTime` type keyword.
    DateTime,
    /// The `Json` type keyword.
    Json,
    /// The `Bytes` type keyword.
    Bytes,
    /// The `Decimal` type keyword.
    Decimal,

    // Literals
    /// A literal value with its source text.
    Literal(String),
    /// An identifier with its source text.
    Identifier(String),

    // Operators
    /// The assignment operator.
    Assign,
    /// The optional marker.
    Optional,
    /// The list-type marker.
    List,
    /// The dot operator.
    Dot,

    // Punctuation
    /// The left brace `{`.
    LeftBrace,
    /// The right brace `}`.
    RightBrace,
    /// The left bracket `[`.
    LeftBracket,
    /// The right bracket `]`.
    RightBracket,
    /// The left parenthesis `(`.
    LeftParen,
    /// The right parenthesis `)`.
    RightParen,
    /// The comma `,`.
    Comma,
    /// The colon `:`.
    Colon,
    /// The at sign `@`.
    At,
    /// The double at sign `@@`.
    DoubleAt,

    // Comments
    /// A comment with its text content.
    Comment(String),
    /// A documentation comment with its text content.
    DocComment(String),

    // Unsupported
    /// A token that is not recognized by the set of tokens
    Unsupported(String),

    // End of File
    /// End-of-input marker emitted after the final token.
    EOF,
}

impl Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Using #[expect(clippy::enum_glob_use)] is not allowed
        // with forbid(pendantic)
        use TokenType::{
            Assign, At, Boolean, Bytes, Colon, Comma, Comment, DataSource,
            DateTime, Decimal, DocComment, Dot, DoubleAt, EOF, Enum, Float,
            Generator, Identifier, Int, Json, LeftBrace, LeftBracket,
            LeftParen, List, Literal, Model, Optional, RightBrace,
            RightBracket, RightParen, Type, Unsupported,
        };

        match &self {
            Assign => f.write_str("Assign ( `=` )"),
            At => f.write_str("At ( `@` )"),
            Boolean => f.write_str("Boolean ( `Boolean` )"),
            Bytes => f.write_str("Bytes ( `Bytes` )"),
            Colon => f.write_str("Colon ( `:` )"),
            Comma => f.write_str("Comma ( `,` )"),
            Comment(data) => {
                let _ = f.write_str("Comment ( `//` ) {\n");
                let _ = f.write_str(data);
                f.write_str("\n}")
            }
            DataSource => f.write_str("DataSource ( `datasource` )"),
            DateTime => f.write_str("DateTime ( `DateTime` )"),
            Decimal => f.write_str("Decimal ( `Decimal` )"),
            DocComment(data) => {
                let _ = f.write_str("DocComment ( `///` ) {\n");
                let _ = f.write_str(data);
                f.write_str("\n}")
            }
            Dot => f.write_str("Dot ( `.` )"),
            DoubleAt => f.write_str("DoubleAt ( `@@` )"),
            Enum => f.write_str("Enum ( `enum` )"),
            EOF => f.write_str("EOF ( end-of-file )"),
            Float => f.write_str("Float ( `Float` )"),
            Generator => f.write_str("Generator ( `generator` )"),
            Identifier(data) => {
                let _ = f.write_str("Identifier( `");
                let _ = f.write_str(data);
                f.write_str("` )")
            }
            Int => f.write_str("Int ( `Int` )"),
            Json => f.write_str("Json ( `Json` )"),
            LeftBrace => f.write_str("LeftBrace ( `{` )"),
            LeftBracket => f.write_str("LeftBracket ( `[` )"),
            LeftParen => f.write_str("LeftParen ( `(` )"),
            List => f.write_str("List ( `[]` )"),
            Literal(data) => {
                let _ = f.write_str("Literal (` ");
                let _ = f.write_str(data);
                f.write_str("` )")
            }
            Model => f.write_str("Model ( `model` )"),
            Optional => f.write_str("Optional ( `?` )"),
            RightBrace => f.write_str("RightBrace ( `}` )"),
            RightBracket => f.write_str("RightBracket ( `]` )"),
            RightParen => f.write_str("RightParen ( `)` )"),
            // lol somehow the qualified name maintains the sorted order :)
            TokenType::String => f.write_str("String ( `String` )"),
            Type => f.write_str("Type ( `type` )"),
            Unsupported(data) => {
                let _ = f.write_str("Unsupported ( `");
                let _ = f.write_str(data);
                f.write_str("` )")
            }
        }
    }
}

/// Record a single position in the source text.
///
/// Uses 1-based `line` and `column` in the lexer’s coordinate space.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::scanner::SymbolLocation;
/// let loc = SymbolLocation { line: 2, column: 5 };
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct SymbolLocation {
    /// Line number of the position.
    pub line: u32,
    /// Column number of the position.
    pub column: u32,
}

impl From<&SymbolLocation> for (u32, u32) {
    fn from(value: &SymbolLocation) -> Self {
        (value.line, value.column)
    }
}

/// Record a half-open range covered by a token.
///
/// Combine a start and end location. Only ordering is guaranteed.
///
/// ## Examples
///
/// ```
/// # use prisma_rs::core::scanner::{SymbolLocation, SymbolSpan};
/// let span = SymbolSpan {
///     start: SymbolLocation { line: 1, column: 1 },
///     end: SymbolLocation { line: 1, column: 4 },
/// };
/// assert!(span.start.column < span.end.column);
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct SymbolSpan {
    /// The start location of the span.
    pub start: SymbolLocation,
    /// The end location of the span.
    pub end: SymbolLocation,
}

/// Pair a token kind with the span it covers.
///
/// Consumers rely on the stored span for diagnostics and error messages.
///
/// ## Examples
///
/// ```
/// # use prisma_rs::core::scanner::*;
/// let t = Token::new(TokenType::Identifier("id".into()), (1, 1), (1, 3));
/// assert!(matches!(t.r#type(), TokenType::Identifier(_)));
/// ```
#[derive(Debug, Clone)]
pub struct Token {
    r#type: TokenType,
    span: SymbolSpan,
}

impl Token {
    /// Create a token from a kind and start/end coordinates.
    ///
    /// Provide 1-based `(line, column)` pairs for `start` and `end`. The
    /// function assembles a `SymbolSpan` accordingly and stores it with the
    /// token kind.
    ///
    /// ## Panics
    /// Panics if `start` follows `end` in line or column ordering.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::scanner::*;
    /// let t = Token::new(TokenType::At, (1, 2), (1, 3));
    /// assert!(matches!(t.r#type(), TokenType::At));
    /// assert_eq!(t.span().start.column, 2);
    /// ```
    #[must_use]
    pub fn new(r#type: TokenType, start: (u32, u32), end: (u32, u32)) -> Self {
        assert!(
            start.0 < end.0 || (start.0 == end.0 && start.1 <= end.1),
            "span should be monotonically increasing"
        );
        Self {
            r#type,
            span: SymbolSpan {
                start: SymbolLocation {
                    line: start.0,
                    column: start.1,
                },
                end: SymbolLocation {
                    line: end.0,
                    column: end.1,
                },
            },
        }
    }

    /// Return the token kind.
    #[must_use]
    pub fn r#type(&self) -> &TokenType {
        &self.r#type
    }

    /// Return the span covered by the token.
    #[must_use]
    pub fn span(&self) -> &SymbolSpan {
        &self.span
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.r#type.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn token_type_name_unit_variants() {
        assert_eq!(TokenType::Int.name(), "Int");
        assert_eq!(TokenType::String.name(), "String");
        assert_eq!(TokenType::List.name(), "List");
        assert_eq!(TokenType::DoubleAt.name(), "DoubleAt");
    }

    #[test]
    fn token_type_name_tuple_variants() {
        assert_eq!(TokenType::Identifier("x".into()).name(), "Identifier");
        assert_eq!(TokenType::Literal("42".into()).name(), "Literal");
        assert_eq!(TokenType::Comment(" note".into()).name(), "Comment");
        assert_eq!(TokenType::Unsupported("?".into()).name(), "Unsupported");
    }

    #[test]
    fn token_type_display_formats_variants() {
        let variants = vec![
            TokenType::Assign,
            TokenType::At,
            TokenType::Boolean,
            TokenType::Bytes,
            TokenType::Colon,
            TokenType::Comma,
            TokenType::DataSource,
            TokenType::DateTime,
            TokenType::Decimal,
            TokenType::Dot,
            TokenType::DoubleAt,
            TokenType::Enum,
            TokenType::EOF,
            TokenType::Float,
            TokenType::Generator,
            TokenType::Identifier("User".into()),
            TokenType::Int,
            TokenType::Json,
            TokenType::LeftBrace,
            TokenType::LeftBracket,
            TokenType::LeftParen,
            TokenType::List,
            TokenType::Literal("42".into()),
            TokenType::Model,
            TokenType::Optional,
            TokenType::RightBrace,
            TokenType::RightBracket,
            TokenType::RightParen,
            TokenType::String,
            TokenType::Type,
            TokenType::Comment(" inline".into()),
            TokenType::DocComment(" doc".into()),
            TokenType::Unsupported("?".into()),
        ];

        let out = variants.into_iter().fold(String::new(), |mut acc, v| {
            acc.push_str(&v.to_string());
            acc
        });

        assert!(out.contains("Assign"));
        assert!(out.contains("DoubleAt"));
        assert!(out.contains("Identifier"));
        assert!(out.contains("Literal"));
        assert!(out.contains("Comment"));
        assert!(out.contains("DocComment"));
        assert!(out.contains("Unsupported"));
        assert!(out.contains("String ( `String` )"));
    }

    #[test]
    fn token_display_delegates_to_token_type() {
        let tok = Token::new(TokenType::At, (1, 2), (1, 3));
        let s = format!("{tok}");
        assert!(s.contains("At"));
    }

    #[test]
    #[should_panic(expected = "monotonically increasing")]
    fn token_new_panics_on_inverted_span() {
        // end before start should panic
        let _ = Token::new(TokenType::At, (2, 1), (1, 1));
    }

    #[test]
    fn symbol_location_from_reference_conversion() {
        // Test the new From<&SymbolLocation> for (u32, u32) implementation
        let location = SymbolLocation {
            line: 5,
            column: 10,
        };
        let tuple: (u32, u32) = (&location).into();
        assert_eq!(tuple, (5, 10));

        // Test with zero values
        let location_zero = SymbolLocation { line: 0, column: 0 };
        let tuple_zero: (u32, u32) = (&location_zero).into();
        assert_eq!(tuple_zero, (0, 0));

        // Test with maximum values
        let location_max = SymbolLocation {
            line: u32::MAX,
            column: u32::MAX,
        };
        let tuple_max: (u32, u32) = (&location_max).into();
        assert_eq!(tuple_max, (u32::MAX, u32::MAX));
    }

    #[test]
    fn token_new_lexicographic_span_ordering() {
        // Test the updated span monotonicity check with lexicographic ordering

        // Same line: start.column <= end.column should work
        let start = SymbolLocation { line: 1, column: 5 };
        let end = SymbolLocation {
            line: 1,
            column: 10,
        };
        let token = Token::new(
            TokenType::Identifier("test".to_string()),
            (start.line, start.column),
            (end.line, end.column),
        );
        assert_eq!(token.span().start, start);
        assert_eq!(token.span().end, end);
    }

    #[test]
    fn token_new_lexicographic_span_same_position() {
        // Same line, same column should be valid
        let location = SymbolLocation { line: 1, column: 5 };
        let token = Token::new(
            TokenType::Identifier("x".to_string()),
            (location.line, location.column),
            (location.line, location.column),
        );
        assert_eq!(token.span().start, location);
        assert_eq!(token.span().end, location);
    }

    #[test]
    fn token_new_lexicographic_span_different_lines() {
        // Different lines: start.line < end.line should work regardless of columns
        let start = SymbolLocation {
            line: 1,
            column: 20,
        };
        let end = SymbolLocation { line: 2, column: 5 };
        let token = Token::new(
            TokenType::Literal("multiline".to_string()),
            (start.line, start.column),
            (end.line, end.column),
        );
        assert_eq!(token.span().start, start);
        assert_eq!(token.span().end, end);
    }

    #[test]
    #[should_panic(expected = "span should be monotonically increasing")]
    fn token_new_lexicographic_span_invalid_same_line() {
        // Same line but end column before start column should panic
        let start = SymbolLocation {
            line: 1,
            column: 10,
        };
        let end = SymbolLocation { line: 1, column: 5 };
        let _ = Token::new(
            TokenType::Identifier("invalid".to_string()),
            (start.line, start.column),
            (end.line, end.column),
        );
    }

    #[test]
    #[should_panic(expected = "span should be monotonically increasing")]
    fn token_new_lexicographic_span_invalid_reverse_lines() {
        // End line before start line should panic
        let start = SymbolLocation { line: 2, column: 5 };
        let end = SymbolLocation {
            line: 1,
            column: 10,
        };
        let _ = Token::new(
            TokenType::Identifier("invalid".to_string()),
            (start.line, start.column),
            (end.line, end.column),
        );
    }
}
