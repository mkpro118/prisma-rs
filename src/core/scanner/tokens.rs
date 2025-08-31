//! Lexical token definitions for a Prisma-like schema scanner.
//!
//! This module declares token kinds, source coordinates, spans, and the `Token`
//! container emitted by the lexer.
//!
//! # Model
//! - `TokenType` enumerates the discrete kinds recognized by the scanner.
//!   Variants carrying `String` retain the associated source text.
//! - `SymbolLocation` records a single position as `(line, column)`.
//! - `SymbolSpan` records a contiguous region `[start, end]` in the scanner's
//!   coordinate system.
//! - `Token` pairs a `TokenType` with a `SymbolSpan`.
//!
//! # Coordinates and spans
//! Line and column units are implementation-defined and measured in the
//! lexer's coordinate system. No guarantee is made about the inclusivity of
//! the `end` bound; consumers should treat spans as opaque bounds reported by
//! the lexer. The only invariant is that `start` does not follow `end` in the
//! lexer's ordering.
//!
//! # Text payloads
//! For variants that carry `String`, delimiter retention (for example, whether
//! quotes or comment markers are included) is an implementation detail of the
//! lexer and may vary across modes or inputs.

/// Lexical token kinds recognized by the scanner.
///
/// Each variant represents a distinct syntactic unit emitted by the lexer.
/// Variants carrying `String` store the source text associated with the token.
#[derive(Debug, PartialEq, Clone)]
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

/// A position in the source text.
///
/// Positions are expressed as line and column numbers measured in the lexer's
/// coordinate system.
#[derive(Debug, Clone)]
pub struct SymbolLocation {
    /// Line number of the position.
    pub line: u32,
    /// Column number of the position.
    pub column: u32,
}

/// A contiguous range in the source text.
///
/// The span is bounded by a start and end location as recorded by the lexer.
#[derive(Debug, Clone)]
pub struct SymbolSpan {
    /// The start location of the span.
    pub start: SymbolLocation,
    /// The end location of the span.
    pub end: SymbolLocation,
}

/// A lexical token with its kind and source span.
#[derive(Debug, Clone)]
pub struct Token {
    r#type: TokenType,
    span: SymbolSpan,
}

impl Token {
    /// Constructs a new `Token` from a kind and start/end coordinates.
    ///
    /// # Parameters
    ///
    /// * `r#type` — The token kind.
    /// * `start` — The `(line, column)` of the token start.
    /// * `end` — The `(line, column)` of the token end.
    ///
    /// # Panics
    ///
    /// Panics if `start` does not precede or equal `end` component-wise.
    /// Specifically, this panics when `start.0 > end.0` or `start.1 > end.1`.
    #[must_use]
    pub fn new(r#type: TokenType, start: (u32, u32), end: (u32, u32)) -> Self {
        assert!(start.0 <= end.0 && start.1 <= end.1);
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

    /// Returns the token kind.
    #[must_use]
    pub fn r#type(&self) -> &TokenType {
        &self.r#type
    }

    /// Returns the span covered by the token.
    #[must_use]
    pub fn span(&self) -> &SymbolSpan {
        &self.span
    }
}
