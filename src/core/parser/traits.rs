//! Core parser traits and interfaces.
//!
//! The parser is a set of narrow, composable traits designed for building
//! custom parsing pipelines. A `TokenStream` feeds tokens sourced from the
//! scanner. Concrete parsers implement `Parser<T>` (and optionally
//! `SchemaParser`, `ItemParser`, or `ExpressionParser`) to transform tokens
//! into AST nodes while producing diagnostics. Error handling flows through
//! `ParseResult` and `Diagnostic`; synchronization points can be advertised
//! for recovery.
//!
//! Spans and positions originate in the scanner and must be preserved.
//! When making decisions, treat comments/doc-comments as skippable unless
//! the grammar requires them. Parsers should be single-responsibility and
//! predictable: either recognize a construct at the current position or
//! leave the stream unchanged so another parser can try. Use
//! checkpoint/restore on the `TokenStream` to probe ahead without
//! committing.
//!
//! ## Examples
//! Minimal `TokenStream` and a tiny parser that recognizes a leading
//! `model` keyword.
//! ```
//! # use prisma_rs::core::parser::traits::{TokenStream, Parser};
//! # use prisma_rs::core::parser::config::{ParserOptions, ParseResult, Diagnostic};
//! # use prisma_rs::core::scanner::tokens::{Token, TokenType, SymbolLocation, SymbolSpan};
//! #[derive(Debug)]
//! struct VecStream { toks: Vec<Token>, i: usize }
//! impl VecStream { fn new(t: Vec<Token>) -> Self { Self { toks: t, i: 0 } } }
//! impl TokenStream for VecStream {
//!     fn peek(&self) -> Option<&Token> { self.toks.get(self.i) }
//!     fn peek_ahead(&self, o: usize) -> Option<&Token> { self.toks.get(self.i + o) }
//!     fn next(&mut self) -> Option<Token> { let t = self.toks.get(self.i).cloned()?; self.i += 1; Some(t) }
//!     fn is_at_end(&self) -> bool { matches!(self.peek().map(|t| t.r#type()), Some(TokenType::EOF)) }
//!     fn position(&self) -> usize { self.i }
//!     fn checkpoint(&self) -> usize { self.i }
//!     fn restore(&mut self, c: usize) { self.i = c; }
//! }
//!
//! struct ModelKeywordParser;
//! impl Parser<()> for ModelKeywordParser {
//!     fn parse(&mut self, stream: &mut dyn TokenStream, _: &ParserOptions) -> ParseResult<()> {
//!         if let Some(tok) = stream.peek() {
//!             if matches!(tok.r#type(), TokenType::Model) { let _ = stream.next(); return ParseResult::success(()); }
//!             return ParseResult::error(Diagnostic::error(tok.span().clone(), "expected 'model'"));
//!         }
//!         let span = SymbolSpan { start: SymbolLocation{ line: 1, column: 1 }, end: SymbolLocation{ line: 1, column: 1 } };
//!         ParseResult::error(Diagnostic::error(span, "unexpected eof"))
//!     }
//!     fn can_parse(&self, stream: &dyn TokenStream) -> bool {
//!         matches!(stream.peek().map(|t| t.r#type()), Some(TokenType::Model))
//!     }
//! }
//!
//! # let span = |s:(u32,u32),e:(u32,u32)| SymbolSpan{ start: SymbolLocation{ line: s.0, column: s.1 }, end: SymbolLocation{ line: e.0, column: e.1 } };
//! let toks = vec![ Token::new(TokenType::Model, (1,1), (1,6)), Token::new(TokenType::EOF, (1,7), (1,7)) ];
//! let mut stream = VecStream::new(toks);
//! let mut parser = ModelKeywordParser;
//! let result = parser.parse(&mut stream, &ParserOptions::default());
//! assert!(result.is_success());
//! ```

use crate::core::parser::ast::{Declaration, Schema};
use crate::core::parser::config::{Diagnostic, ParseResult, ParserOptions};
use crate::core::scanner::tokens::{Token, TokenType};

/// Read tokens for parser input.
///
/// A `TokenStream` supplies the parser with lookahead and consumption
/// operations while tracking a logical position for diagnostics. The
/// interface supports checkpoint/restore so parsers can probe ahead and
/// backtrack without committing to a parse.
///
/// `peek()` inspects the current token; `peek_ahead(n)` inspects future
/// tokens without changing the stream. `next()` consumes one token.
/// `checkpoint()` returns a position token that can later be passed to
/// `restore()` to rewind the stream. `position()` returns an opaque index
/// suitable for error messages.
///
/// Parsers generally avoid consuming input unless they will succeed, or they
/// establish a checkpoint before attempting a speculative parse.
///
/// ## Examples
/// Peek, checkpoint, parse, and restore on failure.
/// ```
/// # use prisma_rs::core::parser::traits::TokenStream;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType, SymbolLocation, SymbolSpan};
/// #[derive(Debug)]
/// struct S { t: Vec<Token>, i: usize }
/// impl S { fn new(t: Vec<Token>) -> Self { Self { t, i: 0 } } }
/// impl TokenStream for S {
///     fn peek(&self) -> Option<&Token> { self.t.get(self.i) }
///     fn peek_ahead(&self, o: usize) -> Option<&Token> { self.t.get(self.i+o) }
///     fn next(&mut self) -> Option<Token> { let tok = self.t.get(self.i).cloned()?; self.i+=1; Some(tok) }
///     fn is_at_end(&self) -> bool { matches!(self.peek().map(|t| t.r#type()), Some(TokenType::EOF)) }
///     fn position(&self) -> usize { self.i }
///     fn checkpoint(&self) -> usize { self.i }
///     fn restore(&mut self, c: usize) { self.i = c; }
/// }
/// # let span = |s:(u32,u32),e:(u32,u32)| SymbolSpan{start:SymbolLocation{line:s.0,column:s.1},end:SymbolLocation{line:e.0,column:e.1}};
/// let mut s = S::new(vec![Token::new(TokenType::Model,(1,1),(1,6)), Token::new(TokenType::EOF,(1,7),(1,7))]);
/// let cp = s.checkpoint();
/// if matches!(s.peek().map(|t| t.r#type()), Some(TokenType::Model)) { let _ = s.next(); } else { s.restore(cp); }
/// assert!(s.is_at_end());
/// ```
pub trait TokenStream {
    /// Peek at the current token without consuming it.
    fn peek(&self) -> Option<&Token>;

    /// Peek ahead at the token at the given offset (0 = current, 1 = next, etc.).
    fn peek_ahead(&self, offset: usize) -> Option<&Token>;

    /// Consume and return the current token.
    fn next(&mut self) -> Option<Token>;

    /// Check if the stream is at end-of-input.
    fn is_at_end(&self) -> bool;

    /// Get the current position in the stream for error reporting.
    fn position(&self) -> usize;

    /// Create a checkpoint that can be restored later.
    fn checkpoint(&self) -> usize;

    /// Restore the stream to a previous checkpoint.
    fn restore(&mut self, checkpoint: usize);
}

/// Parse a language construct from tokens.
///
/// A parser recognizes whether it can start at the current position and
/// then consumes tokens to produce a value and diagnostics. Implementations
/// should be single-responsibility (e.g., “parse a model block”), avoid
/// consuming tokens unless they will succeed, and prefer creating a
/// `TokenStream` checkpoint before speculative parsing.
///
/// `can_parse` should be fast and conservative. It should return true only
/// when the construct very likely starts at the current position. If unsure,
/// return false and let another parser try.
///
/// ## Examples
/// Speculative parse guarded by `can_parse` and a checkpoint.
/// ```
/// # use prisma_rs::core::parser::traits::{TokenStream, Parser};
/// # use prisma_rs::core::parser::config::{ParserOptions, ParseResult, Diagnostic};
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType, SymbolLocation, SymbolSpan};
/// #[derive(Debug)]
/// struct S { t: Vec<Token>, i: usize }
/// impl TokenStream for S {
///     fn peek(&self) -> Option<&Token> { self.t.get(self.i) }
///     fn peek_ahead(&self, o: usize) -> Option<&Token> { self.t.get(self.i+o) }
///     fn next(&mut self) -> Option<Token> { let tok = self.t.get(self.i).cloned()?; self.i+=1; Some(tok) }
///     fn is_at_end(&self) -> bool { matches!(self.peek().map(|t| t.r#type()), Some(TokenType::EOF)) }
///     fn position(&self) -> usize { self.i }
///     fn checkpoint(&self) -> usize { self.i }
///     fn restore(&mut self, c: usize) { self.i = c; }
/// }
/// struct P;
/// impl Parser<()> for P {
///     fn parse(&mut self, s: &mut dyn TokenStream, _: &ParserOptions) -> ParseResult<()> {
///         let cp = s.checkpoint();
///         if self.can_parse(s) {
///             let _ = s.next();
///             return ParseResult::success(());
///         }
///         s.restore(cp);
///         let span = SymbolSpan{ start: SymbolLocation{ line:1, column:1 }, end: SymbolLocation{ line:1, column:1 } };
///         ParseResult::error(Diagnostic::error(span, "expected construct"))
///     }
///     fn can_parse(&self, s: &dyn TokenStream) -> bool {
///         matches!(s.peek().map(|t| t.r#type()), Some(TokenType::Model))
///     }
/// }
/// # let span = |s:(u32,u32),e:(u32,u32)| SymbolSpan{start:SymbolLocation{line:s.0,column:s.1},end:SymbolLocation{line:e.0,column:e.1}};
/// let toks = vec![Token::new(TokenType::Model,(1,1),(1,6)), Token::new(TokenType::EOF,(1,7),(1,7))];
/// let mut stream = S{ t: toks, i: 0 };
/// let mut p = P;
/// assert!(p.parse(&mut stream, &ParserOptions::default()).is_success());
/// ```
pub trait Parser<T> {
    /// Parse the target construct from the token stream.
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<T>;

    /// Check if this parser can handle the current token(s).
    ///
    /// Comments and doc comments are emitted as tokens by the scanner.
    /// Implementations should ignore leading comments when deciding whether
    /// a construct starts at the current position unless the grammar treats
    /// them as significant.
    fn can_parse(&self, stream: &dyn TokenStream) -> bool;

    /// Get synchronization tokens for error recovery.
    fn sync_tokens(&self) -> &[TokenType] {
        &[]
    }
}

/// Parse a complete Prisma schema.
///
/// Extends `Parser<Schema>` with a convenience method that forwards to
/// `parse`. Use this when the parser’s primary responsibility is the
/// whole schema.
pub trait SchemaParser: Parser<Schema> {
    /// Parse a complete schema from start to finish.
    fn parse_schema(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Schema> {
        self.parse(stream, options)
    }
}

/// Parse a single schema item (model, enum, etc.).
///
/// Supported declaration types for schema parsing.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, compiler_macros::EnumKindName,
)]
pub enum DeclarationType {
    Model,
    Enum,
    Datasource,
    Generator,
    Type,
}

/// Implementations should return a static item name used in diagnostics
/// and debugging.
pub trait ItemParser<T>: Parser<T> {
    /// Get the declaration type this parser handles.
    fn declaration_type(&self) -> DeclarationType;

    /// Convert the parsed item to a Declaration variant.
    fn to_declaration(&self, item: T) -> Declaration;

    /// Get the item type name for debugging/diagnostics.
    fn item_type(&self) -> &'static str {
        self.declaration_type().name()
    }
}

/// Parse expressions and values with precedence.
///
/// Expressions often require precedence climbing (e.g., handling function
/// calls and array literals binding tighter than object literals). The
/// `min_precedence` parameter controls how far to parse on the current
/// invocation.
pub trait ExpressionParser<T>: Parser<T> {
    /// Parse expressions with precedence handling.
    fn parse_with_precedence(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
        min_precedence: u8,
    ) -> ParseResult<T>;
}

/// Strategy for recovering from parse errors.
///
/// Error recovery attempts to resynchronize the parser after encountering
/// an error so that additional diagnostics can be gathered. Typical
/// strategies skip tokens until one of a set of synchronization tokens is
/// found (e.g., a closing brace or next declaration keyword).
///
/// ## Examples
/// Skip until a token from `sync_tokens` appears.
/// ```
/// # use prisma_rs::core::parser::traits::{TokenStream, ErrorRecovery};
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// struct R;
/// impl ErrorRecovery for R {
///     fn recover(
///         &mut self,
///         s: &mut dyn TokenStream,
///         sync: &[TokenType],
///     ) -> bool {
///         while let Some(t) = s.peek() {
///             if sync.iter().any(|k| *k == *t.r#type()) {
///                 return true;
///             }
///             let _ = s.next();
///         }
///         false
///     }
///     fn generate_error_diagnostic(
///         &self,
///         _s: &dyn TokenStream,
///         _e: &[TokenType],
///     ) -> prisma_rs::core::parser::config::Diagnostic {
///         use prisma_rs::core::parser::config::Diagnostic;
///         use prisma_rs::core::scanner::tokens::{
///             SymbolLocation, SymbolSpan,
///         };
///         let span = SymbolSpan {
///             start: SymbolLocation { line: 1, column: 1 },
///             end: SymbolLocation { line: 1, column: 1 },
///         };
///         Diagnostic::error(span, "parse error")
///     }
/// }
/// ```
pub trait ErrorRecovery {
    /// Attempt to recover from a parse error by synchronizing to known tokens.
    fn recover(
        &mut self,
        stream: &mut dyn TokenStream,
        sync_tokens: &[TokenType],
    ) -> bool;

    /// Generate appropriate error diagnostics for the current state.
    fn generate_error_diagnostic(
        &self,
        stream: &dyn TokenStream,
        expected: &[TokenType],
    ) -> Diagnostic;
}

/// Mutable parser state and diagnostics sink.
///
/// The context bundles global `ParserOptions`, accumulates diagnostics, and
/// exposes convenience queries such as error-limit handling and feature
/// toggles. Implementations are typically passed by `&mut` to parser
/// entry points that need to report diagnostics.
pub trait ParserContext {
    /// Get the current parser options.
    fn options(&self) -> &ParserOptions;

    /// Add a diagnostic to the current parse.
    fn add_diagnostic(&mut self, diagnostic: Diagnostic);

    /// Get all diagnostics collected so far.
    fn diagnostics(&self) -> &[Diagnostic];

    /// Check if the error limit has been exceeded.
    fn error_limit_exceeded(&self) -> bool;

    /// Check if experimental features are enabled.
    fn experimental_enabled(&self) -> bool;
}

/// Helpers for lookahead checks.
///
/// Lookahead queries allow a parser to cheaply test whether the upcoming
/// tokens match a pattern without consuming input. This is useful when
/// deciding between ambiguous alternatives or for fast-path checks in
/// `can_parse`.
///
/// ## Examples
/// Check a keyword sequence.
/// ```
/// # use prisma_rs::core::parser::traits::{TokenStream, Lookahead};
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// struct L;
/// impl Lookahead for L {
///     fn expect_sequence(
///         &self,
///         s: &dyn TokenStream,
///         expected: &[TokenType],
///     ) -> bool {
///         expected
///             .iter()
///             .enumerate()
///             .all(|(i, k)| s.peek_ahead(i).is_some_and(|t| t.r#type() == k))
///     }
///     fn starts_construct(&self, s: &dyn TokenStream, _: &str) -> bool {
///         matches!(s.peek().map(|t| t.r#type()), Some(TokenType::Model))
///     }
/// }
/// ```
pub trait Lookahead {
    /// Look ahead and check if the next tokens match a pattern.
    fn expect_sequence(
        &self,
        stream: &dyn TokenStream,
        expected: &[TokenType],
    ) -> bool;

    /// Check if the current position starts a specific construct.
    fn starts_construct(
        &self,
        stream: &dyn TokenStream,
        construct: &str,
    ) -> bool;
}

/// Compose parsers into larger units and report structure for debugging.
///
/// Composite parsers aggregate child parsers to form larger parsing units
/// (e.g., a schema parser holding item parsers). `children()` returns a
/// logical hierarchy for introspection or testing.
pub trait CompositeParser {
    /// Get the name of this parser for debugging.
    fn name(&self) -> &'static str;

    /// Get child parsers if this is a composite parser.
    fn children(&self) -> Vec<&dyn CompositeParser> {
        Vec::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};

    #[derive(Debug)]
    struct DummyStream {
        t: Vec<Token>,
        i: usize,
    }
    impl DummyStream {
        fn new(t: Vec<Token>) -> Self {
            Self { t, i: 0 }
        }
    }
    impl TokenStream for DummyStream {
        fn peek(&self) -> Option<&Token> {
            self.t.get(self.i)
        }
        fn peek_ahead(&self, o: usize) -> Option<&Token> {
            self.t.get(self.i + o)
        }
        fn next(&mut self) -> Option<Token> {
            let v = self.t.get(self.i).cloned()?;
            self.i += 1;
            Some(v)
        }
        fn is_at_end(&self) -> bool {
            self.i >= self.t.len()
        }
        fn position(&self) -> usize {
            self.i
        }
        fn checkpoint(&self) -> usize {
            self.i
        }
        fn restore(&mut self, c: usize) {
            self.i = c;
        }
    }

    #[derive(Debug, Clone)]
    struct DummyParser;
    impl Parser<()> for DummyParser {
        fn parse(
            &mut self,
            s: &mut dyn TokenStream,
            _: &ParserOptions,
        ) -> ParseResult<()> {
            if s.peek().is_some() {
                let _ = s.next();
                ParseResult::success(())
            } else {
                let span = SymbolSpan {
                    start: SymbolLocation { line: 1, column: 1 },
                    end: SymbolLocation { line: 1, column: 1 },
                };
                ParseResult::error(Diagnostic::error(span, "eof"))
            }
        }
        fn can_parse(&self, s: &dyn TokenStream) -> bool {
            s.peek().is_some()
        }
    }

    #[derive(Debug, Clone)]
    struct DummyItemParser;
    impl Parser<()> for DummyItemParser {
        fn parse(
            &mut self,
            _s: &mut dyn TokenStream,
            _o: &ParserOptions,
        ) -> ParseResult<()> {
            ParseResult::success(())
        }
        fn can_parse(&self, _s: &dyn TokenStream) -> bool {
            false
        }
    }
    impl ItemParser<()> for DummyItemParser {
        fn declaration_type(&self) -> DeclarationType {
            DeclarationType::Model
        }
        fn to_declaration(&self, (): ()) -> Declaration {
            unreachable!()
        }
    }

    #[test]
    fn declaration_type_names() {
        assert_eq!(DeclarationType::Model.name(), "Model");
        assert_eq!(DeclarationType::Enum.name(), "Enum");
        assert_eq!(DeclarationType::Datasource.name(), "Datasource");
        assert_eq!(DeclarationType::Generator.name(), "Generator");
        assert_eq!(DeclarationType::Type.name(), "Type");
    }

    #[test]
    fn item_parser_default_item_type_uses_enum_name() {
        let p = DummyItemParser;
        assert_eq!(p.item_type(), "Model");
    }

    #[test]
    fn parser_sync_tokens_default_empty() {
        let mut p = DummyParser;
        let mut s = DummyStream::new(vec![Token::new(
            TokenType::Model,
            (1, 1),
            (1, 1),
        )]);
        let res = p.parse(&mut s, &ParserOptions::default());
        assert!(res.is_success());
        assert!(p.sync_tokens().is_empty());
    }
}
