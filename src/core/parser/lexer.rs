//! Lexer interfaces and default implementations.
//!
//! This module defines the `CharacterStream` navigation trait, token recognizers,
//! the `Lexer` that produces `Token`s, and an iterator adapter.
//!
//! # Overview
//! - `CharacterStream`: navigation over character input with position tracking.
//! - `TokenRecognizer`: pluggable token recognition units.
//! - `Lexer`: drives recognition and returns `Token`s with spans.
//! - `LexerIterator`: iterator over `Result<Token, LexError>`.
//!
//! # Coordinates
//! Line and column are 1-based. Offsets are measured in character indices as
//! reported by the active `CharacterStream` implementation.

use crate::core::parser::tokens::{
    SymbolLocation, SymbolSpan, Token, TokenType,
};
use std::fmt;

/// Position within input.
///
/// Carries 1-based line/column and a character offset as defined by the active
/// `CharacterStream`.
#[derive(Debug, Clone, PartialEq)]
pub struct Position {
    line: u32,
    column: u32,
    offset: usize,
}

impl Position {
    /// Creates a new position.
    #[must_use]
    pub fn new(line: u32, column: u32, offset: usize) -> Self {
        Self {
            line,
            column,
            offset,
        }
    }

    /// Returns the 1-based line.
    #[must_use]
    pub fn line(&self) -> u32 {
        self.line
    }

    /// Returns the 1-based column.
    #[must_use]
    pub fn column(&self) -> u32 {
        self.column
    }

    /// Returns the character offset as defined by the stream.
    #[must_use]
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Converts to a token `SymbolLocation` (line/column only).
    #[must_use]
    pub fn to_symbol_location(&self) -> SymbolLocation {
        SymbolLocation {
            line: self.line,
            column: self.column,
        }
    }
}

/// Lexical error with message and source span.
#[derive(Debug, Clone)]
pub struct LexError {
    message: String,
    span: SymbolSpan,
}

impl LexError {
    /// Creates a new lexical error.
    #[must_use]
    pub fn new(message: String, span: SymbolSpan) -> Self {
        Self { message, span }
    }

    /// Returns the error message.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }

    /// Returns the span where the error occurred.
    #[must_use]
    pub fn span(&self) -> &SymbolSpan {
        &self.span
    }
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Lexical error: {}", self.message)
    }
}

impl std::error::Error for LexError {}

/// Character navigation with position tracking.
///
/// A `CharacterStream` exposes read/peek/advance operations and reports
/// positions as `Position`.
pub trait CharacterStream: std::fmt::Debug {
    /// Returns the current character without advancing,
    /// or `None` at end of input.
    fn current(&self) -> Option<char>;

    /// Advances by one character and returns the character that was current,
    /// or `None` at end.
    fn advance(&mut self) -> Option<char>;

    /// Returns the character `offset` positions ahead without advancing,
    /// or `None` if out of range.
    ///
    /// `offset == 0` is equivalent to `current()`.
    fn peek(&self, offset: usize) -> Option<char>;

    /// Returns the current position
    /// (1-based line/column; stream-defined offset).
    fn position(&self) -> Position;

    /// Advances past consecutive Unicode whitespace characters
    /// starting at the current position.
    fn skip_whitespace(&mut self);
}

/// `CharacterStream` over a UTF-8 `&str`.
///
/// Positions use 1-based line/column. Offsets correspond to character indices
/// in the internal sequence.
#[derive(Debug)]
pub struct StringCharacterStream {
    // Internal: pre-collected Unicode scalar values for random access.
    chars: Vec<char>,
    // Internal: index into `chars`.
    position: usize,
    // 1-based line.
    line: u32,
    // 1-based column.
    column: u32,
}

impl StringCharacterStream {
    /// Creates a stream over `input`.
    #[must_use]
    pub fn new(input: &str) -> Self {
        let chars: Vec<char> = input.chars().collect();
        Self {
            chars,
            position: 0,
            line: 1,
            column: 1,
        }
    }
}

impl CharacterStream for StringCharacterStream {
    fn current(&self) -> Option<char> {
        self.chars.get(self.position).copied()
    }

    fn advance(&mut self) -> Option<char> {
        if let Some(&ch) = self.chars.get(self.position) {
            self.position += 1;
            if ch == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
            Some(ch)
        } else {
            None
        }
    }

    fn peek(&self, offset: usize) -> Option<char> {
        self.chars.get(self.position + offset).copied()
    }

    fn position(&self) -> Position {
        Position::new(self.line, self.column, self.position)
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.current() {
            if ch.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }
}

/// Token recognition interface.
///
/// A `TokenRecognizer` decides whether it can parse a token at the current
/// stream position and, if so, consumes the corresponding input to produce a `TokenType`.
///
/// # Errors
/// `consume` returns `LexError` if input is invalid for the recognizer or
/// ends prematurely.
///
/// # Examples
///
/// ```rust
/// # use prisma_rs::core::parser::lexer::*;
/// # use prisma_rs::core::parser::tokens::TokenType;
///
/// #[derive(Debug)]
/// struct MyCustomRecognizer;
///
/// impl TokenRecognizer for MyCustomRecognizer {
///     fn can_handle(&self, input: &dyn CharacterStream) -> bool {
///         // Check if input starts with something this recognizer handles
///         input.current() == Some('#')
///     }
///
///     fn consume(&self, input: &mut dyn CharacterStream) -> Result<TokenType, LexError> {
///         // Parse the token and advance the input stream
///         input.advance(); // consume '#'
///         Ok(TokenType::Unsupported("#".to_string()))
///     }
/// }
/// ```
pub trait TokenRecognizer: std::fmt::Debug {
    /// Returns `true` if a token of this kind can start at the current position.
    fn can_handle(&self, input: &dyn CharacterStream) -> bool;

    /// Consumes input forming a complete token and returns its `TokenType`.
    ///
    /// On success, the stream is advanced to the first character after the token.
    ///
    /// # Errors
    /// Returns `LexError` if input is invalid for the recognizer or
    /// ends prematurely.
    fn consume(
        &self,
        input: &mut dyn CharacterStream,
    ) -> Result<TokenType, LexError>;
}

/// Lexical analyzer that produces `Token`s from character input.
///
/// Uses a `CharacterStream` for navigation and a sequence of `TokenRecognizer`s
/// to classify input into `TokenType`s.
#[derive(Debug)]
pub struct Lexer {
    // Input stream.
    scanner: Box<dyn CharacterStream>,
    // Recognizers checked in order.
    recognizers: Vec<Box<dyn TokenRecognizer>>,
}

impl Lexer {
    /// Creates a lexer from a stream and recognizer list.
    #[must_use]
    pub fn new(
        scanner: Box<dyn CharacterStream>,
        recognizers: Vec<Box<dyn TokenRecognizer>>,
    ) -> Self {
        Self {
            scanner,
            recognizers,
        }
    }

    /// Creates a lexer for `input` with the default recognizers.
    #[must_use]
    pub fn default_for_input(input: &str) -> Self {
        let scanner = Box::new(StringCharacterStream::new(input));
        let recognizers = default_recognizers();
        Self::new(scanner, recognizers)
    }

    /// Parses and returns the next token.
    ///
    /// Leading whitespace is skipped. When the end of input is reached, an
    /// `EOF` token is returned.
    ///
    /// # Returns
    /// - `Ok(Some(token))` if a token was produced.
    /// - `Ok(None)` if iteration finished without producing `EOF`.
    /// - `Err(LexError)` on invalid input.
    ///
    /// # Errors
    /// Returns `LexError` when:
    /// - An unrecognized character is encountered.
    /// - Input ends unexpectedly while determining a fallback token.
    pub fn next_token(&mut self) -> Result<Option<Token>, LexError> {
        self.scanner.skip_whitespace();

        let start_pos = self.scanner.position();

        if self.scanner.current().is_none() {
            let pos = start_pos.to_symbol_location();
            return Ok(Some(Token::new(
                TokenType::EOF,
                (pos.line, pos.column),
                (pos.line, pos.column),
            )));
        }

        for recognizer in &self.recognizers {
            if recognizer.can_handle(self.scanner.as_ref()) {
                let token_type = recognizer.consume(self.scanner.as_mut())?;
                let end_pos = self.scanner.position();
                let start_loc = start_pos.to_symbol_location();
                let end_loc = end_pos.to_symbol_location();
                return Ok(Some(Token::new(
                    token_type,
                    (start_loc.line, start_loc.column),
                    (end_loc.line, end_loc.column),
                )));
            }
        }

        let end_pos = self.scanner.position();
        let start_loc = start_pos.to_symbol_location();
        let end_loc = end_pos.to_symbol_location();
        let span = SymbolSpan {
            start: start_loc,
            end: end_loc,
        };

        match self.scanner.current() {
            Some(ch) => {
                // Consume the offending character and report it.
                self.scanner.advance();
                Err(LexError::new(
                    format!("Unexpected character: '{ch}'"),
                    span,
                ))
            }
            None => {
                // Input ended between checks; report as unexpected end.
                Err(LexError::new("Unexpected end of input".to_string(), span))
            }
        }
    }
}

/// Returns the default recognizers in priority order.
///
/// Recognizers earlier in the vector take precedence.
///
/// Order:
/// 1. Keywords
/// 2. Punctuation
/// 3. String literals
/// 4. Number literals
/// 5. Comments
/// 6. Identifiers
#[must_use]
pub fn default_recognizers() -> Vec<Box<dyn TokenRecognizer>> {
    vec![
        Box::new(KeywordRecognizer::new()),
        Box::new(PunctuationRecognizer::new()),
        Box::new(StringLiteralRecognizer::new()),
        Box::new(NumberLiteralRecognizer::new()),
        Box::new(CommentRecognizer::new()),
        Box::new(IdentifierRecognizer::new()),
    ]
}

/// Recognizes Prisma keywords and built-in scalar types.
///
/// Matches reserved words such as `model`, `enum`, `datasource`, `generator`,
/// and scalar types like `String`, `Int`, `Float`, etc. Keywords are preferred
/// over identifiers.
#[derive(Debug)]
pub struct KeywordRecognizer {
    // Map from keyword text to token type.
    keywords: std::collections::HashMap<&'static str, TokenType>,
}

impl Default for KeywordRecognizer {
    fn default() -> Self {
        Self::new()
    }
}

impl KeywordRecognizer {
    /// Creates a keyword recognizer with the built-in set.
    #[must_use]
    pub fn new() -> Self {
        let mut keywords = std::collections::HashMap::new();
        keywords.insert("generator", TokenType::Generator);
        keywords.insert("datasource", TokenType::DataSource);
        keywords.insert("model", TokenType::Model);
        keywords.insert("enum", TokenType::Enum);
        keywords.insert("type", TokenType::Type);
        keywords.insert("String", TokenType::String);
        keywords.insert("Int", TokenType::Int);
        keywords.insert("Float", TokenType::Float);
        keywords.insert("Boolean", TokenType::Boolean);
        keywords.insert("DateTime", TokenType::DateTime);
        keywords.insert("Json", TokenType::Json);
        keywords.insert("Bytes", TokenType::Bytes);
        keywords.insert("Decimal", TokenType::Decimal);

        Self { keywords }
    }
}

impl TokenRecognizer for KeywordRecognizer {
    fn can_handle(&self, input: &dyn CharacterStream) -> bool {
        if let Some(ch) = input.current()
            && (ch.is_alphabetic() || ch == '_')
        {
            let word = Self::peek_identifier(input);
            return self.keywords.contains_key(word.as_str());
        }
        false
    }

    fn consume(
        &self,
        input: &mut dyn CharacterStream,
    ) -> Result<TokenType, LexError> {
        let word = Self::consume_identifier(input);
        Ok(self.keywords[word.as_str()].clone())
    }
}

impl KeywordRecognizer {
    fn peek_identifier(input: &dyn CharacterStream) -> String {
        let mut word = String::new();
        let mut offset = 0;

        while let Some(ch) = input.peek(offset) {
            if ch.is_alphanumeric() || ch == '_' {
                word.push(ch);
                offset += 1;
            } else {
                break;
            }
        }
        word
    }

    fn consume_identifier(input: &mut dyn CharacterStream) -> String {
        let mut word = String::new();

        while let Some(ch) = input.current() {
            if ch.is_alphanumeric() || ch == '_' {
                word.push(ch);
                input.advance();
            } else {
                break;
            }
        }
        word
    }
}

/// Recognizes punctuation and operators.
///
/// Maps single-character tokens such as `{`, `}`, `(`, `)`, `[`, `]`, `,`, `:`,
/// `.`, `=`, `?`, `@`, and the multi-character forms `@@` and `[]` (list marker).
#[derive(Debug)]
pub struct PunctuationRecognizer;

impl Default for PunctuationRecognizer {
    fn default() -> Self {
        Self::new()
    }
}

impl PunctuationRecognizer {
    /// Creates a punctuation recognizer.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl TokenRecognizer for PunctuationRecognizer {
    fn can_handle(&self, input: &dyn CharacterStream) -> bool {
        if let Some(ch) = input.current() {
            matches!(
                ch,
                '=' | '?'
                    | '.'
                    | '('
                    | ')'
                    | '['
                    | ']'
                    | '{'
                    | '}'
                    | ','
                    | '@'
                    | ':'
            )
        } else {
            false
        }
    }

    fn consume(
        &self,
        input: &mut dyn CharacterStream,
    ) -> Result<TokenType, LexError> {
        let ch = input.current().ok_or_else(|| {
            let pos = input.position().to_symbol_location();
            let span = SymbolSpan {
                start: pos.clone(),
                end: pos,
            };
            LexError::new("Unexpected end of input".to_string(), span)
        })?;

        let token_type = match ch {
            '=' => TokenType::Assign,
            '?' => TokenType::Optional,
            '.' => TokenType::Dot,
            '(' => TokenType::LeftParen,
            ')' => TokenType::RightParen,
            '[' => {
                input.advance();
                if input.current() == Some(']') {
                    input.advance();
                    return Ok(TokenType::List);
                }
                return Ok(TokenType::LeftBracket);
            }
            ']' => TokenType::RightBracket,
            '{' => TokenType::LeftBrace,
            '}' => TokenType::RightBrace,
            ',' => TokenType::Comma,
            ':' => TokenType::Colon,
            '@' => {
                input.advance();
                if input.current() == Some('@') {
                    input.advance();
                    return Ok(TokenType::DoubleAt);
                }
                return Ok(TokenType::At);
            }
            _ => {
                let pos = input.position().to_symbol_location();
                let span = SymbolSpan {
                    start: pos.clone(),
                    end: pos,
                };
                return Err(LexError::new(
                    format!("Unexpected punctuation: '{ch}'"),
                    span,
                ));
            }
        };

        input.advance();
        Ok(token_type)
    }
}

/// Recognizes double-quoted string literals.
///
/// The resulting `TokenType::Literal` contains the string contents without the
/// surrounding quotes. A closing quote is treated as escaped if preceded by an
/// odd number of backslashes in the content accumulated so far.
///
/// # Errors
/// Returns `LexError` if the string is not terminated before end of input.
///
/// # Examples
/// - `"abc"` -> `Literal("abc")`
/// - `"a\"b"` -> `Literal("a\\\"b")`
#[derive(Debug)]
pub struct StringLiteralRecognizer;

impl Default for StringLiteralRecognizer {
    fn default() -> Self {
        Self::new()
    }
}

impl StringLiteralRecognizer {
    /// Creates a string literal recognizer.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl TokenRecognizer for StringLiteralRecognizer {
    fn can_handle(&self, input: &dyn CharacterStream) -> bool {
        input.current() == Some('"')
    }

    fn consume(
        &self,
        input: &mut dyn CharacterStream,
    ) -> Result<TokenType, LexError> {
        let mut content = String::new();

        input.advance(); // opening quote

        while let Some(ch) = input.current() {
            if ch == '"' {
                let mut backslash_count = 0;
                let mut temp_offset = content.len();

                while temp_offset > 0
                    && content.chars().nth(temp_offset - 1) == Some('\\')
                {
                    backslash_count += 1;
                    temp_offset -= 1;
                }

                if backslash_count % 2 == 0 {
                    input.advance(); // closing quote
                    return Ok(TokenType::Literal(content));
                }
            }

            content.push(ch);
            input.advance();
        }

        let pos = input.position().to_symbol_location();
        let span = SymbolSpan {
            start: pos.clone(),
            end: pos,
        };
        Err(LexError::new(
            "Unterminated string literal".to_string(),
            span,
        ))
    }
}

/// Recognizes decimal numbers with optional sign, fraction, and exponent.
///
/// Grammar (informal):
/// - `-? [0-9]+ ( \. [0-9]+ )? ( [eE] [+-]? [0-9]+ )?`
///
/// The resulting token is `TokenType::Literal` containing the matched text.
///
/// # Examples
/// - `42`
/// - `-3.14`
/// - `6.022e23`
#[derive(Debug)]
pub struct NumberLiteralRecognizer;

impl Default for NumberLiteralRecognizer {
    fn default() -> Self {
        Self::new()
    }
}

impl NumberLiteralRecognizer {
    /// Creates a number literal recognizer.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl TokenRecognizer for NumberLiteralRecognizer {
    fn can_handle(&self, input: &dyn CharacterStream) -> bool {
        if let Some(ch) = input.current() {
            ch.is_ascii_digit()
                || (ch == '-'
                    && input.peek(1).is_some_and(|next| next.is_ascii_digit()))
        } else {
            false
        }
    }

    fn consume(
        &self,
        input: &mut dyn CharacterStream,
    ) -> Result<TokenType, LexError> {
        let mut number = String::new();
        let mut has_dot = false;

        if input.current() == Some('-') {
            number.push('-');
            input.advance();
        }

        while let Some(ch) = input.current() {
            match ch {
                '0'..='9' => {
                    number.push(ch);
                    input.advance();
                }
                '.' if !has_dot
                    && input
                        .peek(1)
                        .is_some_and(|next| next.is_ascii_digit()) =>
                {
                    has_dot = true;
                    number.push(ch);
                    input.advance();
                }
                'e' | 'E'
                    if number
                        .chars()
                        .last()
                        .is_some_and(|last| last.is_ascii_digit()) =>
                {
                    number.push(ch);
                    input.advance();
                    if let Some(sign) = input.current()
                        && (sign == '+' || sign == '-')
                    {
                        number.push(sign);
                        input.advance();
                    }
                }
                _ => break,
            }
        }

        Ok(TokenType::Literal(number))
    }
}

/// Recognizes single-line comments `//...` and doc comments `///...`.
///
/// Returns `TokenType::Comment` or `TokenType::DocComment` with the content
/// (excluding the leading slashes and trailing newline).
#[derive(Debug)]
pub struct CommentRecognizer;

impl Default for CommentRecognizer {
    fn default() -> Self {
        Self::new()
    }
}

impl CommentRecognizer {
    /// Creates a comment recognizer.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl TokenRecognizer for CommentRecognizer {
    fn can_handle(&self, input: &dyn CharacterStream) -> bool {
        input.current() == Some('/') && input.peek(1) == Some('/')
    }

    fn consume(
        &self,
        input: &mut dyn CharacterStream,
    ) -> Result<TokenType, LexError> {
        input.advance(); // first '/'
        input.advance(); // second '/'

        let is_doc_comment = input.current() == Some('/');
        if is_doc_comment {
            input.advance(); // third '/'
        }

        let mut content = String::new();
        while let Some(ch) = input.current() {
            if ch == '\n' {
                break;
            }
            content.push(ch);
            input.advance();
        }

        if is_doc_comment {
            Ok(TokenType::DocComment(content))
        } else {
            Ok(TokenType::Comment(content))
        }
    }
}

/// Recognizes identifiers and boolean literals.
///
/// Identifiers match `[A-Za-z_][A-Za-z0-9_]*`. The strings `true` and `false`
/// are emitted as `TokenType::Literal`.
#[derive(Debug)]
pub struct IdentifierRecognizer;

impl Default for IdentifierRecognizer {
    fn default() -> Self {
        Self::new()
    }
}

impl IdentifierRecognizer {
    /// Creates an identifier recognizer.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl TokenRecognizer for IdentifierRecognizer {
    fn can_handle(&self, input: &dyn CharacterStream) -> bool {
        if let Some(ch) = input.current() {
            ch.is_alphabetic() || ch == '_'
        } else {
            false
        }
    }

    fn consume(
        &self,
        input: &mut dyn CharacterStream,
    ) -> Result<TokenType, LexError> {
        let mut identifier = String::new();

        while let Some(ch) = input.current() {
            if !ch.is_ascii() {
                let pos = input.position().to_symbol_location();
                let span = SymbolSpan {
                    start: pos.clone(),
                    end: pos,
                };
                return Err(LexError::new(
                    format!(
                        "Default parser does not support non-ASCII characters in identifiers (found \"{ch}\")"
                    ),
                    span,
                ));
            }
            if ch.is_alphanumeric() || ch == '_' {
                identifier.push(ch);
                input.advance();
            } else {
                break;
            }
        }

        if identifier == "true" || identifier == "false" {
            Ok(TokenType::Literal(identifier))
        } else {
            Ok(TokenType::Identifier(identifier))
        }
    }
}

/// Iterator over tokens produced by a `Lexer`.
///
/// Yields `Result<Token, LexError>`. Terminates after yielding `EOF` or an error.
pub struct LexerIterator {
    lexer: Lexer,
    finished: bool,
}

impl LexerIterator {
    /// Creates an iterator from a lexer.
    #[must_use]
    pub fn new(lexer: Lexer) -> Self {
        Self {
            lexer,
            finished: false,
        }
    }
}

impl Iterator for LexerIterator {
    type Item = Result<Token, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        match self.lexer.next_token() {
            Ok(Some(token)) => {
                if matches!(token.r#type(), TokenType::EOF) {
                    self.finished = true;
                }
                Some(Ok(token))
            }
            Ok(None) => {
                self.finished = true;
                None
            }
            Err(err) => Some(Err(err)),
        }
    }
}

impl Lexer {
    /// Returns an iterator that tokenizes `input` using the default recognizers.
    ///
    /// # Examples
    /// ```
    /// # use prisma_rs::core::parser::lexer::Lexer;
    /// let mut it = Lexer::tokenize("model A {}");
    /// while let Some(res) = it.next() {
    ///     let _tok = res?;
    ///     // use token
    /// }
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn tokenize(input: &str) -> LexerIterator {
        LexerIterator::new(Self::default_for_input(input))
    }
}

#[cfg(test)]
mod tests {
    #![expect(clippy::unwrap_used)]
    use super::*;

    #[test]
    fn test_character_stream_basic_operations() {
        let mut stream = StringCharacterStream::new("hello");

        assert_eq!(stream.current(), Some('h'));
        assert_eq!(stream.position().line(), 1);
        assert_eq!(stream.position().column(), 1);
        assert_eq!(stream.position().offset(), 0);

        assert_eq!(stream.advance(), Some('h'));
        assert_eq!(stream.current(), Some('e'));
        assert_eq!(stream.position().column(), 2);

        assert_eq!(stream.peek(0), Some('e'));
        assert_eq!(stream.peek(1), Some('l'));
        assert_eq!(stream.peek(10), None);
    }

    #[test]
    fn test_character_stream_line_tracking() {
        let mut stream = StringCharacterStream::new("hello\nworld");

        // Advance to 'h'
        stream.advance();
        assert_eq!(stream.position().line(), 1);
        assert_eq!(stream.position().column(), 2);

        // Advance to '\n'
        for _ in 0..4 {
            stream.advance();
        }
        assert_eq!(stream.current(), Some('\n'));

        // Advance past '\n'
        stream.advance();
        assert_eq!(stream.position().line(), 2);
        assert_eq!(stream.position().column(), 1);
        assert_eq!(stream.current(), Some('w'));
    }

    #[test]
    fn test_character_stream_skip_whitespace() {
        let mut stream = StringCharacterStream::new("   \t\n  hello");

        stream.skip_whitespace();
        assert_eq!(stream.current(), Some('h'));
        assert_eq!(stream.position().line(), 2);
        assert_eq!(stream.position().column(), 3);
    }

    #[test]
    fn test_keyword_recognizer() {
        let recognizer = KeywordRecognizer::new();
        let mut stream = StringCharacterStream::new("model User");

        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Model);
        assert_eq!(stream.current(), Some(' '));
    }

    #[test]
    fn test_keyword_recognizer_not_keyword() {
        let recognizer = KeywordRecognizer::new();
        let stream = StringCharacterStream::new("myModel");

        assert!(!recognizer.can_handle(&stream));
    }

    #[test]
    fn test_punctuation_recognizer() {
        let recognizer = PunctuationRecognizer::new();
        let mut stream = StringCharacterStream::new("@");

        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::At);
        assert_eq!(stream.current(), None);
    }

    #[test]
    fn test_punctuation_recognizer_double_at() {
        let recognizer = PunctuationRecognizer::new();
        let mut stream = StringCharacterStream::new("@@id");

        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::DoubleAt);
        assert_eq!(stream.current(), Some('i'));
    }

    #[test]
    fn test_punctuation_recognizer_array_brackets() {
        let recognizer = PunctuationRecognizer::new();
        let mut stream = StringCharacterStream::new("[]");

        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::List);
        assert_eq!(stream.current(), None);
    }

    #[test]
    fn test_string_literal_recognizer() {
        let recognizer = StringLiteralRecognizer::new();
        let mut stream = StringCharacterStream::new("\"hello world\"");

        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Literal("hello world".to_string()));
        assert_eq!(stream.current(), None);
    }

    #[test]
    fn test_string_literal_recognizer_with_escape() {
        let recognizer = StringLiteralRecognizer::new();
        let mut stream = StringCharacterStream::new("\"hello \\\"world\\\"\"");

        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(
            token,
            TokenType::Literal("hello \\\"world\\\"".to_string())
        );
    }

    #[test]
    fn test_string_literal_recognizer_unterminated() {
        let recognizer = StringLiteralRecognizer::new();
        let mut stream = StringCharacterStream::new("\"unterminated");

        assert!(recognizer.can_handle(&stream));
        let result = recognizer.consume(&mut stream);
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err().message(),
            "Unterminated string literal"
        );
    }

    #[test]
    fn test_number_literal_recognizer() {
        let recognizer = NumberLiteralRecognizer::new();

        // Test integer
        let mut stream = StringCharacterStream::new("123");
        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Literal("123".to_string()));

        // Test float
        let mut stream = StringCharacterStream::new("123.456");
        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Literal("123.456".to_string()));

        // Test negative
        let mut stream = StringCharacterStream::new("-123");
        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Literal("-123".to_string()));

        // Test scientific notation
        let mut stream = StringCharacterStream::new("1e10");
        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Literal("1e10".to_string()));
    }

    #[test]
    fn test_comment_recognizer() {
        let recognizer = CommentRecognizer::new();

        // Test regular comment
        let mut stream = StringCharacterStream::new("// this is a comment");
        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Comment(" this is a comment".to_string()));

        // Test doc comment
        let mut stream =
            StringCharacterStream::new("/// this is a doc comment");
        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(
            token,
            TokenType::DocComment(" this is a doc comment".to_string())
        );
    }

    #[test]
    fn test_identifier_recognizer() {
        let recognizer = IdentifierRecognizer::new();

        // Test regular identifier
        let mut stream = StringCharacterStream::new("myIdentifier");
        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Identifier("myIdentifier".to_string()));

        // Test boolean literals
        let mut stream = StringCharacterStream::new("true");
        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Literal("true".to_string()));

        let mut stream = StringCharacterStream::new("false");
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Literal("false".to_string()));
    }

    #[test]
    fn test_lexer_integration() {
        let mut lexer = Lexer::default_for_input("model User { id Int @id }");

        let token1 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token1.r#type(), TokenType::Model);

        let token2 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token2.r#type(), TokenType::Identifier("User".to_string()));

        let token3 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token3.r#type(), TokenType::LeftBrace);

        let token4 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token4.r#type(), TokenType::Identifier("id".to_string()));

        let token5 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token5.r#type(), TokenType::Int);

        let token6 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token6.r#type(), TokenType::At);

        let token7 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token7.r#type(), TokenType::Identifier("id".to_string()));

        let token8 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token8.r#type(), TokenType::RightBrace);

        let token9 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token9.r#type(), TokenType::EOF);
    }

    #[test]
    fn test_lexer_iterator() {
        let iter = Lexer::tokenize("@id");
        let tokens: Result<Vec<Token>, LexError> = iter.collect();
        let tokens = tokens.unwrap();

        assert_eq!(tokens.len(), 3); // @, id, EOF
        assert_eq!(*tokens[0].r#type(), TokenType::At);
        assert_eq!(
            *tokens[1].r#type(),
            TokenType::Identifier("id".to_string())
        );
        assert_eq!(*tokens[2].r#type(), TokenType::EOF);
    }

    #[test]
    fn test_error_handling() {
        let mut lexer = Lexer::default_for_input("$invalid");
        let result = lexer.next_token();
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert_eq!(error.message(), "Unexpected character: '$'");
    }

    // Edge Cases and Complex Scenarios
    #[test]
    fn test_empty_input() {
        let mut lexer = Lexer::default_for_input("");
        let token = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token.r#type(), TokenType::EOF);
    }

    #[test]
    fn test_whitespace_only() {
        let mut lexer = Lexer::default_for_input("   \t\n   ");
        let token = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token.r#type(), TokenType::EOF);
    }

    #[test]
    fn test_unicode_characters() {
        let mut lexer = Lexer::default_for_input("non_asciî");
        assert!(lexer.next_token().is_err());
        assert!(
            lexer
                .next_token()
                .is_err_and(|LexError { message, .. }| message.contains('î'))
        );
    }

    #[test]
    fn test_number_edge_cases() {
        let test_cases = vec![
            ("0", "0"),
            ("-0", "-0"),
            ("123.0", "123.0"),
            ("-123.456", "-123.456"),
            ("1e10", "1e10"),
            ("1E10", "1E10"),
            ("1e+10", "1e+10"),
            ("1e-10", "1e-10"),
            ("1.23e-10", "1.23e-10"),
            ("999999999999999999", "999999999999999999"),
        ];

        for (input, expected) in test_cases {
            let mut lexer = Lexer::default_for_input(input);
            let token = lexer.next_token().unwrap().unwrap();
            assert_eq!(
                *token.r#type(),
                TokenType::Literal(expected.to_string()),
                "Failed for input: {input}"
            );
        }
    }

    #[test]
    fn test_invalid_numbers() {
        let invalid_cases = vec!["1.2.3", "1e", "1e+", "1e-", "1."];

        for case in invalid_cases {
            let mut lexer = Lexer::default_for_input(case);
            // These should parse as separate tokens or identifiers, not valid numbers
            let tokens: Vec<_> =
                std::iter::from_fn(|| match lexer.next_token() {
                    Ok(Some(token))
                        if !matches!(token.r#type(), TokenType::EOF) =>
                    {
                        Some(token)
                    }
                    _ => None,
                })
                .collect();

            assert!(
                !tokens.is_empty(),
                "Should produce some tokens for: {case}"
            );
        }
    }

    #[test]
    fn test_string_edge_cases() {
        let test_cases = vec![
            ("\"\"", ""),
            ("\"hello\"", "hello"),
            ("\"hello world\"", "hello world"),
            ("\"with\\\"quotes\"", "with\\\"quotes"),
            ("\"with\\\\backslash\"", "with\\\\backslash"),
            ("\"with\\nNewline\"", "with\\nNewline"),
            ("\"with\\tTab\"", "with\\tTab"),
        ];

        for (input, expected) in test_cases {
            let mut lexer = Lexer::default_for_input(input);
            let token = lexer.next_token().unwrap().unwrap();
            assert_eq!(
                *token.r#type(),
                TokenType::Literal(expected.to_string()),
                "Failed for input: {input}"
            );
        }
    }

    #[test]
    fn test_complex_string_escapes() {
        let input = r#""She said \"Hello, \"World\"!\" to me.""#;
        let mut lexer = Lexer::default_for_input(input);
        let token = lexer.next_token().unwrap().unwrap();
        assert_eq!(
            *token.r#type(),
            TokenType::Literal(
                r#"She said \"Hello, \"World\"!\" to me."#.to_string()
            )
        );
    }

    #[test]
    fn test_comment_variations() {
        let test_cases = vec![
            ("//", TokenType::Comment(String::new())),
            ("// comment", TokenType::Comment(" comment".to_string())),
            ("///", TokenType::DocComment(String::new())),
            (
                "/// doc comment",
                TokenType::DocComment(" doc comment".to_string()),
            ),
            (
                "// comment with special chars !@#$%^&*()",
                TokenType::Comment(
                    " comment with special chars !@#$%^&*()".to_string(),
                ),
            ),
        ];

        for (input, expected) in test_cases {
            let mut lexer = Lexer::default_for_input(input);
            let token = lexer.next_token().unwrap().unwrap();
            assert_eq!(*token.r#type(), expected, "Failed for input: {input}");
        }
    }

    #[test]
    fn test_punctuation_sequences() {
        let input = "(){}[],.@@@?=:";
        let mut lexer = Lexer::default_for_input(input);

        let expected_tokens = vec![
            TokenType::LeftParen,
            TokenType::RightParen,
            TokenType::LeftBrace,
            TokenType::RightBrace,
            TokenType::List, // [] gets parsed as a single List token
            TokenType::Comma,
            TokenType::Dot,
            TokenType::DoubleAt,
            TokenType::At,
            TokenType::Optional,
            TokenType::Assign,
            TokenType::Colon,
        ];

        for expected in expected_tokens {
            let token = lexer.next_token().unwrap().unwrap();
            assert_eq!(*token.r#type(), expected);
        }
    }

    #[test]
    fn test_separate_brackets() {
        let input = "[ ]"; // Separate brackets with space
        let mut lexer = Lexer::default_for_input(input);

        let token1 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token1.r#type(), TokenType::LeftBracket);

        let token2 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token2.r#type(), TokenType::RightBracket);
    }

    #[test]
    fn test_complex_prisma_schema() {
        let schema = r#"
        // Database configuration
        datasource db {
            provider = "postgresql"
            url      = env("DATABASE_URL")
        }

        generator client {
            provider = "prisma-client-js"
        }
        
        /// User model with relations
        model User {
            id        Int      @id @default(autoincrement())
            email     String   @unique
            name      String?
            posts     Post[]
            createdAt DateTime @default(now())
            @@map("users")
        }
        
        model Post {
            id       Int    @id @default(autoincrement())
            title    String
            content  String?
            author   User   @relation(fields: [authorId], references: [id])
            authorId Int
        }
        "#;

        let tokens: Result<Vec<_>, _> = Lexer::tokenize(schema).collect();
        let tokens = tokens.unwrap();

        // Should have many tokens without errors
        assert!(tokens.len() > 50, "Should have parsed many tokens");

        // Verify some key tokens exist
        let token_types: Vec<_> = tokens.iter().map(Token::r#type).collect();
        assert!(token_types.contains(&&TokenType::DataSource));
        assert!(token_types.contains(&&TokenType::Generator));
        assert!(token_types.contains(&&TokenType::Model));
        assert!(token_types.contains(&&TokenType::At));
        assert!(token_types.contains(&&TokenType::DoubleAt));

        #[rustfmt::skip]
        let expected_identifiers = [
            "author"   , "authorId" , "autoincrement" , "client" , "content"   ,
            "createdAt", "db"       , "default"       , "email"  , "fields"    ,
            "id"       , "name"     , "Post"          , "posts"  , "references",
            "relation" , "title"    , "User"          ,
        ];
        for identifier in expected_identifiers {
            assert!(
                token_types
                    .contains(&&TokenType::Identifier(identifier.to_owned()))
            );
        }
    }

    #[test]
    fn test_mixed_line_endings() {
        let input = "model\rUser\n{\r\nid Int\n}";
        let tokens: Result<Vec<_>, _> = Lexer::tokenize(input).collect();
        let tokens = tokens.unwrap();

        let expected_types = vec![
            TokenType::Model,
            TokenType::Identifier("User".to_string()),
            TokenType::LeftBrace,
            TokenType::Identifier("id".to_string()),
            TokenType::Int,
            TokenType::RightBrace,
            TokenType::EOF,
        ];

        assert_eq!(tokens.len(), expected_types.len());
        for (token, expected) in tokens.iter().zip(expected_types.iter()) {
            assert_eq!(token.r#type(), expected);
        }
    }

    #[test]
    fn test_identifier_edge_cases() {
        let test_cases = vec![
            ("a", TokenType::Identifier("a".to_string())),
            ("A", TokenType::Identifier("A".to_string())),
            (
                "snake_case",
                TokenType::Identifier("snake_case".to_string()),
            ),
            ("camelCase", TokenType::Identifier("camelCase".to_string())),
            (
                "PascalCase",
                TokenType::Identifier("PascalCase".to_string()),
            ),
            (
                "with123numbers",
                TokenType::Identifier("with123numbers".to_string()),
            ),
            ("_", TokenType::Identifier("_".to_string())),
            ("__private", TokenType::Identifier("__private".to_string())),
            ("true", TokenType::Literal("true".to_string())),
            ("false", TokenType::Literal("false".to_string())),
        ];

        for (input, expected) in test_cases {
            let mut lexer = Lexer::default_for_input(input);
            let token = lexer.next_token().unwrap().unwrap();
            assert_eq!(*token.r#type(), expected, "Failed for input: {input}");
        }
    }

    #[test]
    fn test_position_tracking_accuracy() {
        let input = "model\n  User {\n    id Int\n  }";
        let mut lexer = Lexer::default_for_input(input);

        // Test that positions are tracked correctly through newlines and indentation
        let token1 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token1.r#type(), TokenType::Model);

        let token2 = lexer.next_token().unwrap().unwrap(); // User
        assert_eq!(*token2.r#type(), TokenType::Identifier("User".to_string()));

        let token3 = lexer.next_token().unwrap().unwrap(); // {
        assert_eq!(*token3.r#type(), TokenType::LeftBrace);

        let token4 = lexer.next_token().unwrap().unwrap(); // id
        assert_eq!(*token4.r#type(), TokenType::Identifier("id".to_string()));
    }

    #[test]
    fn test_error_recovery() {
        let input = "model User { $invalid id Int }";
        let mut lexer = Lexer::default_for_input(input);

        // Should parse up to the invalid character
        let token1 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token1.r#type(), TokenType::Model);

        let token2 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token2.r#type(), TokenType::Identifier("User".to_string()));

        let token3 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token3.r#type(), TokenType::LeftBrace);

        // This should error
        let error = lexer.next_token().unwrap_err();
        assert_eq!(error.message(), "Unexpected character: '$'");
    }

    #[test]
    fn test_very_long_identifiers() {
        let long_identifier = "a".repeat(1000);
        let mut lexer = Lexer::default_for_input(&long_identifier);
        let token = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token.r#type(), TokenType::Identifier(long_identifier));
    }

    #[test]
    fn test_deeply_nested_structures() {
        let input = "{{{{{{}}}}}}";
        let tokens: Result<Vec<_>, _> = Lexer::tokenize(input).collect();
        let tokens = tokens.unwrap();

        assert_eq!(tokens.len(), 13); // 6 left + 6 right + EOF

        for token in tokens.iter().take(6) {
            assert_eq!(*token.r#type(), TokenType::LeftBrace);
        }
        for token in tokens.iter().take(12).skip(6) {
            assert_eq!(*token.r#type(), TokenType::RightBrace);
        }
    }
}
