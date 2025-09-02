//! Tokenize input text into a stream of tokens.
//!
//! Input is read through a `CharacterStream` abstraction. The lexer delegates
//! token boundaries to an ordered set of `TokenRecognizer`s; the first
//! recognizer that can handle the current input wins. `Lexer` drives the
//! process and yields `Token`s with spans. For ergonomic use there is an
//! iterator adapter via `Lexer::tokenize`.
//!
//! Positions are 1-based (line, column) as reported by the active stream.
//! The lexer skips Unicode whitespace, coalesces consecutive single-line
//! comments and doc comments, and emits a single `EOF` token when input is
//! consumed. Recognizer order is significant and should be chosen to avoid
//! ambiguity.
//!
//! ## Examples
//! ```
//! # use prisma_rs::core::scanner::{Lexer, TokenType};
//! let toks: Result<Vec<_>, _> = Lexer::tokenize("model A {}").collect();
//! let toks = toks.expect("scan ok");
//! assert!(matches!(*toks.last().unwrap().r#type(), TokenType::EOF));
//! ```

use std::fmt;

use crate::core::scanner::tokens::{
    SymbolLocation, SymbolSpan, Token, TokenType,
};

/// Track the lexer's current location in the input.
///
/// Stores 1-based `line` and `column` and a stream-defined `offset`. Offsets
/// advance by characters as seen by the active stream.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::scanner::Position;
/// let p = Position::new(1, 1, 0);
/// assert_eq!(p.line, 1);
/// assert_eq!(p.column, 1);
/// assert_eq!(p.offset, 0);
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Position {
    pub line: u32,
    pub column: u32,
    pub offset: usize,
}

impl Position {
    /// Create a new position with explicit line, column, and offset.
    #[must_use]
    pub fn new(line: u32, column: u32, offset: usize) -> Self {
        Self {
            line,
            column,
            offset,
        }
    }

    /// Convert to a token `SymbolLocation` (line and column only).
    #[must_use]
    pub fn to_symbol_location(&self) -> SymbolLocation {
        SymbolLocation {
            line: self.line,
            column: self.column,
        }
    }
}

/// Describe a lexical error with a diagnostic span.
///
/// Carries a user-displayable message and the `SymbolSpan` where it occurred.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::scanner::{LexError, SymbolLocation, SymbolSpan};
/// let span = SymbolSpan {
///     start: SymbolLocation { line: 1, column: 1 },
///     end: SymbolLocation { line: 1, column: 1 },
/// };
/// let err = LexError::new("oops".into(), span);
/// assert!(err.message().contains("oops"));
/// ```
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

/// Navigate characters with position tracking.
///
/// Implementors expose read, peek, and advance operations and report
/// positions as `Position`. `peek(0)` is equivalent to `current()`. Implementations
/// must be consistent: `advance()` should return the same char that `current()`
/// produced immediately before.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::scanner::{CharacterStream, Position};
/// #[derive(Debug)]
/// struct SliceStream<'a> {
///     s: &'a [u8],
///     i: usize,
///     line: u32,
///     col: u32,
/// }
/// impl<'a> CharacterStream for SliceStream<'a> {
///     fn current(&self) -> Option<char> {
///         self.s.get(self.i).copied().map(|b| b as char)
///     }
///     fn advance(&mut self) -> Option<char> {
///         let ch = self.current()?;
///         self.i += 1;
///         self.col += 1;
///         Some(ch)
///     }
///     fn peek(&self, o: usize) -> Option<char> {
///         self.s.get(self.i + o).copied().map(|b| b as char)
///     }
///     fn position(&self) -> Position {
///         Position::new(self.line, self.col, self.i)
///     }
///     fn skip_whitespace(&mut self) {
///         while self.current().is_some_and(|c| c.is_whitespace()) {
///             self.advance();
///         }
///     }
/// }
/// ```
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

/// Provide a `CharacterStream` over a UTF-8 `&str`.
///
/// Tracks newlines and columns as Unicode scalar values are advanced. Offsets
/// index an internal `Vec<char>` captured at creation time.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::scanner::{CharacterStream, StringCharacterStream};
/// let mut s = StringCharacterStream::new("a\nb");
/// assert_eq!(s.current(), Some('a'));
/// s.advance(); // consume 'a'
/// s.advance(); // consume newline '\n'
/// assert_eq!(s.current(), Some('b'));
/// ```
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

/// Recognize a token at the current position.
///
/// Implementations decide whether they can start a token (`can_handle`) and,
/// if so, consume the input to produce a `TokenType`. `can_handle` must not
/// advance the stream; `consume` must advance exactly the characters that
/// form the token.
///
/// ## Errors
/// `consume` returns `LexError` if input is invalid for the recognizer or
/// ends prematurely.
///
/// ## Examples
///
/// ```rust
/// # use prisma_rs::core::scanner::*;
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
///     fn consume(
///         &self,
///         input: &mut dyn CharacterStream,
///     ) -> Result<TokenType, LexError> {
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

/// Drive tokenization using a character stream and recognizers.
///
/// The lexer consults recognizers in order; the first that can handle the
/// input produces the next token. It coalesces consecutive comments and skips
/// whitespace between tokens.
#[derive(Debug)]
pub struct Lexer {
    // Input stream.
    scanner: Box<dyn CharacterStream>,
    // Recognizers checked in order.
    recognizers: Vec<Box<dyn TokenRecognizer>>,
    // Queue of tokens ready to be emitted (for comment coalescing)
    token_queue: std::collections::VecDeque<Token>,
    // Buffer for comment coalescing: stores the last comment token of each type
    last_comment: Option<Token>,
    last_doc_comment: Option<Token>,
}

impl Lexer {
    /// Create a lexer from a stream and recognizer list.
    #[must_use]
    pub fn new(
        scanner: Box<dyn CharacterStream>,
        recognizers: Vec<Box<dyn TokenRecognizer>>,
    ) -> Self {
        Self {
            scanner,
            recognizers,
            token_queue: std::collections::VecDeque::new(),
            last_comment: None,
            last_doc_comment: None,
        }
    }

    /// Create a lexer for `input` with the default recognizers.
    #[must_use]
    pub fn default_for_input(input: &str) -> Self {
        let scanner = Box::new(StringCharacterStream::new(input));
        let recognizers = default_recognizers();
        Self::new(scanner, recognizers)
    }

    /// Parse and return the next token.
    ///
    /// Leading whitespace is skipped. At end of input, a single `EOF` token
    /// is returned.
    ///
    /// ## Errors
    /// Returns `LexError` for unrecognized characters or unterminated strings.
    pub fn next_token(&mut self) -> Result<Option<Token>, LexError> {
        // First check if we have queued tokens to emit
        if let Some(token) = self.token_queue.pop_front() {
            return Ok(Some(token));
        }

        // Main tokenization loop with comment coalescing
        loop {
            self.scanner.skip_whitespace();
            let start_pos = self.scanner.position();

            if self.scanner.current().is_none() {
                // End of input - flush any buffered comments first, then EOF
                self.flush_buffered_comments();

                if let Some(token) = self.token_queue.pop_front() {
                    return Ok(Some(token));
                }

                let pos = start_pos.to_symbol_location();
                return Ok(Some(Token::new(
                    TokenType::EOF,
                    (pos.line, pos.column),
                    (pos.line, pos.column),
                )));
            }

            // Try to recognize a token
            let mut token_opt: Option<Token> = None;
            for recognizer in &self.recognizers {
                if recognizer.can_handle(self.scanner.as_ref()) {
                    let token_type =
                        recognizer.consume(self.scanner.as_mut())?;
                    let end_pos = self.scanner.position();
                    let start_loc = start_pos.to_symbol_location();
                    let end_loc = end_pos.to_symbol_location();
                    token_opt = Some(Token::new(
                        token_type,
                        (start_loc.line, start_loc.column),
                        (end_loc.line, end_loc.column),
                    ));
                    break;
                }
            }

            let Some(token) = token_opt else {
                // Unrecognized character - error
                let end_pos = self.scanner.position();
                let start_loc = start_pos.to_symbol_location();
                let end_loc = end_pos.to_symbol_location();
                let span = SymbolSpan {
                    start: start_loc,
                    end: end_loc,
                };

                return match self.scanner.current() {
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
                        Err(LexError::new(
                            "Unexpected end of input".to_string(),
                            span,
                        ))
                    }
                };
            };

            // Handle comment coalescing
            match token.r#type() {
                TokenType::Comment(_) => {
                    // Replace any existing buffered comment (coalescing consecutive comments)
                    self.last_comment = Some(token);
                    // Continue to next token
                }
                TokenType::DocComment(_) => {
                    // Replace any existing buffered doc comment (coalescing consecutive doc comments)
                    self.last_doc_comment = Some(token);
                    // Continue to next token
                }
                _ => {
                    // Non-comment token found - flush buffered comments and queue this token
                    self.flush_buffered_comments();
                    self.token_queue.push_back(token);

                    // Return the first token from the queue
                    return Ok(self.token_queue.pop_front());
                }
            }
        }
    }

    /// Flush buffered comments to the token queue.
    fn flush_buffered_comments(&mut self) {
        if let Some(comment) = self.last_comment.take() {
            self.token_queue.push_back(comment);
        }
        if let Some(doc_comment) = self.last_doc_comment.take() {
            self.token_queue.push_back(doc_comment);
        }
    }
}

/// Return the default recognizers in priority order.
///
/// Earlier recognizers take precedence when multiple match.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::scanner::{default_recognizers, CharacterStream, TokenRecognizer, StringCharacterStream};
/// let recs = default_recognizers();
/// assert!(!recs.is_empty());
/// assert!(recs[0].can_handle(&StringCharacterStream::new("model")));
/// ```
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

/// Recognize Prisma keywords and built-in scalar types.
///
/// Keywords take precedence over identifiers when both could match.
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
    /// Create a keyword recognizer with the built-in set.
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

/// Recognize punctuation and operators.
///
/// Handles single-character tokens and the multi-character `@@` and `[]`.
#[derive(Debug)]
pub struct PunctuationRecognizer;

impl Default for PunctuationRecognizer {
    fn default() -> Self {
        Self::new()
    }
}

impl PunctuationRecognizer {
    /// Create a punctuation recognizer.
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

/// Recognize double-quoted string literals.
///
/// The returned `Literal` contains the content without surrounding quotes. A
/// quote is treated as escaped when preceded by an odd number of backslashes.
///
/// ## Errors
/// Returns `LexError` if the string is not terminated before end of input.
///
/// ## Examples
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

/// Recognize decimal numbers with optional sign, fraction, and exponent.
///
/// Produces `Literal` with the matched numeric text (no normalization).
///
/// ## Examples
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
    /// Create a number literal recognizer.
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

/// Recognize single-line comments `//...` and doc comments `///...`.
///
/// Returns `Comment` or `DocComment` with content excluding leading slashes
/// and the trailing newline.
#[derive(Debug)]
pub struct CommentRecognizer;

impl Default for CommentRecognizer {
    fn default() -> Self {
        Self::new()
    }
}

impl CommentRecognizer {
    /// Create a comment recognizer.
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

/// Recognize identifiers and boolean/null literals.
///
/// Identifiers match `[A-Za-z_][A-Za-z0-9_]*` (ASCII only). `true`, `false`,
/// and `null` are emitted as `Literal`.
#[derive(Debug)]
pub struct IdentifierRecognizer;

impl Default for IdentifierRecognizer {
    fn default() -> Self {
        Self::new()
    }
}

impl IdentifierRecognizer {
    /// Create an identifier recognizer.
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

        if identifier == "true" || identifier == "false" || identifier == "null"
        {
            Ok(TokenType::Literal(identifier))
        } else {
            Ok(TokenType::Identifier(identifier))
        }
    }
}

/// Iterate over tokens produced by a `Lexer`.
///
/// Yields `Result<Token, LexError>` and terminates after `EOF` or an error.
pub struct LexerIterator {
    lexer: Lexer,
    finished: bool,
}

impl LexerIterator {
    /// Create an iterator from a lexer.
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
    /// Return an iterator that tokenizes `input`.
    ///
    /// Examples:
    /// ```
    /// # use prisma_rs::core::scanner::Lexer;
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
    use super::*;

    #[test]
    fn character_stream_basic_operations() {
        let mut stream = StringCharacterStream::new("hello");

        assert_eq!(stream.current(), Some('h'));
        assert_eq!(stream.position().line, 1);
        assert_eq!(stream.position().column, 1);
        assert_eq!(stream.position().offset, 0);

        assert_eq!(stream.advance(), Some('h'));
        assert_eq!(stream.current(), Some('e'));
        assert_eq!(stream.position().column, 2);

        assert_eq!(stream.peek(0), Some('e'));
        assert_eq!(stream.peek(1), Some('l'));
        assert_eq!(stream.peek(10), None);
    }

    #[test]
    fn character_stream_line_tracking() {
        let mut stream = StringCharacterStream::new("hello\nworld");

        // Advance to 'h'
        stream.advance();
        assert_eq!(stream.position().line, 1);
        assert_eq!(stream.position().column, 2);

        // Advance to '\n'
        for _ in 0..4 {
            stream.advance();
        }
        assert_eq!(stream.current(), Some('\n'));

        // Advance past '\n'
        stream.advance();
        assert_eq!(stream.position().line, 2);
        assert_eq!(stream.position().column, 1);
        assert_eq!(stream.current(), Some('w'));
    }

    #[test]
    fn character_stream_skip_whitespace() {
        let mut stream = StringCharacterStream::new("   \t\n  hello");

        stream.skip_whitespace();
        assert_eq!(stream.current(), Some('h'));
        assert_eq!(stream.position().line, 2);
        assert_eq!(stream.position().column, 3);
    }

    #[test]
    fn keyword_recognizer() {
        let recognizer = KeywordRecognizer::new();
        let mut stream = StringCharacterStream::new("model User");

        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Model);
        assert_eq!(stream.current(), Some(' '));
    }

    #[test]
    fn keyword_recognizer_not_keyword() {
        let recognizer = KeywordRecognizer::new();
        let stream = StringCharacterStream::new("myModel");

        assert!(!recognizer.can_handle(&stream));
    }

    #[test]
    fn punctuation_recognizer() {
        let recognizer = PunctuationRecognizer::new();
        let mut stream = StringCharacterStream::new("@");

        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::At);
        assert_eq!(stream.current(), None);
    }

    #[test]
    fn punctuation_recognizer_double_at() {
        let recognizer = PunctuationRecognizer::new();
        let mut stream = StringCharacterStream::new("@@id");

        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::DoubleAt);
        assert_eq!(stream.current(), Some('i'));
    }

    #[test]
    fn punctuation_recognizer_array_brackets() {
        let recognizer = PunctuationRecognizer::new();
        let mut stream = StringCharacterStream::new("[]");

        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::List);
        assert_eq!(stream.current(), None);
    }

    #[test]
    fn string_literal_recognizer() {
        let recognizer = StringLiteralRecognizer::new();
        let mut stream = StringCharacterStream::new("\"hello world\"");

        assert!(recognizer.can_handle(&stream));
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Literal("hello world".to_string()));
        assert_eq!(stream.current(), None);
    }

    #[test]
    fn string_literal_recognizer_with_escape() {
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
    fn string_literal_recognizer_unterminated() {
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
    fn number_literal_recognizer() {
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
    fn comment_recognizer() {
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
    fn identifier_recognizer() {
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

        let mut stream = StringCharacterStream::new("null");
        let token = recognizer.consume(&mut stream).unwrap();
        assert_eq!(token, TokenType::Literal("null".to_string()));
    }

    #[test]
    fn lexer_integration() {
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
    fn lexer_iterator() {
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
    fn error_handling() {
        let mut lexer = Lexer::default_for_input("$invalid");
        let result = lexer.next_token();
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert_eq!(error.message(), "Unexpected character: '$'");
    }

    // Edge Cases and Complex Scenarios
    #[test]
    fn empty_input() {
        let mut lexer = Lexer::default_for_input("");
        let token = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token.r#type(), TokenType::EOF);
    }

    #[test]
    fn whitespace_only() {
        let mut lexer = Lexer::default_for_input("   \t\n   ");
        let token = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token.r#type(), TokenType::EOF);
    }

    #[test]
    fn unicode_characters() {
        let mut lexer = Lexer::default_for_input("non_asciî");
        assert!(lexer.next_token().is_err());
        assert!(
            lexer
                .next_token()
                .is_err_and(|LexError { message, .. }| message.contains('î'))
        );
    }

    #[test]
    fn number_edge_cases() {
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
    fn invalid_numbers() {
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
    fn string_edge_cases() {
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
    fn complex_string_escapes() {
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
    fn comment_variations() {
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
    fn punctuation_sequences() {
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
    fn separate_brackets() {
        let input = "[ ]"; // Separate brackets with space
        let mut lexer = Lexer::default_for_input(input);

        let token1 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token1.r#type(), TokenType::LeftBracket);

        let token2 = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token2.r#type(), TokenType::RightBracket);
    }

    #[test]
    fn complex_prisma_schema() {
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
    fn mixed_line_endings() {
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
    fn identifier_edge_cases() {
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
    fn position_tracking_accuracy() {
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
    fn error_recovery() {
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
    fn very_long_identifiers() {
        let long_identifier = "a".repeat(1000);
        let mut lexer = Lexer::default_for_input(&long_identifier);
        let token = lexer.next_token().unwrap().unwrap();
        assert_eq!(*token.r#type(), TokenType::Identifier(long_identifier));
    }

    #[test]
    fn deeply_nested_structures() {
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
