//! Feed tokens to parsers with ergonomic lookahead and filtering.
//!
//! This module provides concrete `TokenStream` implementations and a small
//! extension trait for convenience methods used throughout parsing. The
//! primary implementation, `VectorTokenStream`, stores tokens in memory and
//! offers O(1) lookahead with checkpoint/restore for speculative parsing.
//! `FilteredTokenStream` composes over any `TokenStream` to hide specific
//! token kinds (commonly comments) from the parser.
//!
//! Parsers rely on predictable, non-destructive lookahead. Use
//! `checkpoint()`/`restore()` around speculative paths. For comment-aware
//! checks, prefer the non-comment helpers on `TokenStreamExt` (e.g.,
//! `peek_non_comment`, `peek_ahead_non_comment`, `check_non_comment`).
//!
//! ## Examples
//! Build a `VectorTokenStream` and read tokens with a checkpoint.
//! ```
//! # use prisma_rs::core::parser::stream::VectorTokenStream;
//! # use prisma_rs::core::parser::traits::TokenStream;
//! # use prisma_rs::core::scanner::tokens::{Token, TokenType};
//! let toks = vec![
//!     Token::new(TokenType::Model, (1, 1), (1, 6)),
//!     Token::new(TokenType::Identifier("User".into()), (1, 7), (1, 11)),
//!     Token::new(TokenType::EOF, (1, 12), (1, 12)),
//! ];
//! let mut s = VectorTokenStream::new(toks);
//! assert!(matches!(s.peek().unwrap().r#type(), TokenType::Model));
//! let cp = s.checkpoint();
//! let _ = s.next(); // consume 'model'
//! s.restore(cp); // backtrack
//! assert!(matches!(s.peek().unwrap().r#type(), TokenType::Model));
//! ```

use crate::core::parser::traits::TokenStream;
use crate::core::scanner::tokens::{Token, TokenType};

/// A token stream backed by a vector of tokens.
///
/// This is the primary in-memory implementation used by parsers. It provides
/// constant-time indexed lookahead, linear consumption, and cheap
/// checkpoint/restore by saving the current index.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::stream::VectorTokenStream;
/// # use prisma_rs::core::parser::traits::TokenStream;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::Enum, (1, 1), (1, 5)),
///     Token::new(TokenType::EOF, (1, 6), (1, 6)),
/// ]);
/// assert!(s.checkpoint() == 0);
/// assert!(matches!(s.peek().unwrap().r#type(), TokenType::Enum));
/// let _ = s.next(); // consume Enum
/// assert!(!s.is_at_end());
/// let _ = s.next(); // consume EOF
/// assert!(s.is_at_end());
/// ```
#[derive(Debug)]
pub struct VectorTokenStream {
    /// The tokens in this stream.
    tokens: Vec<Token>,
    /// Current position in the token vector.
    position: usize,
}

impl VectorTokenStream {
    /// Create a new token stream from a vector of tokens.
    #[must_use]
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            position: 0,
        }
    }

    /// Get the total number of tokens in this stream.
    #[must_use]
    pub fn len(&self) -> usize {
        self.tokens.len()
    }

    /// Check if the stream is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    /// Reset the stream to the beginning.
    pub fn reset(&mut self) {
        self.position = 0;
    }

    /// Get all remaining tokens from current position.
    #[must_use]
    pub fn remaining(&self) -> &[Token] {
        &self.tokens[self.position..]
    }
}

impl TokenStream for VectorTokenStream {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }

    fn peek_ahead(&self, offset: usize) -> Option<&Token> {
        self.tokens.get(self.position + offset)
    }

    fn next(&mut self) -> Option<Token> {
        if self.position < self.tokens.len() {
            let token = self.tokens[self.position].clone();
            self.position += 1;
            Some(token)
        } else {
            None
        }
    }

    fn is_at_end(&self) -> bool {
        self.position >= self.tokens.len()
    }

    fn position(&self) -> usize {
        self.position
    }

    fn checkpoint(&self) -> usize {
        self.position
    }

    fn restore(&mut self, checkpoint: usize) {
        self.position = checkpoint.min(self.tokens.len());
    }
}

/// A token stream that filters out specific token types.
///
/// Wraps an inner `TokenStream` and skips tokens with types present in
/// `filtered_types`. This is commonly used to ignore comments and doc
/// comments while preserving all other tokens.
///
/// The filter is applied eagerly when constructed and after each
/// consumption or restore operation to ensure `peek()` always returns a
/// non-filtered token.
///
/// ## Examples
/// Hide comment tokens from the parser.
/// ```
/// # use prisma_rs::core::parser::stream::VectorTokenStream;
/// # use prisma_rs::core::parser::stream::FilteredTokenStream;
/// # use prisma_rs::core::parser::traits::TokenStream;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// let inner = VectorTokenStream::new(vec![
///     Token::new(TokenType::Comment(" x".into()), (1, 1), (1, 4)),
///     Token::new(TokenType::Model, (1, 5), (1, 10)),
///     Token::new(TokenType::DocComment(" y".into()), (1, 11), (1, 20)),
///     Token::new(TokenType::Identifier("User".into()), (1, 21), (1, 25)),
/// ]);
/// let mut s = FilteredTokenStream::new(
///     inner,
///     vec![
///         TokenType::Comment(" x".into()),
///         TokenType::DocComment(" y".into()),
///     ],
/// );
/// assert!(matches!(s.peek().unwrap().r#type(), TokenType::Model));
/// let _ = s.next();
/// assert!(matches!(
///     s.peek().unwrap().r#type(),
///     TokenType::Identifier(_)
/// ));
/// ```
#[derive(Debug)]
pub struct FilteredTokenStream<S: TokenStream> {
    /// The underlying token stream.
    inner: S,
    /// Token types to filter out.
    filtered_types: Vec<TokenType>,
}

impl<S: TokenStream> FilteredTokenStream<S> {
    /// Create a new filtered token stream.
    pub fn new(inner: S, filtered_types: Vec<TokenType>) -> Self {
        let mut stream = Self {
            inner,
            filtered_types,
        };
        stream.advance_to_next_valid();
        stream
    }

    /// Advance the inner stream past any filtered tokens.
    fn advance_to_next_valid(&mut self) {
        while let Some(token) = self.inner.peek() {
            if self.filtered_types.iter().any(|ft| {
                std::mem::discriminant(ft)
                    == std::mem::discriminant(token.r#type())
            }) {
                self.inner.next();
            } else {
                break;
            }
        }
    }
}

impl<S: TokenStream> TokenStream for FilteredTokenStream<S> {
    fn peek(&self) -> Option<&Token> {
        self.inner.peek()
    }

    fn peek_ahead(&self, mut offset: usize) -> Option<&Token> {
        let mut current_offset = 0;

        // Skip filtered tokens while counting non-filtered ones
        while let Some(token) = self.inner.peek_ahead(current_offset) {
            if self.filtered_types.iter().any(|ft| {
                std::mem::discriminant(ft)
                    == std::mem::discriminant(token.r#type())
            }) {
                // filtered, skip
            } else if offset == 0 {
                return Some(token);
            } else {
                offset -= 1;
            }
            current_offset += 1;
        }

        None
    }

    fn next(&mut self) -> Option<Token> {
        let token = self.inner.next();
        self.advance_to_next_valid();
        token
    }

    fn is_at_end(&self) -> bool {
        self.inner.is_at_end()
    }

    fn position(&self) -> usize {
        self.inner.position()
    }

    fn checkpoint(&self) -> usize {
        self.inner.checkpoint()
    }

    fn restore(&mut self, checkpoint: usize) {
        self.inner.restore(checkpoint);
        self.advance_to_next_valid();
    }
}

/// Extension methods for token streams to make parsing more convenient.
///
/// These helpers compare only token kinds (ignoring payloads like lexemes)
/// and offer simple synchronization utilities. The “non-comment” helpers
/// treat `Comment` and `DocComment` as skippable for lookahead decisions.
///
/// Bring the trait into scope to call these methods.
/// `use prisma_rs::core::parser::stream::TokenStreamExt;`
///
/// ## Examples
/// Check, match, and synchronize using the extension methods.
/// ```
/// # use prisma_rs::core::parser::stream::{VectorTokenStream, TokenStreamExt};
/// # use prisma_rs::core::parser::traits::TokenStream;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::Model, (1,1), (1,6)),
///     Token::new(TokenType::Identifier("User".into()), (1,7), (1,11)),
///     Token::new(TokenType::LeftBrace, (1,12), (1,12)),
/// ]);
/// assert!(s.check(TokenType::Model));
/// let _ = s.match_token(TokenType::Model);
/// s.synchronize(&[TokenType::LeftBrace]);
/// assert!(matches!(s.peek().unwrap().r#type(), TokenType::LeftBrace));
/// ```
pub trait TokenStreamExt: TokenStream {
    /// Check if the current token matches the expected type.
    fn check(&self, expected: TokenType) -> bool {
        self.peek().is_some_and(|token| {
            std::mem::discriminant(token.r#type())
                == std::mem::discriminant(&expected)
        })
    }

    /// Check if the current token is one of the expected types.
    fn check_any(&self, expected: &[TokenType]) -> bool {
        if let Some(current) = self.peek() {
            expected.iter().any(|expected_type| {
                std::mem::discriminant(current.r#type())
                    == std::mem::discriminant(expected_type)
            })
        } else {
            false
        }
    }

    /// Consume a token if it matches the expected type.
    fn match_token(&mut self, expected: TokenType) -> Option<Token> {
        if self.check(expected) {
            self.next()
        } else {
            None
        }
    }

    /// Skip tokens until we find one of the synchronization tokens.
    fn synchronize(&mut self, sync_tokens: &[TokenType]) {
        while !self.is_at_end() {
            if let Some(current) = self.peek()
                && sync_tokens.iter().any(|sync_token| {
                    std::mem::discriminant(current.r#type())
                        == std::mem::discriminant(sync_token)
                })
            {
                break;
            }
            self.next();
        }
    }

    /// Skip tokens until we find one of the synchronization tokens.
    /// Returns true if a sync token was found, false if end-of-stream.
    fn synchronize_to(&mut self, sync_tokens: &[TokenType]) -> bool {
        while !self.is_at_end() {
            if let Some(current) = self.peek()
                && sync_tokens.iter().any(|sync_token| {
                    std::mem::discriminant(current.r#type())
                        == std::mem::discriminant(sync_token)
                })
            {
                return true;
            }
            self.next();
        }
        false
    }

    /// Peek at the current token, skipping `Comment` and `DocComment`.
    ///
    /// Useful in `can_parse` to make decisions based on significant tokens.
    fn peek_non_comment(&self) -> Option<&Token> {
        let mut offset = 0;
        while let Some(token) = self.peek_ahead(offset) {
            match token.r#type() {
                TokenType::Comment(_) | TokenType::DocComment(_) => {
                    offset += 1;
                }
                _ => return Some(token),
            }
        }
        None
    }

    /// Peek ahead at non-comment tokens only.
    ///
    /// Counts only significant tokens toward `target_offset`.
    fn peek_ahead_non_comment(
        &self,
        mut target_offset: usize,
    ) -> Option<&Token> {
        let mut offset = 0;
        while let Some(token) = self.peek_ahead(offset) {
            match token.r#type() {
                TokenType::Comment(_) | TokenType::DocComment(_) => {
                    offset += 1;
                }
                _ => {
                    if target_offset == 0 {
                        return Some(token);
                    }
                    target_offset -= 1;
                    offset += 1;
                }
            }
        }
        None
    }

    /// Check if the current non-comment token matches the expected type.
    ///
    /// Compares only the token kind (variant), ignoring any string payloads.
    fn check_non_comment(&self, expected: TokenType) -> bool {
        self.peek_non_comment().is_some_and(|token| {
            std::mem::discriminant(token.r#type())
                == std::mem::discriminant(&expected)
        })
    }
}

// Implement the extension trait for all token streams
impl<T: ?Sized + TokenStream> TokenStreamExt for T {}

#[cfg(test)]
mod tests {
    #![expect(clippy::expect_used, clippy::unwrap_used)]

    use super::*;

    fn create_test_token(token_type: TokenType) -> Token {
        Token::new(token_type, (1, 1), (1, 2))
    }

    #[test]
    fn vector_token_stream_basic() {
        let tokens = vec![
            create_test_token(TokenType::Model),
            create_test_token(TokenType::Identifier("User".to_string())),
            create_test_token(TokenType::LeftBrace),
        ];

        let mut stream = VectorTokenStream::new(tokens);

        assert!(!stream.is_at_end());
        assert_eq!(stream.len(), 3);
        assert_eq!(stream.position(), 0);

        // Test peeking
        assert!(matches!(
            stream.peek().expect("Should have token").r#type(),
            TokenType::Model
        ));
        assert!(matches!(
            stream
                .peek_ahead(1)
                .expect("Should have token ahead")
                .r#type(),
            TokenType::Identifier(_)
        ));

        // Test consumption
        assert!(matches!(
            stream.next().expect("Should have token").r#type(),
            TokenType::Model
        ));
        assert_eq!(stream.position(), 1);

        // Test checkpoint/restore
        let checkpoint = stream.checkpoint();
        stream.next(); // consume Ident
        assert_eq!(stream.position(), 2);
        stream.restore(checkpoint);
        assert_eq!(stream.position(), 1);
    }

    #[test]
    fn token_stream_ext() {
        let tokens = vec![
            create_test_token(TokenType::Model),
            create_test_token(TokenType::Identifier("User".to_string())),
        ];

        let mut stream = VectorTokenStream::new(tokens);

        // Test check
        assert!(stream.check(TokenType::Model));
        assert!(!stream.check(TokenType::Enum));

        // Test match_token
        assert!(stream.match_token(TokenType::Model).is_some());
        assert!(stream.match_token(TokenType::Model).is_none()); // Should fail now

        // Test check_any
        assert!(stream.check_any(&[
            TokenType::Identifier(String::new()),
            TokenType::String
        ]));

        // Negative paths
        assert!(!stream.check(TokenType::Enum));
        assert!(stream.match_token(TokenType::Enum).is_none());
    }

    #[test]
    fn vector_stream_remaining_and_reset() {
        let tokens = vec![
            create_test_token(TokenType::Model),
            create_test_token(TokenType::Identifier("User".into())),
            create_test_token(TokenType::EOF),
        ];
        let mut s = VectorTokenStream::new(tokens);
        assert_eq!(s.remaining().len(), 3);
        let _ = s.next();
        assert_eq!(s.remaining().len(), 2);
        s.reset();
        assert_eq!(s.position(), 0);
        assert_eq!(s.remaining().len(), 3);
    }

    #[test]
    fn filtered_token_stream_hides_comments_and_restores() {
        let inner = VectorTokenStream::new(vec![
            create_test_token(TokenType::Comment(" x".into())),
            create_test_token(TokenType::Model),
            create_test_token(TokenType::DocComment(" y".into())),
            create_test_token(TokenType::Identifier("User".into())),
            create_test_token(TokenType::EOF),
        ]);
        let mut s = FilteredTokenStream::new(
            inner,
            vec![
                TokenType::Comment(" x".into()),
                TokenType::DocComment(" y".into()),
            ],
        );
        assert!(matches!(s.peek().unwrap().r#type(), TokenType::Model));
        let cp = s.checkpoint();
        let _ = s.next();
        assert!(matches!(
            s.peek().unwrap().r#type(),
            TokenType::Identifier(_)
        ));
        s.restore(cp);
        assert!(matches!(s.peek().unwrap().r#type(), TokenType::Model));
    }

    #[test]
    fn token_stream_ext_non_comment_helpers_and_sync() {
        let tokens = vec![
            create_test_token(TokenType::Comment(" a".into())),
            create_test_token(TokenType::DocComment(" b".into())),
            create_test_token(TokenType::Model),
            create_test_token(TokenType::Identifier("User".into())),
            create_test_token(TokenType::RightBrace),
        ];
        let mut s = VectorTokenStream::new(tokens);
        // peek_non_comment should see Model
        assert!(matches!(
            s.peek_non_comment().unwrap().r#type(),
            TokenType::Model
        ));
        // check_non_comment respects kind only
        assert!(s.check_non_comment(TokenType::Model));

        // synchronize_to should stop on RightBrace and return true
        let found = s.synchronize_to(&[TokenType::RightBrace]);
        assert!(found);
        assert!(matches!(s.peek().unwrap().r#type(), TokenType::RightBrace));

        // synchronize over missing token should reach end and return false
        let mut s2 =
            VectorTokenStream::new(vec![create_test_token(TokenType::Model)]);
        let ok = s2.synchronize_to(&[TokenType::RightBrace]);
        assert!(!ok);
    }

    #[test]
    fn filtered_peek_ahead_counts_only_non_filtered() {
        let inner = VectorTokenStream::new(vec![
            create_test_token(TokenType::Comment(" a".into())),
            create_test_token(TokenType::DocComment(" b".into())),
            create_test_token(TokenType::Model),
            create_test_token(TokenType::Identifier("User".into())),
            create_test_token(TokenType::LeftBrace),
        ]);
        let s = FilteredTokenStream::new(
            inner,
            vec![
                TokenType::Comment(" a".into()),
                TokenType::DocComment(" b".into()),
            ],
        );
        assert!(matches!(s.peek().unwrap().r#type(), TokenType::Model));
        // peek_ahead(1) should skip to Identifier, not LeftBrace
        assert!(matches!(
            s.peek_ahead(1).unwrap().r#type(),
            TokenType::Identifier(_)
        ));
    }

    #[test]
    fn vector_stream_is_at_end_behavior() {
        let mut s =
            VectorTokenStream::new(vec![create_test_token(TokenType::EOF)]);
        assert!(!s.is_at_end());
        let _ = s.next();
        assert!(s.is_at_end());
        assert!(s.next().is_none());
    }
}
