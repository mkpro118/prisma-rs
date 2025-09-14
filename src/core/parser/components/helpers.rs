//! Helper functions for parsing common patterns.
//!
//! Utilities shared across parser components, primarily for associating
//! documentation comments with subsequent declarations. Spans are preserved
//! and comments are treated according to the scanner’s guarantees.

use crate::core::parser::ast::Docs;
use crate::core::parser::traits::TokenStream;
use crate::core::scanner::tokens::{
    SymbolLocation, SymbolSpan, Token, TokenType,
};

/// Build a span that goes from the start of `a` to the end of `b`.
pub(crate) fn span_from_to(a: &SymbolSpan, b: &SymbolSpan) -> SymbolSpan {
    SymbolSpan {
        start: SymbolLocation {
            line: a.start.line,
            column: a.start.column,
        },
        end: SymbolLocation {
            line: b.end.line,
            column: b.end.column,
        },
    }
}

/// Extract documentation text from a `DocComment` token.
///
/// Given a `DocComment` token whose text is the content after the `///`
/// marker, remove at most one leading space. Preserve all other whitespace.
#[must_use]
pub fn extract_doc_text(token: &Token) -> Option<String> {
    if let TokenType::DocComment(text) = token.r#type() {
        if let Some(rest) = text.strip_prefix(' ') {
            Some(rest.to_string())
        } else {
            Some(text.to_string())
        }
    } else {
        None
    }
}

/// Parse leading documentation comments from the stream.
///
/// Greedily consumes consecutive `DocComment` tokens at the current position
/// and returns a single `Docs` node with the collected lines and combined
/// span. If no doc comments are present, returns `None` and does not
/// advance the stream.
///
/// ## Examples
/// ```
/// # use prisma_rs::core::parser::components::helpers::parse_leading_docs;
/// # use prisma_rs::core::parser::stream::VectorTokenStream;
/// # use prisma_rs::core::parser::traits::TokenStream;
/// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
/// let mut s = VectorTokenStream::new(vec![
///     Token::new(TokenType::DocComment("User model".into()), (1,1), (1,1)),
///     Token::new(TokenType::DocComment("for auth".into()), (1,2), (1,2)),
///     Token::new(TokenType::Model, (1,3), (1,7)),
/// ]);
/// let docs = parse_leading_docs(&mut s).expect("should collect docs");
/// assert_eq!(docs.lines, vec!["User model", "for auth"]);
/// assert!(matches!(s.peek().unwrap().r#type(), TokenType::Model));
/// ```
pub fn parse_leading_docs(stream: &mut dyn TokenStream) -> Option<Docs> {
    let mut doc_lines = Vec::new();
    let mut first_span: Option<SymbolSpan> = None;
    let mut last_span: Option<SymbolSpan> = None;

    // Greedily consume all consecutive DocComment tokens
    while let Some(token) = stream.peek() {
        if matches!(token.r#type(), TokenType::DocComment(_)) {
            // Safe to consume since we peeked and confirmed it's a DocComment
            // This should never panic since we just checked with peek()
            if let Some(doc_token) = stream.next() {
                // Track spans for the overall Docs span
                if first_span.is_none() {
                    first_span = Some(doc_token.span().clone());
                }
                last_span = Some(doc_token.span().clone());

                // Extract and store the documentation text
                if let Some(doc_text) = extract_doc_text(&doc_token) {
                    doc_lines.push(doc_text);
                }
            }
        } else {
            // Hit a non-DocComment token, stop consuming
            break;
        }
    }

    // If we found any documentation comments, create a Docs node
    if doc_lines.is_empty() {
        None
    } else {
        let span = match (first_span, last_span) {
            (Some(first), Some(last)) => span_from_to(&first, &last),
            (Some(single), None) => single, // Should not happen, but handle gracefully
            _ => {
                // This should never happen if doc_lines is not empty
                SymbolSpan {
                    start: SymbolLocation { line: 0, column: 0 },
                    end: SymbolLocation { line: 0, column: 0 },
                }
            }
        };

        Some(Docs {
            lines: doc_lines,
            span,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::parser::stream::VectorTokenStream;

    fn tok(t: TokenType) -> Token {
        Token::new(t, (1, 1), (1, 1))
    }

    #[test]
    fn extract_doc_text_variants() {
        let t = tok(TokenType::DocComment(" hello".into()));
        assert_eq!(extract_doc_text(&t).unwrap(), "hello");
        let t = tok(TokenType::DocComment("plain".into()));
        assert_eq!(extract_doc_text(&t).unwrap(), "plain");
        let t = tok(TokenType::Comment(" not-doc".into()));
        assert!(extract_doc_text(&t).is_none());
    }

    #[test]
    fn extract_doc_text_removes_only_one_space() {
        let t = tok(TokenType::DocComment("   many spaces".into()));
        // Only the first leading space is removed; remaining preserved
        assert_eq!(extract_doc_text(&t).unwrap(), "  many spaces");
    }

    #[test]
    fn extract_doc_text_preserves_tabs_and_other_whitespace() {
        let t = tok(TokenType::DocComment("\tTabbed doc".into()));
        // Not a space prefix, so unchanged
        assert_eq!(extract_doc_text(&t).unwrap(), "\tTabbed doc");
    }

    #[test]
    fn parse_leading_docs_none_and_some() {
        // None path (no docs)
        let mut s = VectorTokenStream::new(vec![tok(TokenType::Model)]);
        assert!(parse_leading_docs(&mut s).is_none());

        // Some path with multiple lines
        let mut s = VectorTokenStream::new(vec![
            tok(TokenType::DocComment(" line1".into())),
            tok(TokenType::DocComment(" line2".into())),
            tok(TokenType::Enum),
        ]);
        let d = parse_leading_docs(&mut s).unwrap();
        assert_eq!(d.lines, vec!["line1", "line2"]);
        assert!(matches!(s.peek().unwrap().r#type(), TokenType::Enum));
    }
}
