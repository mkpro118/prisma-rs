//! Serialize and deserialize lexer outputs to a stable ASCII archive.
//!
//! This module defines a line-oriented text format for persisting the
//! lexer's observable outputs — tokens and lexical diagnostics — so that
//! later stages can be resumed without re-scanning the original input.
//! The format is architecture-independent and uses only ASCII with simple
//! backslash escapes for payload strings.
//!
//! The archive captures exactly what the parser needs:
//! token kinds, payload text for stringly tokens, precise 1-based spans,
//! and a single `EOF` at the end. Lexical errors can also be recorded.
//!
//! Format sketch (one record per line):
//!
//! HDR\tPRLX1\tversion=1\tencoding=ascii-escape\tsha256=<hex-or-empty>
//! TOK\t<KIND>\t<SL>\t<SC>\t<EL>\t<EC>[\t<PAYLOAD>]
//! ERR\t<MESSAGE>\t<SL>\t<SC>\t<EL>\t<EC>
//! TOK\tEOF\t<SL>\t<SC>\t<EL>\t<EC>
//! EOF
//!
//! KIND is the textual `TokenType` variant name. PAYLOAD is present only
//! for `Literal`, `Identifier`, `Comment`, `DocComment`, and `Unsupported`.
//! Spans use 1-based line/column. Strings use C-like escapes: `\n`, `\r`,
//! `\t`, `\\`, `\"`, and `\uXXXX` for non-ASCII scalars.
//!
//! The header optionally carries a source SHA-256 to validate caches.
//!
//! ## Examples
//! ```text
//! HDR\tPRLX1\tversion=1\tencoding=ascii-escape\tsha256=
//! TOK\tModel\t1\t1\t1\t5
//! TOK\tIdentifier\t1\t7\t1\t10\tUser
//! TOK\tLeftBrace\t1\t12\t1\t12
//! TOK\tRightBrace\t1\t13\t1\t13
//! TOK\tEOF\t1\t14\t1\t14
//! EOF
//! ```

use crate::core::scanner::lexer::LexError;
use crate::core::scanner::tokens::Token;

/// Hold a complete, serialized view of lexer outputs.
#[derive(Debug, Clone)]
pub struct TokenArchive {
    /// Format version (currently 1).
    pub version: u32,
    /// Optional SHA-256 (hex) of the original source bytes.
    pub source_sha256_hex: Option<String>,
    /// All tokens in emission order (including exactly one EOF at end).
    pub tokens: Vec<Token>,
    /// Lexical errors encountered while scanning, if any.
    pub errors: Vec<LexError>,
}

impl TokenArchive {
    /// Create an empty archive with version 1.
    #[must_use]
    pub fn new() -> Self {
        Self {
            version: 1,
            source_sha256_hex: None,
            tokens: Vec::new(),
            errors: Vec::new(),
        }
    }
}

impl Default for TokenArchive {
    fn default() -> Self {
        Self::new()
    }
}

/// Write a token archive to a writer using the PRLX1 text format.
///
/// The writer receives a header line followed by `TOK` and `ERR` records
/// and a terminal `EOF` record. Strings are escaped so the output is
/// ASCII-only regardless of input contents.
///
/// ## Errors
/// Returns an I/O error if writing to the underlying writer fails.
pub fn write_token_archive_to_writer(
    _w: &mut dyn std::io::Write,
    _src_sha256_hex: Option<&str>,
    _tokens: &[Token],
    _errors: &[LexError],
) -> std::io::Result<()> {
    // Scaffold: implementation to be added in a follow-up.
    unimplemented!("writer implementation not yet provided");
}

/// Write a token archive to the specified filesystem path.
///
/// Creates or truncates the file at `path` and writes the PRLX1 archive.
/// Buffers writes internally for efficiency.
///
/// ## Errors
/// Returns an I/O error if the file cannot be created or written.
pub fn write_token_archive_to_path(
    _path: &std::path::Path,
    _src_sha256_hex: Option<&str>,
    _tokens: &[Token],
    _errors: &[LexError],
) -> std::io::Result<()> {
    // Scaffold: implementation to be added in a follow-up.
    unimplemented!("writer implementation not yet provided");
}

/// Read a token archive from a buffered reader.
///
/// Parses PRLX1 records line-by-line and reconstructs `Token` and `LexError`
/// values. Unknown token kinds should be mapped to `Unsupported` in the
/// eventual implementation.
///
/// ## Errors
/// Returns an I/O error if reading fails. Parse errors will also be surfaced
/// as I/O errors with a descriptive message in the final implementation.
pub fn read_token_archive_from_reader(
    _r: &mut dyn std::io::BufRead,
) -> std::io::Result<TokenArchive> {
    // Scaffold: implementation to be added in a follow-up.
    unimplemented!("reader implementation not yet provided");
}

/// Read a token archive from a filesystem path.
///
/// Opens the file, wraps it in a buffered reader, and delegates to
/// `read_token_archive_from_reader`.
///
/// ## Errors
/// Returns an I/O error if the file cannot be opened or the contents are
/// malformed (in the final implementation).
pub fn read_token_archive_from_path(
    _path: &std::path::Path,
) -> std::io::Result<TokenArchive> {
    // Scaffold: implementation to be added in a follow-up.
    unimplemented!("reader implementation not yet provided");
}

/// Escape a string for ASCII-only output (scaffold).
///
/// The final implementation will encode control characters and non-ASCII
/// scalars using `\uXXXX` escapes, and backslash-escape `\n`, `\r`, `\t`,
/// `\\`, and `\"`.
#[must_use]
pub fn escape_str(_s: &str) -> String {
    // Scaffold placeholder
    String::new()
}

/// Unescape a previously escaped string (scaffold).
///
/// The final implementation will parse `\uXXXX` sequences and the common
/// escape sequences back into a UTF-8 string.
///
/// ## Errors
/// Returns an I/O error in the final implementation when the escape
/// sequences are malformed.
pub fn unescape_str(_s: &str) -> std::io::Result<String> {
    // Scaffold placeholder
    unimplemented!("escape parser not yet provided");
}

/// Convert a token type into its stable textual key (scaffold).
#[must_use]
pub fn token_type_to_key(
    _t: &crate::core::scanner::tokens::TokenType,
) -> &'static str {
    // Scaffold placeholder
    "UNSUPPORTED"
}

/// Convert a textual key with optional payload into a `TokenType` (scaffold).
///
/// Unknown keys should map to `TokenType::Unsupported` in the final
/// implementation so archives remain forward-compatible.
///
/// ## Errors
/// Returns an I/O error in the final implementation when the key or payload
/// is malformed and cannot be converted into a supported token type.
pub fn token_type_from_key(
    _key: &str,
    _payload: Option<String>,
) -> std::io::Result<crate::core::scanner::tokens::TokenType> {
    // Scaffold placeholder
    unimplemented!("key-to-token converter not yet provided");
}
