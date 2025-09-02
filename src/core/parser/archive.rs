//! Serialize and deserialize parsed AST and diagnostics to a stable ASCII archive.
//!
//! This module defines a line-oriented text format for persisting the parser's
//! observable outputs — a `Schema` AST and parse diagnostics — so that later
//! stages (e.g., semantic analysis) can be resumed without reparsing tokens.
//! The format is architecture-independent and uses ASCII with simple escapes.
//!
//! The archive captures exactly what downstream needs: the complete AST in
//! source order with 1-based spans and doc comments, and all diagnostics with
//! severities and messages.
//!
//! Format sketch (sections):
//!
//! HDR\tPRPA1\tversion=1\tencoding=ascii-escape\tgrammar=v1
//! BEGIN\tAST
//!   AST\tSchema\tDECLS=<N>\tSL\tSC\tEL\tEC
//!   ... N declaration subtrees ...
//! END\tAST
//! BEGIN\tDIAGNOSTICS
//!   DIAG\tSEV=<Info|Warning|Error>\tSL\tSC\tEL\tEC\tMSG=<text>
//! END\tDIAGNOSTICS
//! EOF
//!
//! Node encodings follow the structure from `src/core/parser/ast/mod.rs`.
//! Strings use C-like escapes: `\n`, `\r`, `\t`, `\\`, `\"`, and `\uXXXX`.
//!
//! ## Examples
//! ```text
//! HDR\tPRPA1\tversion=1\tencoding=ascii-escape\tgrammar=v1
//! BEGIN\tAST
//! AST\tSchema\tDECLS=1\t1\t1\t1\t13
//! AST\tDecl\tModel
//! AST\tModelDecl\tNAME=...\tMEMBERS=0\tATTRS=0\tDOCS=0\t1\t1\t1\t13
//! END\tAST
//! BEGIN\tDIAGNOSTICS
//! END\tDIAGNOSTICS
//! EOF
//! ```

use crate::core::parser::ast::Schema;
use crate::core::parser::config::Diagnostic;

/// Hold a complete, serialized view of parser outputs.
#[derive(Debug, Clone)]
pub struct SchemaArchive {
    /// Format version (currently 1).
    pub version: u32,
    /// Grammar version tag (e.g., "v1").
    pub grammar: String,
    /// The parsed AST in source order with spans.
    pub schema: Schema,
    /// Parse diagnostics emitted during parsing.
    pub diagnostics: Vec<Diagnostic>,
}

impl SchemaArchive {
    /// Create a new archive with version 1 and `v1` grammar tag.
    #[must_use]
    pub fn new(schema: Schema, diagnostics: Vec<Diagnostic>) -> Self {
        Self {
            version: 1,
            grammar: "v1".to_string(),
            schema,
            diagnostics,
        }
    }
}

/// Write a schema archive to a writer using the PRPA1 text format.
///
/// The writer receives a header line, `AST` section, `DIAGNOSTICS` section,
/// and terminal `EOF`. Strings are escaped so the output is ASCII-only.
///
/// ## Errors
/// Returns an I/O error if writing to the underlying writer fails.
pub fn write_schema_archive_to_writer(
    _w: &mut dyn std::io::Write,
    _schema: &Schema,
    _diagnostics: &[Diagnostic],
) -> std::io::Result<()> {
    // Scaffold: implementation to be added in a follow-up.
    unimplemented!("writer implementation not yet provided");
}

/// Write a schema archive to the specified filesystem path.
///
/// Creates or truncates the file at `path` and writes the PRPA1 archive.
/// Buffers writes internally for efficiency.
///
/// ## Errors
/// Returns an I/O error if the file cannot be created or written.
pub fn write_schema_archive_to_path(
    _path: &std::path::Path,
    _schema: &Schema,
    _diagnostics: &[Diagnostic],
) -> std::io::Result<()> {
    // Scaffold: implementation to be added in a follow-up.
    unimplemented!("writer implementation not yet provided");
}

/// Read a schema archive from a buffered reader.
///
/// Parses PRPA1 records line-by-line and reconstructs a `Schema` tree and
/// parse diagnostics.
///
/// ## Errors
/// Returns an I/O error if reading fails. Parse errors will also be surfaced
/// as I/O errors with a descriptive message in the final implementation.
pub fn read_schema_archive_from_reader(
    _r: &mut dyn std::io::BufRead,
) -> std::io::Result<SchemaArchive> {
    // Scaffold: implementation to be added in a follow-up.
    unimplemented!("reader implementation not yet provided");
}

/// Read a schema archive from a filesystem path.
///
/// Opens the file, wraps it in a buffered reader, and delegates to
/// `read_schema_archive_from_reader`.
///
/// ## Errors
/// Returns an I/O error if the file cannot be opened or the contents are
/// malformed (in the final implementation).
pub fn read_schema_archive_from_path(
    _path: &std::path::Path,
) -> std::io::Result<SchemaArchive> {
    // Scaffold: implementation to be added in a follow-up.
    unimplemented!("reader implementation not yet provided");
}

/// Escape a string for ASCII-only output (scaffold).
#[must_use]
pub fn escape_str(_s: &str) -> String {
    // Scaffold placeholder
    String::new()
}

/// Unescape a previously escaped string (scaffold).
///
/// ## Errors
/// Returns an I/O error in the final implementation when the escape
/// sequences are malformed.
pub fn unescape_str(_s: &str) -> std::io::Result<String> {
    // Scaffold placeholder
    unimplemented!("escape parser not yet provided");
}
