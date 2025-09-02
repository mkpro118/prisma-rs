//! Supervised schema parser orchestrator with progress validation.
//!
//! This orchestrator mirrors the behavior of `DefaultSchemaParser` but runs
//! each top-level declaration parse under a `ParseSupervisor` using a
//! `ProgressTrackingStream`. This allows detection of stalls and timeouts in
//! both sequential and concurrent modes without modifying existing parser
//! components.

use std::sync::Arc;
use std::sync::mpsc::{RecvTimeoutError, channel};
use std::thread;
use std::time::Instant;

use crate::core::parser::ast::{Declaration, HasSpan, Schema};
use crate::core::parser::config::{
    ConcurrencyMode, Diagnostic, ParseResult, ParserOptions,
};
use crate::core::parser::progress::{
    DefaultParseSupervisor, ParseSupervisor, ProgressOptions,
    ProgressTrackingStream,
};
use crate::core::parser::schema_parser::DeclarationParser;
use crate::core::parser::stream::VectorTokenStream;
use crate::core::parser::traits::TokenStream;
use crate::core::scanner::tokens::{
    SymbolLocation, SymbolSpan, Token, TokenType,
};

/// Builder for a supervised schema parser. It reuses factories configured on
/// the default schema parser but allows independent supervision options.
pub struct SupervisedSchemaParserBuilder {
    factories: Vec<Arc<dyn Fn() -> Box<dyn DeclarationParser> + Send + Sync>>,
    progress_options: ProgressOptions,
}

impl Default for SupervisedSchemaParserBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl SupervisedSchemaParserBuilder {
    /// Start a new builder with default supervision options.
    #[must_use]
    pub fn new() -> Self {
        Self {
            factories: Vec::new(),
            progress_options: ProgressOptions::default(),
        }
    }

    /// Inherit the default declaration parsers from `DefaultSchemaParser`'s builder.
    #[must_use]
    pub fn with_default_parsers(mut self) -> Self {
        // Reuse the same factories by constructing a default schema parser
        // builder and transferring its factories via the built parser.
        let default = crate::core::parser::schema_parser::SchemaParserBuilder::with_defaults()
            .build();
        self.factories.extend(default.factories().iter().cloned());
        self
    }

    /// Add a declaration parser factory.
    #[must_use]
    pub fn with_factory<F>(mut self, factory: F) -> Self
    where
        F: Fn() -> Box<dyn DeclarationParser> + Send + Sync + 'static,
    {
        self.factories.push(Arc::new(factory));
        self
    }

    /// Configure progress supervision options.
    #[must_use]
    pub fn with_progress_options(mut self, options: ProgressOptions) -> Self {
        self.progress_options = options;
        self
    }

    /// Build the final supervised parser.
    #[must_use]
    pub fn build(self) -> SupervisedSchemaParser {
        SupervisedSchemaParser {
            factories: self.factories,
            progress_options: self.progress_options,
        }
    }
}

/// Supervised orchestrator that validates parser progress.
pub struct SupervisedSchemaParser {
    factories: Vec<Arc<dyn Fn() -> Box<dyn DeclarationParser> + Send + Sync>>,
    progress_options: ProgressOptions,
}

impl SupervisedSchemaParser {
    /// Parse an entire schema with supervision.
    pub fn parse(
        &self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Schema> {
        // Compute top-level blocks first, similar to DefaultSchemaParser.
        let blocks = identify_blocks(stream);
        let use_concurrency = match options.concurrency {
            ConcurrencyMode::Sequential => false,
            ConcurrencyMode::Concurrent {
                max_threads,
                threshold,
            } => max_threads > 1 && blocks.len() >= threshold,
        };

        if use_concurrency {
            self.parse_concurrent(blocks)
        } else {
            self.parse_sequential(stream)
        }
    }

    fn parse_sequential(
        &self,
        stream: &mut dyn TokenStream,
    ) -> ParseResult<Schema> {
        let mut declarations: Vec<Declaration> = Vec::new();
        let mut diagnostics: Vec<Diagnostic> = Vec::new();

        while !stream.is_at_end() {
            if let Some(tok) = stream.peek()
                && matches!(tok.r#type(), TokenType::EOF)
            {
                break;
            }

            let start_pos = stream.position();
            let supervisor =
                DefaultParseSupervisor::new(&self.progress_options);
            match parse_one_block_supervised(
                &self.factories,
                stream,
                &supervisor,
                self.progress_options.report_interval,
            ) {
                Ok(result) => {
                    if let Some(decl) = result.value {
                        declarations.push(decl);
                    }
                    diagnostics.extend(result.diagnostics);
                }
                Err(diag) => {
                    diagnostics.push(diag);
                    // Best-effort sync: consume one token to avoid infinite loop.
                    if stream.position() == start_pos {
                        let _ = stream.next();
                    }
                }
            }
        }

        let span = schema_span(&declarations);
        let mut res = ParseResult::success(Schema { declarations, span });
        res.diagnostics = diagnostics;
        res
    }

    fn parse_concurrent(&self, blocks: Vec<Block>) -> ParseResult<Schema> {
        if blocks.is_empty() {
            let span = SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            };
            return ParseResult::success(Schema {
                declarations: Vec::new(),
                span,
            });
        }

        let mut handles = Vec::new();
        for block in blocks {
            let factories = self.factories.clone();
            let progress_options = self.progress_options.clone();
            // Capture a simple span from the block for diagnostics in this task.
            let block_span = block.tokens.first().map_or(
                SymbolSpan {
                    start: SymbolLocation { line: 1, column: 1 },
                    end: SymbolLocation { line: 1, column: 1 },
                },
                |t| t.span().clone(),
            );

            handles.push(thread::spawn(move || {
                let supervisor = DefaultParseSupervisor::new(&progress_options);
                let mut stream = VectorTokenStream::new(block.tokens);

                // Run in a supervised worker and return result with block index.
                let (tx, rx) = channel();
                thread::spawn(move || {
                    // Build a fresh parser set for this worker.
                    let mut parsers: Vec<Box<dyn DeclarationParser>> =
                        factories.iter().map(|f| f()).collect();
                    let res = dispatch_first_match_supervised(
                        &mut parsers,
                        &mut stream,
                        &supervisor,
                        progress_options.report_interval,
                    );
                    let _ = tx.send(res);
                });

                // Wait with timeout loop; if timeout, surface a diagnostic.
                let deadline = Instant::now() + progress_options.max_parse_time;
                loop {
                    match rx
                        .recv_timeout(progress_options.progress_check_interval)
                    {
                        Ok(res) => return (block.index, res),
                        Err(RecvTimeoutError::Timeout) => {
                            if Instant::now() >= deadline {
                                let diag = Diagnostic::error(
                                    block_span.clone(),
                                    "Parser stalled without making progress",
                                );
                                let r: ParseResult<Declaration> =
                                    ParseResult::error(diag);
                                return (block.index, r);
                            }
                        }
                        Err(RecvTimeoutError::Disconnected) => {
                            // Worker panicked; report error.
                            let diag = Diagnostic::error(
                                block_span.clone(),
                                "Worker thread terminated unexpectedly",
                            );
                            let r: ParseResult<Declaration> =
                                ParseResult::error(diag);
                            return (block.index, r);
                        }
                    }
                }
            }));
        }

        let mut pairs: Vec<(usize, ParseResult<Declaration>)> = Vec::new();
        for h in handles {
            if let Ok(pair) = h.join() {
                pairs.push(pair);
            } else {
                let r: ParseResult<Declaration> =
                    ParseResult::error(Diagnostic::error(
                        SymbolSpan {
                            start: SymbolLocation { line: 1, column: 1 },
                            end: SymbolLocation { line: 1, column: 1 },
                        },
                        "Worker join failed",
                    ));
                pairs.push((usize::MAX, r));
            }
        }

        pairs.sort_by_key(|(i, _)| *i);
        let mut declarations = Vec::new();
        let mut diagnostics = Vec::new();
        for (_, r) in pairs {
            if let Some(d) = r.value {
                declarations.push(d);
            }
            diagnostics.extend(r.diagnostics);
        }
        let span = schema_span(&declarations);
        let mut res = ParseResult::success(Schema { declarations, span });
        res.diagnostics = diagnostics;
        res
    }
}

/// Identify top-level declaration blocks and return their token slices as vectors.
fn identify_blocks(stream: &mut dyn TokenStream) -> Vec<Block> {
    let mut blocks = Vec::new();
    let mut index = 0usize;
    while !stream.is_at_end() {
        // Skip doc/comments before a block boundary, but keep them as part of block.
        let start_pos = stream.position();
        let start_tok = match stream.peek() {
            Some(t) => t.clone(),
            None => break,
        };
        // Top-level starts are keywords known at schema level.
        let is_start = matches!(
            start_tok.r#type(),
            TokenType::Model
                | TokenType::Enum
                | TokenType::DataSource
                | TokenType::Generator
                | TokenType::Type
        );
        if !is_start {
            // Consume one token to avoid getting stuck and continue.
            let _ = stream.next();
            continue;
        }
        // Collect tokens until matching closing brace at depth 0 or EOF.
        let mut depth: i32 = 0;
        let mut tokens = Vec::<Token>::new();
        // Push the starting token as part of block
        if let Some(t) = stream.next() {
            tokens.push(t);
        } else {
            break;
        }
        while let Some(tok) = stream.peek().cloned() {
            match tok.r#type() {
                TokenType::LeftBrace => {
                    depth += 1;
                    if let Some(t) = stream.next() {
                        tokens.push(t);
                    } else {
                        break;
                    }
                }
                TokenType::RightBrace => {
                    if let Some(t) = stream.next() {
                        tokens.push(t);
                    } else {
                        break;
                    }
                    depth -= 1;
                    if depth < 0 {
                        break;
                    }
                }
                TokenType::EOF => {
                    if let Some(t) = stream.next() {
                        tokens.push(t);
                    }
                    break;
                }
                _ => {
                    if let Some(t) = stream.next() {
                        tokens.push(t);
                    } else {
                        break;
                    }
                }
            }
        }
        blocks.push(Block { index, tokens });
        index += 1;
        // Safety valve: if we didn't advance, avoid infinite loop.
        if stream.position() == start_pos {
            let _ = stream.next();
        }
    }
    blocks
}

/// Dispatch using first-match-wins strategy under supervision.
fn dispatch_first_match_supervised(
    parsers: &mut [Box<dyn DeclarationParser>],
    stream: &mut dyn TokenStream,
    supervisor: &dyn ParseSupervisor,
    report_interval: usize,
) -> ParseResult<Declaration> {
    for p in parsers.iter_mut() {
        if p.can_parse(stream) {
            let mut progress_stream = ProgressTrackingStream::new(
                stream,
                supervisor,
                0,
                report_interval,
            );
            return p.parse(&mut progress_stream, &ParserOptions::default());
        }
    }
    let span = stream.peek().map_or(
        SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation { line: 1, column: 1 },
        },
        |t| t.span().clone(),
    );
    ParseResult::error(Diagnostic::error(
        span,
        "Unexpected token - expected top-level declaration",
    ))
}

/// Parse a single declaration from the shared sequential stream under supervision.
fn parse_one_block_supervised(
    factories: &[Arc<dyn Fn() -> Box<dyn DeclarationParser> + Send + Sync>],
    stream: &mut dyn TokenStream,
    supervisor: &dyn ParseSupervisor,
    report_interval: usize,
) -> Result<ParseResult<Declaration>, Diagnostic> {
    let mut parsers: Vec<Box<dyn DeclarationParser>> =
        factories.iter().map(|f| f()).collect();

    // Try to find a parser first to avoid work for clearly invalid tokens.
    let mut selected: Option<usize> = None;
    for (i, p) in parsers.iter().enumerate() {
        if p.can_parse(stream) {
            selected = Some(i);
            break;
        }
    }
    if selected.is_none() {
        let span = stream.peek().map_or(
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            },
            |t| t.span().clone(),
        );
        return Err(Diagnostic::error(
            span,
            "Unexpected token - expected top-level declaration",
        ));
    }
    let Some(idx) = selected else { unreachable!() };
    // Parse directly in the current thread with progress tracking; this
    // avoids unsafe sharing of the sequential stream across threads.
    let mut tracking =
        ProgressTrackingStream::new(stream, supervisor, 0, report_interval);
    Ok(parsers[idx].parse(&mut tracking, &ParserOptions::default()))
}

#[derive(Debug)]
struct Block {
    index: usize,
    tokens: Vec<Token>,
}

fn schema_span(decls: &[Declaration]) -> SymbolSpan {
    if let (Some(first), Some(last)) = (decls.first(), decls.last()) {
        let s = first.span();
        let e = last.span();
        return SymbolSpan {
            start: s.start.clone(),
            end: e.end.clone(),
        };
    }
    SymbolSpan {
        start: SymbolLocation { line: 1, column: 1 },
        end: SymbolLocation { line: 1, column: 1 },
    }
}
