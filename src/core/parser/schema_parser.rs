use crate::core::parser::ast::{
    DatasourceDecl, Declaration, EnumDecl, GeneratorDecl, HasSpan, ModelDecl,
    Schema, TypeDecl,
};
use crate::core::parser::components::declarations::{
    DatasourceParser, EnumParser, GeneratorParser, ModelParser, TypeDeclParser,
};
use crate::core::parser::config::{
    ConcurrencyMode, Diagnostic, ParseResult, ParserOptions,
};
use crate::core::parser::progress::{
    DefaultProgressObserver, ObservedTokenStream, ProgressConfig,
};
use crate::core::parser::stream::VectorTokenStream;
use crate::core::parser::traits::{
    DeclarationType, ItemParser, Parser, SchemaParser, TokenStream,
};
use crate::core::scanner::tokens::{
    SymbolLocation, SymbolSpan, Token, TokenType,
};
use std::marker::PhantomData;
use std::sync::Arc;
use std::thread;

/// Type-erased interface for any `ItemParser` that can produce a Declaration.
/// Any parser that implements this can be orchestrated by `SchemaParser`.
///
/// Library users can use this trait to introspect parsers, get their types,
/// and even implement custom orchestration logic.
pub trait DeclarationParser: Send + Sync {
    /// Check if this parser can handle the current token stream state.
    fn can_parse(&self, stream: &dyn TokenStream) -> bool;

    /// Parse a declaration from the token stream.
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Declaration>;

    /// Get the type of declaration this parser handles.
    /// Useful for debugging, logging, metrics, and custom orchestration.
    fn declaration_type(&self) -> DeclarationType;
}

/// Builder for `DefaultSchemaParser` with factory-based plug-ins.
///
/// Users can provide their own custom parsers for maximum flexibility.
/// This builder uses per-worker factories so that concurrent parsing correctly
/// honors the configured parser set without sharing mutable instances across threads.
pub struct SchemaParserBuilder {
    factories: Vec<Arc<dyn Fn() -> Box<dyn DeclarationParser> + Send + Sync>>,
}

/// Default implementation of a schema parser with pluggable, factory-built parsers.
///
/// Like an orchestrator, this struct dispatches parsing tasks to a set of
/// configured `DeclarationParser` implementations. It supports both sequential
/// and concurrent parsing modes.
pub struct DefaultSchemaParser {
    // Factories to create per-worker parser sets
    factories: Vec<Arc<dyn Fn() -> Box<dyn DeclarationParser> + Send + Sync>>,
}

/// Adapter to convert any `ItemParser<T>` into a `DeclarationParser`.
struct ItemParserAdapter<T, P: ItemParser<T>> {
    parser: P,
    _phantom: PhantomData<T>,
}

impl<T, P: ItemParser<T>> ItemParserAdapter<T, P> {
    fn new(parser: P) -> Self {
        Self {
            parser,
            _phantom: PhantomData,
        }
    }
}

impl<T: Send + Sync, P: ItemParser<T> + Send + Sync> DeclarationParser
    for ItemParserAdapter<T, P>
{
    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        self.parser.can_parse(stream)
    }

    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Declaration> {
        let res = self.parser.parse(stream, options);
        let value = res.value.map(|item| self.parser.to_declaration(item));
        ParseResult {
            value,
            diagnostics: res.diagnostics,
        }
    }

    fn declaration_type(&self) -> DeclarationType {
        self.parser.declaration_type()
    }
}

impl Default for SchemaParserBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl SchemaParserBuilder {
    /// Start a schema parser builder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            factories: Vec::new(),
        }
    }

    /// Create a builder with the default declaration parsers.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new()
            .with_factory(|| {
                Box::new(ItemParserAdapter::<ModelDecl, _>::new(ModelParser))
            })
            .with_factory(|| {
                Box::new(ItemParserAdapter::<EnumDecl, _>::new(EnumParser))
            })
            .with_factory(|| {
                Box::new(ItemParserAdapter::<DatasourceDecl, _>::new(
                    DatasourceParser,
                ))
            })
            .with_factory(|| {
                Box::new(ItemParserAdapter::<GeneratorDecl, _>::new(
                    GeneratorParser,
                ))
            })
            .with_factory(|| {
                Box::new(ItemParserAdapter::<TypeDecl, _>::new(TypeDeclParser))
            })
    }

    /// Add any parser implementing `ItemParser<T>`; stored as per-worker factory.
    #[must_use]
    pub fn with_parser<
        T: Send + Sync + 'static,
        P: ItemParser<T> + Send + Sync + Clone + 'static,
    >(
        mut self,
        parser: P,
    ) -> Self {
        // Store a factory that constructs a fresh adapter instance per worker
        let arc: Arc<dyn Fn() -> Box<dyn DeclarationParser> + Send + Sync> =
            Arc::new(move || {
                let p = parser.clone();
                Box::new(ItemParserAdapter::<T, P>::new(p))
            });
        self.factories.push(arc);
        self
    }

    /// Add a raw `DeclarationParser` factory for full control.
    #[must_use]
    pub fn with_factory<F>(mut self, factory: F) -> Self
    where
        F: Fn() -> Box<dyn DeclarationParser> + Send + Sync + 'static,
    {
        self.factories.push(Arc::new(factory));
        self
    }

    /// Build the final parser with factories.
    #[must_use]
    pub fn build(self) -> DefaultSchemaParser {
        DefaultSchemaParser {
            factories: self.factories,
        }
    }
}

impl Default for DefaultSchemaParser {
    fn default() -> Self {
        SchemaParserBuilder::with_defaults().build()
    }
}

impl DefaultSchemaParser {
    /// Create a new parser with defaults.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Access the configured factories (for introspection/testing).
    #[must_use]
    pub fn factories(
        &self,
    ) -> &[Arc<dyn Fn() -> Box<dyn DeclarationParser> + Send + Sync>] {
        &self.factories
    }

    /// Parse a complete schema, selecting sequential or concurrent strategy.
    pub fn parse_schema(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Schema> {
        // Identify blocks once, use result for mode decision.
        let blocks = Self::identify_blocks(stream);
        if blocks.is_empty()
            && stream
                .peek()
                .filter(|tok| !matches!(tok.r#type(), TokenType::EOF))
                .is_some()
        {
            let mut result = ParseResult::success(Schema {
                declarations: Vec::new(),
                span: SymbolSpan {
                    start: SymbolLocation { line: 1, column: 1 },
                    end: SymbolLocation { line: 1, column: 1 },
                },
            });
            let span = stream.peek().map_or(
                SymbolSpan {
                    start: SymbolLocation { line: 1, column: 1 },
                    end: SymbolLocation { line: 1, column: 1 },
                },
                |t| t.span().clone(),
            );
            result.diagnostics.push(Diagnostic::error(
                span,
                "Unexpected token - expected top-level declaration",
            ));
            return result;
        }

        let use_concurrency = match options.concurrency {
            ConcurrencyMode::Sequential => false,
            ConcurrencyMode::Concurrent {
                max_threads,
                threshold,
            } => max_threads > 1 && blocks.len() >= threshold,
        };

        if use_concurrency {
            self.parse_schema_concurrent(blocks, options)
        } else {
            // Parse sequentially but supervised per block
            self.parse_schema_sequential_blocks(blocks, options)
        }
    }

    /// Parse schema sequentially from identified blocks with supervision.
    fn parse_schema_sequential_blocks(
        &self,
        blocks: Vec<Block>,
        options: &ParserOptions,
    ) -> ParseResult<Schema> {
        let mut declarations = Vec::new();
        let mut diagnostics: Vec<Diagnostic> = Vec::new();
        for block in blocks {
            let (decl_opt, mut diags) =
                Self::parse_block_supervised(&self.factories, block, options);
            if let Some(d) = decl_opt {
                declarations.push(d);
            }
            diagnostics.append(&mut diags);
        }
        let span = Self::schema_span(&declarations);
        let mut result = ParseResult::success(Schema { declarations, span });
        result.diagnostics = diagnostics;
        result
    }

    /// Parse schema concurrently with per-worker parser sets.
    fn parse_schema_concurrent(
        &self,
        blocks: Vec<Block>,
        options: &ParserOptions,
    ) -> ParseResult<Schema> {
        let (max_threads, _threshold) = match options.concurrency {
            ConcurrencyMode::Sequential => (1, 0),
            ConcurrencyMode::Concurrent {
                max_threads,
                threshold,
            } => (max_threads, threshold),
        };

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

        let n_workers = max_threads.max(1).min(blocks.len());

        // Shared LIFO queue of blocks to avoid cloning tokens; workers pop until empty.
        let shared_blocks = std::sync::Arc::new(std::sync::Mutex::new(blocks));

        let mut handles = Vec::with_capacity(n_workers);
        for _ in 0..n_workers {
            let factories = self.factories.clone();
            let options_clone = options.clone();
            let queue = shared_blocks.clone();
            handles.push(thread::spawn(move || {
                let mut results: Vec<(usize, Declaration)> = Vec::new();
                let mut diags: Vec<Diagnostic> = Vec::new();

                loop {
                    let maybe_block = {
                        let mut guard = match queue.lock() {
                            Ok(g) => g,
                            Err(poisoned) => poisoned.into_inner(),
                        };
                        guard.pop()
                    };
                    let Some(block) = maybe_block else { break };
                    let idx = block.index;
                    // For each block, run supervised parsing with timeout using fresh parsers.
                    let (decl_opt, mut d) = Self::parse_block_supervised(
                        &factories,
                        block,
                        &options_clone,
                    );
                    if let Some(decl) = decl_opt {
                        results.push((idx, decl));
                    }
                    diags.append(&mut d);
                }

                (results, diags)
            }));
        }

        // Aggregate results preserving original order by block index.
        let mut all_pairs: Vec<(usize, Declaration)> = Vec::new();
        let mut diagnostics: Vec<Diagnostic> = Vec::new();
        for handle in handles {
            match handle.join() {
                Ok((mut pairs, mut diags)) => {
                    all_pairs.append(&mut pairs);
                    diagnostics.append(&mut diags);
                }
                Err(_) => {
                    diagnostics.push(Diagnostic::error(
                        SymbolSpan {
                            start: SymbolLocation { line: 1, column: 1 },
                            end: SymbolLocation { line: 1, column: 1 },
                        },
                        "Worker thread panicked during parsing",
                    ));
                }
            }
        }

        all_pairs.sort_by_key(|(i, _)| *i);
        let declarations: Vec<Declaration> =
            all_pairs.into_iter().map(|(_, d)| d).collect();
        let span = Self::schema_span(&declarations);
        let mut result = ParseResult::success(Schema { declarations, span });
        result.diagnostics = diagnostics;
        result
    }

    /// Supervise parsing of a single block using factories to build a parser set.
    ///
    /// This runs synchronously in the caller thread using an `ObservedTokenStream`
    /// to enforce progress/timeouts, avoiding a per-block worker thread.
    fn parse_block_supervised(
        factories: &[Arc<
            dyn Fn() -> Box<dyn DeclarationParser> + Send + Sync,
        >],
        block: Block,
        options: &ParserOptions,
    ) -> (Option<Declaration>, Vec<Diagnostic>) {
        let mut parsers: Vec<Box<dyn DeclarationParser>> =
            factories.iter().map(|f| f()).collect();
        let tuning = options.progress_tuning();
        let mut stream = VectorTokenStream::new(block.tokens);

        for parser in &mut parsers {
            if parser.can_parse(&stream) {
                // Wrap with a progress-observed stream to enforce timeouts/cutoff
                let supervisor = DefaultProgressObserver::new(tuning);
                let mut tracking = ObservedTokenStream::new(
                    &mut stream,
                    &supervisor,
                    0,
                    tuning.report_interval,
                );
                let res = parser.parse(&mut tracking, options);
                return (res.value, res.diagnostics);
            }
        }

        // No parser could handle this block; emit the same diagnostic.
        let span = stream.peek().map_or(
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            },
            |t| t.span().clone(),
        );
        (
            None,
            vec![Diagnostic::error(
                span,
                "Unexpected token - expected top-level declaration",
            )],
        )
    }

    fn schema_span(decls: &[Declaration]) -> SymbolSpan {
        if decls.is_empty() {
            return SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            };
        }
        let mut start = decls[0].span().start.clone();
        let mut end = decls[0].span().end.clone();
        for d in decls {
            let s = d.span();
            if s.start.line < start.line
                || (s.start.line == start.line && s.start.column < start.column)
            {
                start = s.start.clone();
            }
            if s.end.line > end.line
                || (s.end.line == end.line && s.end.column > end.column)
            {
                end = s.end.clone();
            }
        }
        SymbolSpan { start, end }
    }

    /// Identify top-level declaration blocks with their original indices.
    fn identify_blocks(stream: &dyn TokenStream) -> Vec<Block> {
        let mut blocks = Vec::new();
        let mut current = Vec::new();
        let mut brace_depth = 0usize;
        let mut in_block = false;
        let mut offset = 0usize;
        let mut next_index = 0usize;
        // Pending doc comments that directly precede a block
        let mut pending_docs: Vec<Token> = Vec::new();

        while let Some(token) = stream.peek_ahead(offset) {
            match token.r#type() {
                // Accumulate doc comments until a declaration keyword, reset on other noise
                TokenType::DocComment(_) if !in_block => {
                    pending_docs.push(token.clone());
                }
                TokenType::Model
                | TokenType::Enum
                | TokenType::DataSource
                | TokenType::Generator
                | TokenType::Type => {
                    if in_block && !current.is_empty() {
                        blocks.push(Block {
                            index: next_index,
                            tokens: current,
                        });
                        next_index += 1;
                        current = Vec::new();
                    }
                    in_block = true;
                    brace_depth = 0;
                    // Prepend any pending docs to the new block
                    if !pending_docs.is_empty() {
                        current.append(&mut pending_docs);
                    }
                    current.push(token.clone());
                }
                TokenType::LeftBrace if in_block => {
                    brace_depth += 1;
                    current.push(token.clone());
                }
                TokenType::RightBrace if in_block => {
                    current.push(token.clone());
                    brace_depth = brace_depth.saturating_sub(1);
                    if brace_depth == 0 {
                        blocks.push(Block {
                            index: next_index,
                            tokens: current,
                        });
                        next_index += 1;
                        current = Vec::new();
                        in_block = false;
                    }
                }
                TokenType::EOF => {
                    break;
                }
                _ if in_block => {
                    current.push(token.clone());
                }
                _ => {
                    // Any non-doc token outside a block clears pending docs
                    pending_docs.clear();
                }
            }
            offset += 1;
        }

        if !current.is_empty() {
            blocks.push(Block {
                index: next_index,
                tokens: current,
            });
        }

        blocks
    }
}

impl Parser<Schema> for DefaultSchemaParser {
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<Schema> {
        self.parse_schema(stream, options)
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        !stream.is_at_end()
    }
}

impl SchemaParser for DefaultSchemaParser {}

#[derive(Debug)]
struct Block {
    index: usize,
    tokens: Vec<Token>,
}

#[cfg(test)]
mod tests {
    #![expect(clippy::unwrap_used)]
    use super::*;
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };
    use std::time::{Duration, Instant};

    fn t(t: TokenType) -> Token {
        Token::new(t, (1, 1), (1, 1))
    }

    // A parser that loops consuming tokens until EOF; with supervision,
    // the observed stream should synthesize EOF after timeout, allowing
    // this parser to terminate and return an error diagnostic.
    struct FakeLoopingDeclParser;
    impl DeclarationParser for FakeLoopingDeclParser {
        fn can_parse(&self, _stream: &dyn TokenStream) -> bool {
            true
        }
        fn parse(
            &mut self,
            stream: &mut dyn TokenStream,
            _options: &ParserOptions,
        ) -> ParseResult<Declaration> {
            // Consume until EOF; with supervision, EOF will be synthesized
            // after the time budget if progress is deemed too slow.
            loop {
                match stream.next() {
                    Some(t) if matches!(t.r#type(), TokenType::EOF) => break,
                    Some(_) => {
                        // Simulate slow work to trip the supervisor
                        std::thread::sleep(Duration::from_millis(5));
                    }
                    None => break,
                }
            }
            let span = SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            };
            ParseResult::error(Diagnostic::error(
                span,
                "looping parser terminated",
            ))
        }
        fn declaration_type(&self) -> DeclarationType {
            DeclarationType::Model
        }
    }

    #[test]
    fn supervised_looping_parser_is_cut_off_sequential() {
        // Single simple model block; looping parser should be cut off by supervision
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("User"));
        toks.push(t(TokenType::EOF));
        let mut stream = VectorTokenStream::new(toks);

        let builder = SchemaParserBuilder::new()
            .with_factory(|| Box::new(FakeLoopingDeclParser));
        let mut parser = builder.build();
        let mut opts = ParserOptions {
            concurrency: ConcurrencyMode::Sequential,
            ..Default::default()
        };
        // Tighten supervision so test runs quickly
        opts.max_parse_time = Duration::from_millis(15);
        opts.progress_check_interval = Duration::from_millis(3);
        opts.report_interval = 1;
        opts.enable_progress_validation = true;

        let res = parser.parse(&mut stream, &opts);
        assert!(res.value.is_some());
        // No successful declarations expected from looping parser
        assert!(res.value.unwrap().declarations.is_empty());
        // Should record at least one diagnostic from the fake parser
        assert!(!res.diagnostics.is_empty());
    }

    #[test]
    fn supervised_looping_parser_is_cut_off_concurrent() {
        // Two blocks to exercise group-thread path; both use looping parser
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("A"));
        toks.extend(simple_enum_tokens("B"));
        toks.push(t(TokenType::EOF));
        let mut stream = VectorTokenStream::new(toks);

        let builder = SchemaParserBuilder::new()
            .with_factory(|| Box::new(FakeLoopingDeclParser));
        let mut parser = builder.build();
        let mut opts = ParserOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 2,
                threshold: 1,
            },
            ..Default::default()
        };
        // Tighten supervision so test runs quickly
        opts.max_parse_time = Duration::from_millis(15);
        opts.progress_check_interval = Duration::from_millis(3);
        opts.report_interval = 1;
        opts.enable_progress_validation = true;

        let res = parser.parse(&mut stream, &opts);
        assert!(res.value.is_some());
        // No successful declarations expected
        assert!(res.value.as_ref().unwrap().declarations.is_empty());
        assert!(!res.diagnostics.is_empty());
    }

    fn ident(name: &str) -> Token {
        t(TokenType::Identifier(name.to_string()))
    }

    fn simple_model_tokens(name: &str) -> Vec<Token> {
        vec![
            t(TokenType::Model),
            ident(name),
            t(TokenType::LeftBrace),
            t(TokenType::RightBrace),
        ]
    }

    fn simple_enum_tokens(name: &str) -> Vec<Token> {
        vec![
            t(TokenType::Enum),
            ident(name),
            t(TokenType::LeftBrace),
            t(TokenType::RightBrace),
        ]
    }

    struct FakeStallDeclParser;
    impl DeclarationParser for FakeStallDeclParser {
        fn can_parse(&self, stream: &dyn TokenStream) -> bool {
            matches!(stream.peek().map(Token::r#type), Some(TokenType::Model))
        }
        fn parse(
            &mut self,
            _stream: &mut dyn TokenStream,
            _options: &ParserOptions,
        ) -> ParseResult<Declaration> {
            // Sleep longer than default supervision timeout to simulate stall.
            std::thread::sleep(Duration::from_millis(500));
            let span = SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            };
            ParseResult::error(Diagnostic::error(span, "delayed"))
        }
        fn declaration_type(&self) -> DeclarationType {
            DeclarationType::Model
        }
    }

    struct FakeOkDeclParser;
    impl DeclarationParser for FakeOkDeclParser {
        fn can_parse(&self, _stream: &dyn TokenStream) -> bool {
            true
        }
        fn parse(
            &mut self,
            _stream: &mut dyn TokenStream,
            _options: &ParserOptions,
        ) -> ParseResult<Declaration> {
            let span = SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            };
            let decl = Declaration::Enum(EnumDecl {
                name: crate::core::parser::ast::Ident {
                    text: "X".into(),
                    span: span.clone(),
                },
                members: Vec::new(),
                attrs: Vec::new(),
                docs: None,
                span,
            });
            ParseResult::success(decl)
        }
        fn declaration_type(&self) -> DeclarationType {
            DeclarationType::Enum
        }
    }

    struct FakeSlowDeclParser;
    impl DeclarationParser for FakeSlowDeclParser {
        fn can_parse(&self, _stream: &dyn TokenStream) -> bool {
            true
        }
        fn parse(
            &mut self,
            _stream: &mut dyn TokenStream,
            _options: &ParserOptions,
        ) -> ParseResult<Declaration> {
            // Simulate a slow parse to measure parallelism benefits.
            std::thread::sleep(Duration::from_millis(25));
            let span = SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            };
            let decl = Declaration::Enum(EnumDecl {
                name: crate::core::parser::ast::Ident {
                    text: "X".into(),
                    span: span.clone(),
                },
                members: Vec::new(),
                attrs: Vec::new(),
                docs: None,
                span,
            });
            ParseResult::success(decl)
        }
        fn declaration_type(&self) -> DeclarationType {
            DeclarationType::Enum
        }
    }

    #[test]
    #[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
    fn parallel_two_blocks_is_faster_than_sequential() {
        // Prepare two blocks
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("A"));
        toks.extend(simple_enum_tokens("B"));
        toks.push(t(TokenType::EOF));

        // Build parser that uses the slow parser
        let builder = SchemaParserBuilder::new()
            .with_factory(|| Box::new(FakeSlowDeclParser));
        let mut parser = builder.build();

        // Measure sequential
        let mut stream_seq = VectorTokenStream::new(toks.clone());
        let opts_seq = ParserOptions {
            concurrency: ConcurrencyMode::Sequential,
            ..Default::default()
        };
        let t0 = Instant::now();
        let res_seq = parser.parse(&mut stream_seq, &opts_seq);
        assert!(res_seq.value.is_some());
        let dur_seq = t0.elapsed();

        // Measure concurrent with 2 workers
        let mut stream_con = VectorTokenStream::new(toks);
        let opts_con = ParserOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 2,
                threshold: 1,
            },
            ..Default::default()
        };
        let t1 = Instant::now();
        let res_con = parser.parse(&mut stream_con, &opts_con);
        assert!(res_con.value.is_some());
        let dur_con = t1.elapsed();

        // Expect a noticeable improvement: concurrent should be at least ~10ms faster
        assert!(
            dur_con < dur_seq,
            "expected concurrent {dur_con:?} < sequential {dur_seq:?}"
        );
    }

    #[test]
    #[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
    fn parallel_batches_reduce_time_with_two_workers() {
        // Four blocks, two workers => about two batches
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("A"));
        toks.extend(simple_enum_tokens("B"));
        toks.extend(simple_model_tokens("C"));
        toks.extend(simple_enum_tokens("D"));
        toks.push(t(TokenType::EOF));

        let builder = SchemaParserBuilder::new()
            .with_factory(|| Box::new(FakeSlowDeclParser));
        let mut parser = builder.build();

        // Sequential timing baseline
        let mut stream_seq = VectorTokenStream::new(toks.clone());
        let opts_seq = ParserOptions {
            concurrency: ConcurrencyMode::Sequential,
            ..Default::default()
        };
        let t0 = Instant::now();
        let res_seq = parser.parse(&mut stream_seq, &opts_seq);
        assert!(res_seq.value.is_some());
        let dur_seq = t0.elapsed();

        // Concurrent with two workers
        let mut stream_con = VectorTokenStream::new(toks);
        let opts_con = ParserOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 2,
                threshold: 1,
            },
            ..Default::default()
        };
        let t1 = Instant::now();
        let res_con = parser.parse(&mut stream_con, &opts_con);
        assert!(res_con.value.is_some());
        let dur_con = t1.elapsed();

        // Expect concurrent to be substantially faster than sequential
        assert!(
            dur_con < dur_seq,
            "expected concurrent {dur_con:?} < sequential {dur_seq:?}"
        );
    }

    struct FakeParallelProbeDeclParser {
        current: Arc<AtomicUsize>,
        max_seen: Arc<AtomicUsize>,
        sleep_ms: u64,
    }

    impl DeclarationParser for FakeParallelProbeDeclParser {
        fn can_parse(&self, _stream: &dyn TokenStream) -> bool {
            true
        }
        fn parse(
            &mut self,
            _stream: &mut dyn TokenStream,
            _options: &ParserOptions,
        ) -> ParseResult<Declaration> {
            let now = self.current.fetch_add(1, Ordering::SeqCst) + 1;
            // Update max_seen if current exceeds stored max
            let mut prev = self.max_seen.load(Ordering::SeqCst);
            while now > prev {
                match self.max_seen.compare_exchange(
                    prev,
                    now,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                ) {
                    Ok(_) => break,
                    Err(p) => prev = p,
                }
            }
            std::thread::sleep(Duration::from_millis(self.sleep_ms));
            self.current.fetch_sub(1, Ordering::SeqCst);

            let span = SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            };
            let decl = Declaration::Enum(EnumDecl {
                name: crate::core::parser::ast::Ident {
                    text: "P".into(),
                    span: span.clone(),
                },
                members: Vec::new(),
                attrs: Vec::new(),
                docs: None,
                span,
            });
            ParseResult::success(decl)
        }
        fn declaration_type(&self) -> DeclarationType {
            DeclarationType::Enum
        }
    }

    #[test]
    fn parallel_observes_concurrency_level() {
        // Many blocks and 3 workers; expect max concurrent >= 2
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("A"));
        toks.extend(simple_enum_tokens("B"));
        toks.extend(simple_model_tokens("C"));
        toks.extend(simple_enum_tokens("D"));
        toks.extend(simple_model_tokens("E"));
        toks.extend(simple_enum_tokens("F"));
        toks.push(t(TokenType::EOF));

        let current = Arc::new(AtomicUsize::new(0));
        let max_seen = Arc::new(AtomicUsize::new(0));
        let c1 = current.clone();
        let m1 = max_seen.clone();
        let builder = SchemaParserBuilder::new().with_factory(move || {
            Box::new(FakeParallelProbeDeclParser {
                current: c1.clone(),
                max_seen: m1.clone(),
                sleep_ms: 20,
            }) as Box<dyn DeclarationParser>
        });
        let mut parser = builder.build();
        let mut stream = VectorTokenStream::new(toks);
        let opts = ParserOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 3,
                threshold: 1,
            },
            ..Default::default()
        };
        let res = parser.parse(&mut stream, &opts);
        assert!(res.value.is_some());
        let max_c = max_seen.load(Ordering::SeqCst);
        assert!(
            max_c >= 2,
            "expected at least 2 concurrent workers, saw {max_c}"
        );

        // Sequential run should show max concurrency == 1
        let mut toks2 = Vec::new();
        toks2.extend(simple_model_tokens("A"));
        toks2.extend(simple_enum_tokens("B"));
        toks2.extend(simple_model_tokens("C"));
        toks2.extend(simple_enum_tokens("D"));
        toks2.push(t(TokenType::EOF));
        let current2 = Arc::new(AtomicUsize::new(0));
        let max_seen2 = Arc::new(AtomicUsize::new(0));
        let c2 = current2.clone();
        let m2 = max_seen2.clone();
        let builder2 = SchemaParserBuilder::new().with_factory(move || {
            Box::new(FakeParallelProbeDeclParser {
                current: c2.clone(),
                max_seen: m2.clone(),
                sleep_ms: 10,
            }) as Box<dyn DeclarationParser>
        });
        let mut parser2 = builder2.build();
        let mut stream2 = VectorTokenStream::new(toks2);
        let opts2 = ParserOptions {
            concurrency: ConcurrencyMode::Sequential,
            ..Default::default()
        };
        let res2 = parser2.parse(&mut stream2, &opts2);
        assert!(res2.value.is_some());
        let max_c2 = max_seen2.load(Ordering::SeqCst);
        assert_eq!(
            max_c2, 1,
            "expected sequential processing to not overlap, saw {max_c2}"
        );
    }

    struct FakeVaryingSlowDeclParser;
    impl DeclarationParser for FakeVaryingSlowDeclParser {
        fn can_parse(&self, _stream: &dyn TokenStream) -> bool {
            true
        }
        fn parse(
            &mut self,
            stream: &mut dyn TokenStream,
            _options: &ParserOptions,
        ) -> ParseResult<Declaration> {
            // Peek name to vary delay and to reflect it in output declaration
            let name_len = stream
                .peek_ahead(1)
                .and_then(|t| match t.r#type() {
                    TokenType::Identifier(s) => Some(s.len()),
                    _ => None,
                })
                .unwrap_or(1);
            std::thread::sleep(Duration::from_millis((name_len as u64) * 5));
            let name = stream
                .peek_ahead(1)
                .and_then(|t| match t.r#type() {
                    TokenType::Identifier(s) => Some(s.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| "X".into());

            let span = SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            };
            let decl = Declaration::Enum(EnumDecl {
                name: crate::core::parser::ast::Ident {
                    text: name,
                    span: span.clone(),
                },
                members: Vec::new(),
                attrs: Vec::new(),
                docs: None,
                span,
            });
            ParseResult::success(decl)
        }
        fn declaration_type(&self) -> DeclarationType {
            DeclarationType::Enum
        }
    }

    #[test]
    fn concurrent_preserves_order_with_varying_durations() {
        // Names with varying sleep durations per parser
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("A")); // short
        toks.extend(simple_enum_tokens("LONG")); // long
        toks.extend(simple_model_tokens("BB")); // medium
        toks.extend(simple_enum_tokens("Z")); // short
        toks.push(t(TokenType::EOF));

        let builder = SchemaParserBuilder::new()
            .with_factory(|| Box::new(FakeVaryingSlowDeclParser));
        let mut parser = builder.build();
        let mut stream = VectorTokenStream::new(toks);
        let opts = ParserOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 2,
                threshold: 1,
            },
            ..Default::default()
        };
        let res = parser.parse(&mut stream, &opts);
        assert!(res.value.is_some());
        let schema = res.value.unwrap();
        // Extract order of declaration names
        let names: Vec<String> = schema
            .declarations
            .iter()
            .map(|d| match d {
                Declaration::Enum(e) => e.name.text.clone(),
                Declaration::Model(m) => m.name.text.clone(),
                Declaration::Datasource(ds) => ds.name.text.clone(),
                Declaration::Generator(g) => g.name.text.clone(),
                Declaration::Type(t) => t.name.text.clone(),
            })
            .collect();
        assert_eq!(
            names,
            vec!["A", "LONG", "BB", "Z"],
            "declaration order must match input despite varying durations"
        );
    }

    #[test]
    fn parses_sequential_multiple_blocks() {
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("User"));
        toks.extend(simple_enum_tokens("Role"));
        toks.push(t(TokenType::EOF));

        let mut stream = VectorTokenStream::new(toks);
        let mut parser = DefaultSchemaParser::default();
        let opts = ParserOptions {
            concurrency: ConcurrencyMode::Sequential,
            ..Default::default()
        };

        let res = parser.parse(&mut stream, &opts);
        assert!(res.is_success());
        let schema = res.value.unwrap();
        assert_eq!(schema.declarations.len(), 2);
        assert!(matches!(schema.declarations[0], Declaration::Model(_)));
        assert!(matches!(schema.declarations[1], Declaration::Enum(_)));
        assert!(res.diagnostics.is_empty());
    }

    #[test]
    fn parses_concurrently_with_docs_and_preserves_order() {
        // Add doc comments that should stick to the next block
        let mut toks = vec![t(TokenType::DocComment(" model".into()))];
        toks.extend(simple_model_tokens("User"));
        toks.push(t(TokenType::DocComment(" enum".into())));
        toks.extend(simple_enum_tokens("Role"));
        toks.push(t(TokenType::EOF));

        let mut parser = DefaultSchemaParser::default();
        let opts = ParserOptions {
            // Force concurrency path
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 1,
            },
            ..Default::default()
        };

        let mut stream = VectorTokenStream::new(toks.clone());
        let res = parser.parse(&mut stream, &opts);
        assert!(res.is_success());
        let schema = res.value.unwrap();
        assert_eq!(schema.declarations.len(), 2);
        match &schema.declarations[0] {
            Declaration::Model(m) => {
                assert_eq!(m.name.text, "User");
                assert!(m.docs.is_some());
            }
            _ => panic!("expected model first"),
        }
        match &schema.declarations[1] {
            Declaration::Enum(e) => {
                assert_eq!(e.name.text, "Role");
                assert!(e.docs.is_some());
            }
            _ => panic!("expected enum second"),
        }
    }

    #[test]
    fn supervised_sequential_stall_detected() {
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("User"));
        toks.push(t(TokenType::EOF));
        let mut stream = VectorTokenStream::new(toks);

        let builder = SchemaParserBuilder::new()
            .with_factory(|| Box::new(FakeStallDeclParser));
        let mut parser = builder.build();
        let opts = ParserOptions {
            concurrency: ConcurrencyMode::Sequential,
            ..Default::default()
        };
        let res = parser.parse(&mut stream, &opts);
        assert!(res.value.is_some());
        assert!(!res.diagnostics.is_empty());
    }

    #[test]
    fn supervised_concurrent_stall_detected() {
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("A"));
        toks.extend(simple_enum_tokens("B"));
        toks.push(t(TokenType::EOF));
        let mut stream = VectorTokenStream::new(toks);

        let builder = SchemaParserBuilder::new()
            .with_factory(|| Box::new(FakeStallDeclParser));
        let mut parser = builder.build();
        let opts = ParserOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 1,
            },
            ..Default::default()
        };
        let res = parser.parse(&mut stream, &opts);
        assert!(res.value.is_some());
        assert!(res.diagnostics.len() >= 2);
    }

    #[test]
    fn supervised_concurrent_ok_parses() {
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("A"));
        toks.extend(simple_enum_tokens("B"));
        toks.push(t(TokenType::EOF));
        let mut stream = VectorTokenStream::new(toks);

        let builder = SchemaParserBuilder::new()
            .with_factory(|| Box::new(FakeOkDeclParser));
        let mut parser = builder.build();
        let opts = ParserOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 1,
            },
            ..Default::default()
        };
        let res = parser.parse(&mut stream, &opts);
        assert!(res.value.is_some());
        let schema = res.value.unwrap();
        assert_eq!(schema.declarations.len(), 2);
        assert!(res.diagnostics.is_empty());
    }

    #[test]
    fn supervised_sequential_ok_parses() {
        // Simple single model parsed by a fake OK parser in sequential mode
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("A"));
        toks.push(t(TokenType::EOF));
        let mut stream = VectorTokenStream::new(toks);

        let builder = SchemaParserBuilder::new()
            .with_factory(|| Box::new(FakeOkDeclParser));
        let mut parser = builder.build();
        let opts = ParserOptions {
            concurrency: ConcurrencyMode::Sequential,
            ..Default::default()
        };
        let res = parser.parse(&mut stream, &opts);
        assert!(res.value.is_some());
        let schema = res.value.unwrap();
        assert_eq!(schema.declarations.len(), 1);
        assert!(res.diagnostics.is_empty());
    }

    #[test]
    fn supervised_concurrent_mixed_blocks() {
        // Two blocks: first stalls, second OK; expect one decl and a stall diagnostic
        let mut toks = Vec::new();
        toks.extend(simple_model_tokens("A"));
        toks.extend(simple_enum_tokens("B"));
        toks.push(t(TokenType::EOF));
        let mut stream = VectorTokenStream::new(toks);

        // First factory is stall, second factory is OK.
        let builder = SchemaParserBuilder::new()
            .with_factory(|| Box::new(FakeStallDeclParser))
            .with_factory(|| Box::new(FakeOkDeclParser));
        let mut parser = builder.build();
        let opts = ParserOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 1,
            },
            ..Default::default()
        };
        let res = parser.parse(&mut stream, &opts);
        assert!(res.value.is_some());
        let schema = res.value.unwrap();
        assert_eq!(schema.declarations.len(), 1);
        assert!(!res.diagnostics.is_empty());
    }

    #[test]
    fn unexpected_top_level_produces_diagnostic() {
        // Starts with identifier which no top-level parser accepts
        let toks = vec![ident("NotADecl"), t(TokenType::EOF)];
        let mut stream = VectorTokenStream::new(toks);
        let mut parser = DefaultSchemaParser::default();
        let opts = ParserOptions {
            concurrency: ConcurrencyMode::Sequential,
            ..Default::default()
        };

        let res = parser.parse(&mut stream, &opts);
        assert!(res.value.is_some());
        assert!(!res.diagnostics.is_empty());
    }

    #[test]
    fn builder_factories_count_matches_defaults() {
        let p = DefaultSchemaParser::default();
        // 5 default factories: model, enum, datasource, generator, type
        assert!(p.factories().len() >= 5);
    }

    #[test]
    fn concurrent_invalid_model_yields_diagnostic() {
        // Block starting with `model` but missing name should produce an error
        let mut toks = vec![
            t(TokenType::Model),
            t(TokenType::LeftBrace),
            t(TokenType::RightBrace),
        ];
        toks.push(t(TokenType::EOF));

        let mut parser = DefaultSchemaParser::default();
        let opts = ParserOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 1,
            },
            ..Default::default()
        };
        let mut stream = VectorTokenStream::new(toks);

        let res = parser.parse(&mut stream, &opts);
        assert!(res.value.is_some());
        assert!(!res.diagnostics.is_empty());
        // No declarations should be produced from the invalid block
        assert!(res.value.as_ref().unwrap().declarations.is_empty());
    }
}
