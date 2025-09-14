//! Scanner-Parser Integration Test Utilities
//!
//! Comprehensive test utilities for end-to-end validation of the complete
//! parsing pipeline from raw strings to ASTs with diagnostics.

use prisma_rs::core::parser::ast::*;
use prisma_rs::core::parser::config::{
    ConcurrencyMode, Diagnostic, FeatureSupport, ParseResult, ParserOptions,
    ParsingMode,
};
use prisma_rs::core::parser::schema_parser::DefaultSchemaParser;
use prisma_rs::core::parser::stream::VectorTokenStream;
use prisma_rs::core::scanner::lexer::Lexer;
use prisma_rs::core::scanner::tokens::{Token, TokenType};
use std::time::{Duration, Instant};

/// Result of end-to-end parsing containing AST and diagnostics
#[derive(Debug)]
pub struct EndToEndResult {
    pub schema: Option<Schema>,
    pub diagnostics: Vec<Diagnostic>,
    pub parse_time: Duration,
    pub token_count: usize,
}

/// Performance metrics for parsing pipeline
#[derive(Debug)]
pub struct PerformanceMetrics {
    pub total_time: Duration,
    pub scan_time: Duration,
    pub parse_time: Duration,
    pub token_count: usize,
    pub ast_node_count: usize,
    pub memory_usage: usize, // Approximate
}

/// Parse a schema string end-to-end through the complete pipeline
pub fn parse_schema_end_to_end(input: &str) -> EndToEndResult {
    parse_schema_with_options(input, &ParserOptions::default())
}

/// Parse a schema with specific parser options
pub fn parse_schema_with_options(
    input: &str,
    options: &ParserOptions,
) -> EndToEndResult {
    let start_time = Instant::now();

    // Create lexer and tokenize
    let mut lexer = Lexer::default_for_input(input);
    let mut tokens = Vec::new();

    while let Ok(Some(token)) = lexer.next_token() {
        let is_eof = matches!(token.r#type(), TokenType::EOF);
        tokens.push(token);
        if is_eof {
            break;
        }
    }

    let token_count = tokens.len();

    // Create parser and parse
    let mut parser = DefaultSchemaParser::default();

    // Convert tokens to stream
    let mut stream = VectorTokenStream::new(tokens);
    let result = parser.parse_schema(&mut stream, options);

    let parse_time = start_time.elapsed();

    EndToEndResult {
        schema: result.value,
        diagnostics: result.diagnostics,
        parse_time,
        token_count,
    }
}

/// Benchmark the parsing pipeline with detailed metrics
pub fn benchmark_parsing_pipeline(input: &str) -> PerformanceMetrics {
    let total_start = Instant::now();

    // Measure scanning phase
    let scan_start = Instant::now();
    let mut lexer = Lexer::default_for_input(input);
    let mut tokens = Vec::new();

    while let Ok(Some(token)) = lexer.next_token() {
        let is_eof = matches!(token.r#type(), TokenType::EOF);
        tokens.push(token);
        if is_eof {
            break;
        }
    }

    let scan_time = scan_start.elapsed();
    let token_count = tokens.len();

    // Measure parsing phase
    let parse_start = Instant::now();
    let options = ParserOptions::default();
    let mut parser = DefaultSchemaParser::default();
    let mut stream = VectorTokenStream::new(tokens.clone());

    let schema_result = parser.parse_schema(&mut stream, &options);
    let parse_time = parse_start.elapsed();

    let total_time = total_start.elapsed();

    // Approximate AST node count
    let ast_node_count = match &schema_result.value {
        Some(schema) => count_ast_nodes(schema),
        None => 0,
    };

    PerformanceMetrics {
        total_time,
        scan_time,
        parse_time,
        token_count,
        ast_node_count,
        memory_usage: estimate_memory_usage(&tokens, &schema_result),
    }
}

/// Assert that AST structure matches expected patterns
pub fn assert_ast_structure(
    schema: &Schema,
    expected_models: usize,
    expected_enums: usize,
    expected_datasources: usize,
) {
    let mut model_count = 0;
    let mut enum_count = 0;
    let mut datasource_count = 0;

    for declaration in &schema.declarations {
        match declaration {
            Declaration::Model(_) => model_count += 1,
            Declaration::Enum(_) => enum_count += 1,
            Declaration::Datasource(_) => datasource_count += 1,
            _ => {}
        }
    }

    assert_eq!(model_count, expected_models, "Model count mismatch");
    assert_eq!(enum_count, expected_enums, "Enum count mismatch");
    assert_eq!(
        datasource_count, expected_datasources,
        "Datasource count mismatch"
    );
}

/// Assert diagnostic quality and accuracy
pub fn assert_diagnostic_quality(diagnostics: &[Diagnostic]) {
    for diagnostic in diagnostics {
        // Ensure all diagnostics have valid source spans
        // Line and column numbers are unsigned, so always >= 0
        // Just ensure the span is well-formed
        assert!(
            diagnostic.span.end.line >= diagnostic.span.start.line,
            "Diagnostic span should be well-formed"
        );

        // Ensure diagnostic messages are meaningful
        assert!(
            !diagnostic.message.is_empty(),
            "Diagnostic message should not be empty"
        );
        assert!(
            diagnostic.message.len() > 5,
            "Diagnostic message should be descriptive"
        );
    }
}

/// Test concurrent parsing produces deterministic results
pub fn assert_concurrent_deterministic(input: &str, thread_count: usize) {
    use std::thread;

    // Parse sequentially as reference
    let sequential_result = parse_schema_end_to_end(input);

    // Parse concurrently with multiple threads
    let handles: Vec<_> = (0..thread_count)
        .map(|_| {
            let input_clone = input.to_string();
            thread::spawn(move || parse_schema_end_to_end(&input_clone))
        })
        .collect();

    let concurrent_results: Vec<_> =
        handles.into_iter().map(|h| h.join().unwrap()).collect();

    // Verify all results match
    for (i, result) in concurrent_results.iter().enumerate() {
        assert_eq!(
            result.schema.is_some(),
            sequential_result.schema.is_some(),
            "Thread {i} parsing success should match sequential"
        );

        if let (Some(seq_schema), Some(conc_schema)) =
            (&sequential_result.schema, &result.schema)
        {
            assert_eq!(
                seq_schema.declarations.len(),
                conc_schema.declarations.len(),
                "Thread {i} should produce same number of declarations"
            );
        }

        assert_eq!(
            result.diagnostics.len(),
            sequential_result.diagnostics.len(),
            "Thread {i} diagnostic count should match sequential"
        );
    }
}

/// Create parser options for specific test scenarios
pub fn create_test_options() -> ParserOptions {
    ParserOptions {
        max_errors: 100,
        parsing_mode: ParsingMode::Lenient,
        feature_support: FeatureSupport::WithExperimental,
        error_recovery: true,
        concurrency: ConcurrencyMode::Sequential, // Start with sequential for testing
        ..Default::default()
    }
}

/// Create strict parser options for error testing
pub fn create_strict_options() -> ParserOptions {
    ParserOptions {
        max_errors: 1,
        parsing_mode: ParsingMode::Strict,
        feature_support: FeatureSupport::StableOnly,
        error_recovery: false,
        concurrency: ConcurrencyMode::Sequential,
        ..Default::default()
    }
}

/// Create concurrent parser options for threading tests
pub fn create_concurrent_options(
    max_threads: usize,
    threshold: usize,
) -> ParserOptions {
    ParserOptions {
        max_errors: 100,
        parsing_mode: ParsingMode::Lenient,
        feature_support: FeatureSupport::WithExperimental,
        error_recovery: true,
        concurrency: ConcurrencyMode::Concurrent {
            max_threads,
            threshold,
        },
        ..Default::default()
    }
}

// Helper functions for internal use

fn count_ast_nodes(schema: &Schema) -> usize {
    let mut count = 1; // Schema itself

    for declaration in &schema.declarations {
        count += match declaration {
            Declaration::Model(model) => 1 + model.members.len(),
            Declaration::Enum(enum_decl) => 1 + enum_decl.members.len(),
            Declaration::Datasource(_)
            | Declaration::Generator(_)
            | Declaration::Type(_) => 1,
        };
    }

    count
}

fn estimate_memory_usage(
    tokens: &[Token],
    schema_result: &ParseResult<Schema>,
) -> usize {
    let token_size = std::mem::size_of_val(tokens);
    let schema_size = match &schema_result.value {
        Some(schema) => estimate_schema_size(schema),
        None => 0,
    };

    token_size + schema_size
}

fn estimate_schema_size(schema: &Schema) -> usize {
    // Rough estimation - in practice would be more sophisticated
    std::mem::size_of::<Schema>() + (schema.declarations.len() * 256)
}
