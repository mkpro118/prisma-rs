//! Concurrent Parsing Determinism Tests
//!
//! Tests that validate concurrent parsing produces deterministic results
//! and that the parser handles multi-threading scenarios correctly.

use crate::scanner_parser::{
    assert_concurrent_deterministic, create_concurrent_options,
    parse_schema_with_options,
};
use std::fs;

fn load_fixture(path: &str) -> String {
    fs::read_to_string(format!("tests/fixtures/schemas/{path}"))
        .unwrap_or_else(|_| panic!("Failed to load fixture: {path}"))
}

#[test]
#[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
fn concurrent_empty_schema() {
    let input = "";
    let thread_count = 4;

    // Should produce identical results across all threads
    assert_concurrent_deterministic(input, thread_count);
}

#[test]
#[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
fn concurrent_simple_model() {
    let input = r"
model User {
  id String @id
  name String
  email String @unique
}
";
    let thread_count = 8;

    // Complex enough to exercise parser but deterministic
    assert_concurrent_deterministic(input, thread_count);
}

#[test]
#[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
fn concurrent_comprehensive_schema() {
    let schema_content = load_fixture("comprehensive/blog_schema.prisma");
    let thread_count = 6;

    // Large schema should still be deterministic
    assert_concurrent_deterministic(&schema_content, thread_count);
}

#[test]
#[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
fn concurrent_error_schema() {
    let input = r"
model User {
  id String @id
  invalid_field  // Missing type
}

enum Status
  ACTIVE  // Missing braces
  INACTIVE
}
";
    let thread_count = 4;

    // Error conditions should be deterministic too
    assert_concurrent_deterministic(input, thread_count);
}

#[test]
#[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
fn concurrent_options_configuration() {
    let input = r"
model User {
  id String @id
  name String
}

enum Status {
  ACTIVE
  INACTIVE  
}
";

    let options = create_concurrent_options(4, 1000);
    let result1 = parse_schema_with_options(input, &options);
    let result2 = parse_schema_with_options(input, &options);

    // Same options should produce same results
    assert_eq!(
        result1.schema.is_some(),
        result2.schema.is_some(),
        "Concurrent options should produce consistent results"
    );

    if let (Some(schema1), Some(schema2)) = (&result1.schema, &result2.schema) {
        assert_eq!(
            schema1.declarations.len(),
            schema2.declarations.len(),
            "Declaration counts should match"
        );
    }

    assert_eq!(
        result1.diagnostics.len(),
        result2.diagnostics.len(),
        "Diagnostic counts should match"
    );
}

#[test]
#[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
fn concurrent_scaling_thread_counts() {
    let input = r"
model User {
  id String @id
  name String
  email String @unique
  posts Post[]
}

model Post {
  id String @id
  title String
  content String?
  published Boolean @default(false)
  author User @relation(fields: [authorId], references: [id])
  authorId String
}

enum Status {
  DRAFT
  PUBLISHED
  ARCHIVED
}
";

    let thread_counts = [1, 2, 4, 8, 16];

    for &count in &thread_counts {
        println!("Testing with {count} threads");
        assert_concurrent_deterministic(input, count);
    }
}

#[test]
#[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
fn concurrent_mixed_workloads() {
    let test_cases = [
        ("", "empty"),
        ("model User { id String }", "simple"),
        (&load_fixture("minimal/single_model.prisma"), "minimal"),
        (
            &load_fixture("comprehensive/blog_schema.prisma"),
            "comprehensive",
        ),
    ];

    for (input, case_name) in test_cases {
        println!("Testing concurrent determinism for: {case_name}");
        assert_concurrent_deterministic(input, 4);
    }
}

#[test]
#[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
fn concurrent_options_with_different_thresholds() {
    let input = load_fixture("comprehensive/blog_schema.prisma");

    let configs = [
        (2, 500),  // Low threads, low threshold
        (4, 1000), // Medium threads, medium threshold
        (8, 2000), // High threads, high threshold
    ];

    for (threads, threshold) in configs {
        let options = create_concurrent_options(threads, threshold);
        let result = parse_schema_with_options(&input, &options);

        // Should parse successfully regardless of concurrency config
        assert!(
            result.schema.is_some(),
            "Schema should parse with {threads}T/{threshold}B threshold",
        );

        println!(
            "Parsed with {}T/{}B: {} diagnostics",
            threads,
            threshold,
            result.diagnostics.len()
        );
    }
}

#[test]
#[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
fn concurrent_high_contention() {
    let input = r"
model A { id String }
model B { id String }
model C { id String }
model D { id String }
model E { id String }
";
    let high_thread_count = 32;

    // High contention scenario - many threads on small schema
    assert_concurrent_deterministic(input, high_thread_count);
}

#[test]
#[ignore = "concurrent test - run with: cargo test -- --include-ignored"]
fn concurrent_unicode_handling() {
    let input = r"
// Unicode model names and comments
model Użytkownik {
  identyfikator String @id
  imię String
  // Komentarz po polsku
  email String @unique
}

enum Status {
  AKTYWNY
  NIEAKTYWNY
  // 中文注释  
}
";

    // Unicode content should be deterministic across threads
    assert_concurrent_deterministic(input, 6);
}
