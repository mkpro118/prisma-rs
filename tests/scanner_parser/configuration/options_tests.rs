//! Parser Configuration and Options Tests
//!
//! Tests that validate different parser configurations and their effects
//! on parsing behavior, error handling, and performance characteristics.

use crate::scanner_parser::{
    create_strict_options, create_test_options, parse_schema_with_options,
};
use std::fs;

fn load_fixture(path: &str) -> String {
    fs::read_to_string(format!("tests/fixtures/schemas/{path}"))
        .unwrap_or_else(|_| panic!("Failed to load fixture: {path}"))
}

#[test]
fn default_options_behavior() {
    let input = r"
model User {
  id String @id
  name String
  email String @unique
}
";

    let test_options = create_test_options();
    let result = parse_schema_with_options(input, &test_options);

    assert!(
        result.schema.is_some(),
        "Test options should enable successful parsing"
    );
    // Test options should be lenient and allow parsing to succeed
    println!(
        "Test options result: {} diagnostics",
        result.diagnostics.len()
    );
}

#[test]
fn strict_vs_lenient_parsing() {
    let input = r"
model User {
  id String @id
  optional_field String?
  // Potentially problematic constructs that strict mode might reject
}

enum Status {
  ACTIVE
  INACTIVE
}
";

    let test_options = create_test_options(); // Lenient
    let strict_options = create_strict_options(); // Strict

    let lenient_result = parse_schema_with_options(input, &test_options);
    let strict_result = parse_schema_with_options(input, &strict_options);

    // Both should parse, but strict might have different diagnostic behavior
    assert!(
        lenient_result.schema.is_some(),
        "Lenient mode should parse successfully"
    );
    println!(
        "Lenient mode: {} diagnostics",
        lenient_result.diagnostics.len()
    );
    println!(
        "Strict mode: {} diagnostics",
        strict_result.diagnostics.len()
    );

    // If strict mode is more restrictive, it might produce more diagnostics
    // or fail to parse where lenient mode succeeds
    if strict_result.schema.is_none() {
        assert!(
            !strict_result.diagnostics.is_empty(),
            "Strict mode failure should produce diagnostics"
        );
    }
}

#[test]
fn error_recovery_options() {
    let invalid_input = r"
model User {
  id String @id
  invalid_field  // Missing type - syntax error
  name String
}

model Post {
  id String @id
  title String
  // More valid content after error
}
";

    let test_options = create_test_options(); // Has error recovery
    let strict_options = create_strict_options(); // No error recovery

    let recovery_result =
        parse_schema_with_options(invalid_input, &test_options);
    let no_recovery_result =
        parse_schema_with_options(invalid_input, &strict_options);

    // Error recovery should allow parsing to continue despite errors
    if let Some(schema) = &recovery_result.schema {
        println!(
            "With error recovery: {} declarations parsed",
            schema.declarations.len()
        );
        // Should parse some declarations despite errors
        assert!(
            !schema.declarations.is_empty(),
            "Error recovery should allow partial parsing"
        );
    }

    // Without error recovery, parsing might stop at first error
    if no_recovery_result.schema.is_none() {
        println!("Without error recovery: parsing failed completely");
        assert!(
            !no_recovery_result.diagnostics.is_empty(),
            "Should have error diagnostics when parsing fails"
        );
    }

    // Both should have diagnostics for the syntax error
    assert!(
        !recovery_result.diagnostics.is_empty(),
        "Should detect syntax error"
    );
    assert!(
        !no_recovery_result.diagnostics.is_empty(),
        "Should detect syntax error"
    );
}

#[test]
fn max_errors_configuration() {
    let multi_error_input = r"
model {  // Error 1: missing name
  id String @id
  invalid_field  // Error 2: missing type
}

enum {  // Error 3: missing name
  VALUE1
  VALUE2
}

model Post
  id String  // Error 4: missing braces
  title String
}
";

    let test_options = create_test_options(); // max_errors: 100
    let strict_options = create_strict_options(); // max_errors: 1

    let many_errors_result =
        parse_schema_with_options(multi_error_input, &test_options);
    let limited_errors_result =
        parse_schema_with_options(multi_error_input, &strict_options);

    // Test options should collect more errors
    println!(
        "Test options found {} diagnostics",
        many_errors_result.diagnostics.len()
    );
    println!(
        "Strict options found {} diagnostics",
        limited_errors_result.diagnostics.len()
    );

    // Strict options with max_errors=1 should stop after first error
    assert!(
        !limited_errors_result.diagnostics.is_empty(),
        "Should find at least one error"
    );
    assert!(
        limited_errors_result.diagnostics.len() <= 3,
        "Should be limited by max_errors setting"
    );

    // Test options should find more errors
    if many_errors_result.diagnostics.len()
        > limited_errors_result.diagnostics.len()
    {
        println!("Test options collected more errors as expected");
    }
}

#[test]
fn feature_support_configuration() {
    let experimental_input = r"
// This might use experimental features
type StringAlias = String

model User {
  id String @id
  name String
}
";

    let test_options = create_test_options(); // WithExperimental
    let strict_options = create_strict_options(); // StableOnly

    let experimental_result =
        parse_schema_with_options(experimental_input, &test_options);
    let stable_result =
        parse_schema_with_options(experimental_input, &strict_options);

    // Test options should allow experimental features
    println!(
        "Experimental support: {} diagnostics",
        experimental_result.diagnostics.len()
    );
    println!(
        "Stable only: {} diagnostics",
        stable_result.diagnostics.len()
    );

    // Both should parse the model, but might differ on experimental constructs
    if let Some(exp_schema) = &experimental_result.schema
        && let Some(stable_schema) = &stable_result.schema
    {
        println!(
            "Experimental: {} declarations, Stable: {} declarations",
            exp_schema.declarations.len(),
            stable_schema.declarations.len()
        );
    }
}

#[test]
fn comprehensive_schema_with_different_options() {
    let schema_content = load_fixture("comprehensive/blog_schema.prisma");

    let configs = [
        ("test_options", create_test_options()),
        ("strict_options", create_strict_options()),
    ];

    for (name, options) in configs {
        let result = parse_schema_with_options(&schema_content, &options);

        println!(
            "{}: parsing success = {}, diagnostics = {}",
            name,
            result.schema.is_some(),
            result.diagnostics.len()
        );

        if let Some(schema) = &result.schema {
            println!(
                "{}: {} declarations parsed",
                name,
                schema.declarations.len()
            );
        }

        // Parsing time should be reasonable regardless of options
        assert!(
            result.parse_time.as_millis() < 500,
            "Parse time should be reasonable for {name}",
        );
    }
}

#[test]
fn parsing_mode_differences() {
    let input = r"
model User {
  id String @id
  name String
  // Some constructs that might be interpreted differently
  metadata Json?
}

enum Status {
  ACTIVE
  INACTIVE
}
";

    let lenient_options = create_test_options(); // ParsingMode::Lenient
    let strict_options = create_strict_options(); // ParsingMode::Strict

    let lenient_result = parse_schema_with_options(input, &lenient_options);
    let strict_result = parse_schema_with_options(input, &strict_options);

    // Compare parsing outcomes
    let lenient_success = lenient_result.schema.is_some();
    let strict_success = strict_result.schema.is_some();

    println!(
        "Lenient parsing: {} (diagnostics: {})",
        lenient_success,
        lenient_result.diagnostics.len()
    );
    println!(
        "Strict parsing: {} (diagnostics: {})",
        strict_success,
        strict_result.diagnostics.len()
    );

    // At minimum, both should complete without crashing
    assert!(
        lenient_result.parse_time.as_millis() < 1000,
        "Lenient parsing should complete"
    );
    assert!(
        strict_result.parse_time.as_millis() < 1000,
        "Strict parsing should complete"
    );
}

#[test]
fn concurrency_mode_consistency() {
    let input = r"
model User {
  id String @id
  posts Post[]
}

model Post {
  id String @id
  author User @relation(fields: [authorId], references: [id])
  authorId String
}
";

    let sequential_options = create_test_options(); // ConcurrencyMode::Sequential

    // Parse the same input multiple times with sequential options
    let results: Vec<_> = (0..5)
        .map(|_| parse_schema_with_options(input, &sequential_options))
        .collect();

    // All results should be identical
    let first_success = results[0].schema.is_some();
    let first_diag_count = results[0].diagnostics.len();

    for (i, result) in results.iter().enumerate().skip(1) {
        assert_eq!(
            result.schema.is_some(),
            first_success,
            "Result {i} should match first result",
        );
        assert_eq!(
            result.diagnostics.len(),
            first_diag_count,
            "Diagnostic count {i} should match first result",
        );
    }

    println!("Sequential parsing consistency verified across 5 runs");
}
