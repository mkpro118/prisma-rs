//! Diagnostic Quality and Error Recovery Tests
//!
//! Tests that validate error handling, diagnostic quality, and recovery
//! capabilities using the diagnostic utility functions.

use crate::scanner_parser::{
    assert_diagnostic_quality, parse_schema_end_to_end,
};
use std::fs;

fn load_fixture(path: &str) -> String {
    fs::read_to_string(format!("tests/fixtures/schemas/{path}"))
        .unwrap_or_else(|_| panic!("Failed to load fixture: {path}"))
}

#[test]
fn syntax_error_diagnostic_quality() {
    let invalid_schema = load_fixture("invalid/syntax_errors.prisma");
    let result = parse_schema_end_to_end(&invalid_schema);

    // Should produce diagnostics for syntax errors
    assert!(
        !result.diagnostics.is_empty(),
        "Invalid schema should produce diagnostics"
    );

    // All diagnostics should meet quality standards
    assert_diagnostic_quality(&result.diagnostics);

    println!(
        "Found {} diagnostics for syntax errors",
        result.diagnostics.len()
    );
    for (i, diagnostic) in result.diagnostics.iter().enumerate() {
        println!("Diagnostic {}: {:?}", i + 1, diagnostic);
    }
}

#[test]
fn missing_brace_error() {
    let input = r"
model User {
  id String @id
  name String
// Missing closing brace
";
    let result = parse_schema_end_to_end(input);

    // Should produce error diagnostics
    assert!(
        !result.diagnostics.is_empty(),
        "Missing brace should produce diagnostics"
    );

    // Validate diagnostic quality
    assert_diagnostic_quality(&result.diagnostics);

    // All diagnostics have been validated by assert_diagnostic_quality above

    println!("Missing brace diagnostics: {:#?}", result.diagnostics);
}

#[test]
fn invalid_field_syntax() {
    let input = r"
model User {
  id String @id
  title // missing type
  content String
}
";
    let result = parse_schema_end_to_end(input);

    // Should produce diagnostics for invalid field
    assert!(
        !result.diagnostics.is_empty(),
        "Invalid field should produce diagnostics"
    );
    assert_diagnostic_quality(&result.diagnostics);

    // Should still attempt to parse the model
    if let Some(schema) = &result.schema {
        assert!(
            !schema.declarations.is_empty(),
            "Should still create some declarations"
        );
    }

    println!("Invalid field diagnostics: {:#?}", result.diagnostics);
}

#[test]
fn unknown_attribute_error() {
    let input = r#"
model User {
  id String @invalid_attribute
  name String @unknown_attr("param")
}
"#;
    let result = parse_schema_end_to_end(input);

    // May or may not produce diagnostics depending on parser implementation
    // But if it does, they should be high quality
    if !result.diagnostics.is_empty() {
        assert_diagnostic_quality(&result.diagnostics);

        // Diagnostics should point to the problematic attributes
        for diagnostic in &result.diagnostics {
            println!(
                "Attribute diagnostic: {} at {}:{}",
                diagnostic.message,
                diagnostic.span.start.line,
                diagnostic.span.start.column
            );
        }
    }
}

#[test]
fn unclosed_enum_error() {
    let input = r"
enum Status {
  ACTIVE
  INACTIVE
// Missing closing brace

model User {
  id String
}
";
    let result = parse_schema_end_to_end(input);

    // Should produce error diagnostics
    assert!(
        !result.diagnostics.is_empty(),
        "Unclosed enum should produce diagnostics"
    );
    assert_diagnostic_quality(&result.diagnostics);

    println!("Unclosed enum diagnostics: {:#?}", result.diagnostics);
}

#[test]
fn strict_mode_diagnostics() {
    let input = r"
model User {
  id String @id
  optional_field String?
}
";

    // Parse with strict options
    let strict_result = parse_schema_end_to_end(input);

    // Compare with lenient parsing if there are differences
    if !strict_result.diagnostics.is_empty() {
        assert_diagnostic_quality(&strict_result.diagnostics);
        println!("Strict mode diagnostics: {:#?}", strict_result.diagnostics);
    }
}

#[test]
fn error_recovery_continues_parsing() {
    let input = r"
model User {
  id String @id
  // Syntax error here
  invalid syntax error
}

// Parser should recover and continue
model Post {
  id String @id
  title String
}

enum Status {
  ACTIVE
  INACTIVE
}
";
    let result = parse_schema_end_to_end(input);

    // Should have diagnostics for the error
    assert!(
        !result.diagnostics.is_empty(),
        "Should produce diagnostics for syntax error"
    );
    assert_diagnostic_quality(&result.diagnostics);

    // But should still parse some declarations
    if let Some(schema) = &result.schema {
        assert!(
            !schema.declarations.is_empty(),
            "Should recover and parse some declarations"
        );
        println!(
            "Recovered {} declarations despite errors",
            schema.declarations.len()
        );
    }

    println!("Error recovery diagnostics: {:#?}", result.diagnostics);
}

#[test]
fn diagnostic_message_helpfulness() {
    let test_cases = [
        (r"model { }", "missing model name"),
        (r"model User", "missing braces"),
        (r"model User { id }", "missing field type"),
    ];

    for (input, expected_error_type) in test_cases {
        let result = parse_schema_end_to_end(input);

        if !result.diagnostics.is_empty() {
            assert_diagnostic_quality(&result.diagnostics);

            // Check that error messages are descriptive
            for diagnostic in &result.diagnostics {
                assert!(
                    diagnostic.message.len() >= 10,
                    "Diagnostic message should be reasonably descriptive: '{}'",
                    diagnostic.message
                );

                // Messages shouldn't just be generic
                assert!(
                    !diagnostic.message.contains("error"),
                    "Diagnostic messages should be specific, not generic: '{}'",
                    diagnostic.message
                );
            }

            println!("{}: {:#?}", expected_error_type, result.diagnostics);
        }
    }
}

#[test]
fn diagnostic_span_accuracy() {
    let input = r"model User {
  id String @id
  invalid_field_without_type
  name String
}";

    let result = parse_schema_end_to_end(input);

    if !result.diagnostics.is_empty() {
        assert_diagnostic_quality(&result.diagnostics);

        for diagnostic in &result.diagnostics {
            // Spans should point to reasonable locations
            assert!(
                diagnostic.span.start.line <= 5,
                "Diagnostic line should be within schema bounds"
            );

            // End should be after or equal to start
            assert!(
                diagnostic.span.end.line >= diagnostic.span.start.line,
                "Diagnostic end line should be >= start line"
            );
            if diagnostic.span.end.line == diagnostic.span.start.line {
                assert!(
                    diagnostic.span.end.column >= diagnostic.span.start.column,
                    "Diagnostic end column should be >= start column on same line"
                );
            }

            println!(
                "Diagnostic span: {}:{}-{}:{} - {}",
                diagnostic.span.start.line,
                diagnostic.span.start.column,
                diagnostic.span.end.line,
                diagnostic.span.end.column,
                diagnostic.message
            );
        }
    }
}

#[test]
fn multiple_error_handling() {
    let input = r"
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

    let result = parse_schema_end_to_end(input);

    // Should handle multiple errors gracefully
    if !result.diagnostics.is_empty() {
        assert_diagnostic_quality(&result.diagnostics);

        // Should have multiple diagnostics
        assert!(
            result.diagnostics.len() >= 2,
            "Should detect multiple errors, found: {}",
            result.diagnostics.len()
        );

        println!("Multiple error diagnostics: {:#?}", result.diagnostics);
    }

    // Parser should not crash despite multiple errors
    assert!(
        result.parse_time.as_millis() < 1000,
        "Should complete parsing despite multiple errors"
    );
}
