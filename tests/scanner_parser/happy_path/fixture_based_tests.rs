//! Fixture-based Integration Tests
//!
//! Tests using predefined schema fixtures to validate end-to-end parsing
//! of realistic Prisma schemas.

use crate::scanner_parser::{assert_ast_structure, parse_schema_end_to_end};
use std::fs;

fn load_fixture(path: &str) -> String {
    fs::read_to_string(format!("tests/fixtures/schemas/{path}"))
        .unwrap_or_else(|_| panic!("Failed to load fixture: {path}"))
}

#[test]
fn empty_fixture() {
    let schema_content = load_fixture("minimal/empty.prisma");
    let result = parse_schema_end_to_end(&schema_content);

    assert!(
        result.schema.is_some(),
        "Empty fixture should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert_eq!(
        schema.declarations.len(),
        0,
        "Empty schema should have no declarations"
    );
}

#[test]
fn single_model_fixture() {
    let schema_content = load_fixture("minimal/single_model.prisma");
    let result = parse_schema_end_to_end(&schema_content);

    assert!(
        result.schema.is_some(),
        "Single model fixture should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert_ast_structure(&schema, 1, 0, 0);

    // Verify the model structure
    if let Some(prisma_rs::core::parser::ast::Declaration::Model(model)) =
        schema.declarations.first()
    {
        assert_eq!(model.name.text, "User");
        assert_eq!(model.members.len(), 3, "User model should have 3 fields");
    } else {
        panic!("Expected first declaration to be a model");
    }
}

#[test]
fn single_enum_fixture() {
    let schema_content = load_fixture("minimal/single_enum.prisma");
    let result = parse_schema_end_to_end(&schema_content);

    assert!(
        result.schema.is_some(),
        "Single enum fixture should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert_ast_structure(&schema, 0, 1, 0);

    // Verify the enum structure
    if let Some(prisma_rs::core::parser::ast::Declaration::Enum(enum_decl)) =
        schema.declarations.first()
    {
        assert_eq!(enum_decl.name.text, "Status");
        assert_eq!(
            enum_decl.members.len(),
            3,
            "Status enum should have 3 values"
        );
    } else {
        panic!("Expected first declaration to be an enum");
    }
}

#[test]
fn comprehensive_blog_schema() {
    let schema_content = load_fixture("comprehensive/blog_schema.prisma");
    let result = parse_schema_end_to_end(&schema_content);

    assert!(
        result.schema.is_some(),
        "Blog schema should parse successfully"
    );
    let schema = result.schema.unwrap();

    println!(
        "Blog schema parsed {} declarations",
        schema.declarations.len()
    );
    println!("Diagnostics: {:?}", result.diagnostics);

    // Count different declaration types
    let mut models = 0;
    let mut enums = 0;
    let mut datasources = 0;
    let mut generators = 0;

    for declaration in &schema.declarations {
        match declaration {
            prisma_rs::core::parser::ast::Declaration::Model(_) => models += 1,
            prisma_rs::core::parser::ast::Declaration::Enum(_) => enums += 1,
            prisma_rs::core::parser::ast::Declaration::Datasource(_) => {
                datasources += 1;
            }
            prisma_rs::core::parser::ast::Declaration::Generator(_) => {
                generators += 1;
            }
            prisma_rs::core::parser::ast::Declaration::Type(_) => {}
        }
    }

    // The blog schema should have multiple models and at least one enum
    assert!(
        models >= 3,
        "Blog schema should have at least 3 models, found: {models}"
    );
    assert!(
        enums >= 1,
        "Blog schema should have at least 1 enum, found: {enums}"
    );
    // Report what we found
    println!(
        "Found: {models} models, {enums} enums, {datasources} datasources, {generators} generators"
    );

    // Note: datasource and generator parsing may not be fully implemented yet

    // Performance check - complex schema should still parse reasonably quickly
    assert!(
        result.parse_time.as_millis() < 500,
        "Complex schema should parse under 500ms"
    );
}

#[test]
fn token_counts() {
    let fixtures = [
        ("minimal/empty.prisma", 1, 10), // Should have at least EOF, maybe some comment tokens
        ("minimal/single_model.prisma", 15, 50), // Should have reasonable token count
        ("minimal/single_enum.prisma", 5, 15), // Should have reasonable token count
    ];

    for (fixture_path, min_tokens, max_tokens) in fixtures {
        let schema_content = load_fixture(fixture_path);
        let result = parse_schema_end_to_end(&schema_content);

        assert!(
            result.token_count >= min_tokens
                && result.token_count <= max_tokens,
            "Fixture {} should have between {} and {} tokens, found: {}",
            fixture_path,
            min_tokens,
            max_tokens,
            result.token_count
        );
    }
}

#[test]
fn parse_times_reasonable() {
    let fixtures = [
        "minimal/empty.prisma",
        "minimal/single_model.prisma",
        "minimal/single_enum.prisma",
        "comprehensive/blog_schema.prisma",
    ];

    for fixture_path in fixtures {
        let schema_content = load_fixture(fixture_path);
        let result = parse_schema_end_to_end(&schema_content);

        // All fixtures should parse in under 100ms (very generous for small schemas)
        assert!(
            result.parse_time.as_millis() < 100,
            "Fixture {} took too long to parse: {}ms",
            fixture_path,
            result.parse_time.as_millis()
        );
    }
}
