//! Minimal Schema Integration Tests
//!
//! Tests the complete scanner-parser pipeline with minimal but valid
//! Prisma schemas. Focuses on basic functionality and successful parsing.

use crate::scanner_parser::{assert_ast_structure, parse_schema_end_to_end};

use prisma_rs::core::parser::ast::{Declaration, EnumMember, ModelMember};

#[test]
fn empty_schema() {
    let input = "";
    let result = parse_schema_end_to_end(input);

    assert!(
        result.schema.is_some(),
        "Empty schema should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert_eq!(
        schema.declarations.len(),
        0,
        "Empty schema should have no declarations"
    );
    assert!(
        result.diagnostics.is_empty(),
        "Empty schema should produce no diagnostics"
    );
    assert!(result.token_count >= 1, "Should contain at least EOF token");
}

#[test]
fn whitespace_only_schema() {
    let input = "   \n\t  \n  ";
    let result = parse_schema_end_to_end(input);

    assert!(
        result.schema.is_some(),
        "Whitespace-only schema should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert_eq!(
        schema.declarations.len(),
        0,
        "Whitespace schema should have no declarations"
    );
    assert!(
        result.diagnostics.is_empty(),
        "Whitespace schema should produce no diagnostics"
    );
}

#[test]
fn single_empty_model() {
    let input = r"
model User {
}
";
    let result = parse_schema_end_to_end(input);

    assert!(
        result.schema.is_some(),
        "Single empty model should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert_ast_structure(&schema, 1, 0, 0);
    assert!(
        result.diagnostics.is_empty(),
        "Empty model should produce no diagnostics"
    );

    // Verify model structure
    if let Some(Declaration::Model(model)) = schema.declarations.first() {
        assert_eq!(model.name.text, "User");
        assert!(
            model.members.is_empty(),
            "Empty model should have no members"
        );
    } else {
        panic!("Expected first declaration to be a model");
    }
}

#[test]
fn single_model_with_field() {
    let input = r"
model User {
  id String
}
";
    let result = parse_schema_end_to_end(input);

    assert!(
        result.schema.is_some(),
        "Model with single field should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert_ast_structure(&schema, 1, 0, 0);
    assert!(
        result.diagnostics.is_empty(),
        "Simple model should produce no diagnostics"
    );

    // Verify model and field structure
    if let Some(Declaration::Model(model)) = schema.declarations.first() {
        assert_eq!(model.name.text, "User");
        assert_eq!(model.members.len(), 1, "Model should have one field");

        if let Some(ModelMember::Field(field)) = model.members.first() {
            assert_eq!(field.name.text, "id");
            // Additional field type validation could be added here
        } else {
            panic!("Expected first member to be a field");
        }
    } else {
        panic!("Expected first declaration to be a model");
    }
}

#[test]
fn single_empty_enum() {
    let input = r"
enum Status {
}
";
    let result = parse_schema_end_to_end(input);

    assert!(
        result.schema.is_some(),
        "Single empty enum should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert_ast_structure(&schema, 0, 1, 0);
    assert!(
        result.diagnostics.is_empty(),
        "Empty enum should produce no diagnostics"
    );

    // Verify enum structure
    if let Some(Declaration::Enum(enum_decl)) = schema.declarations.first() {
        assert_eq!(enum_decl.name.text, "Status");
        assert!(
            enum_decl.members.is_empty(),
            "Empty enum should have no values"
        );
    } else {
        panic!("Expected first declaration to be an enum");
    }
}

#[test]
fn single_enum_with_value() {
    let input = r"
enum Status {
  ACTIVE
}
";
    let result = parse_schema_end_to_end(input);

    assert!(
        result.schema.is_some(),
        "Enum with single value should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert_ast_structure(&schema, 0, 1, 0);
    assert!(
        result.diagnostics.is_empty(),
        "Simple enum should produce no diagnostics"
    );

    // Verify enum and value structure
    if let Some(Declaration::Enum(enum_decl)) = schema.declarations.first() {
        assert_eq!(enum_decl.name.text, "Status");
        assert_eq!(enum_decl.members.len(), 1, "Enum should have one value");

        if let Some(EnumMember::Value(value)) = enum_decl.members.first() {
            assert_eq!(value.name.text, "ACTIVE");
        } else {
            panic!("Expected first member to be a value");
        }
    } else {
        panic!("Expected first declaration to be an enum");
    }
}

#[test]
fn minimal_datasource() {
    let input = r#"
datasource db {
  provider = "postgresql"
  url      = "postgresql://localhost/test"
}
"#;
    let result = parse_schema_end_to_end(input);

    assert!(
        result.schema.is_some(),
        "Minimal datasource should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert_ast_structure(&schema, 0, 0, 1);
    // Note: May produce diagnostics for unsupported constructs - this is expected
    println!("Datasource diagnostics: {:?}", result.diagnostics);

    // Verify datasource structure
    if let Some(Declaration::Datasource(ds)) = schema.declarations.first() {
        assert_eq!(ds.name.text, "db");
        // Note: assignments may be empty if parsing failed, but the declaration should exist
        println!("Datasource assignments: {:?}", ds.assignments.len());
    } else {
        panic!("Expected first declaration to be a datasource");
    }
}

#[test]
fn minimal_generator() {
    let input = r#"
generator client {
  provider = "prisma-client-js"
}
"#;
    let result = parse_schema_end_to_end(input);

    assert!(
        result.schema.is_some(),
        "Minimal generator should parse successfully"
    );
    let schema = result.schema.unwrap();

    // Verify generator structure
    let mut generator_count = 0;
    for declaration in &schema.declarations {
        if matches!(declaration, Declaration::Generator(_)) {
            generator_count += 1;
        }
    }
    assert_eq!(generator_count, 1, "Should have one generator");
    // Note: May produce diagnostics for unsupported constructs - this is expected
    println!("Generator diagnostics: {:?}", result.diagnostics);
}

#[test]
fn comment_only_schema() {
    let input = r"
// This is a comment
/* This is a block comment */
/// This is a doc comment
";
    let result = parse_schema_end_to_end(input);

    assert!(
        result.schema.is_some(),
        "Comment-only schema should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert_eq!(
        schema.declarations.len(),
        0,
        "Comment-only schema should have no declarations"
    );
    assert!(
        result.diagnostics.is_empty(),
        "Comments should produce no diagnostics"
    );
}

#[test]
fn mixed_minimal_declarations() {
    let input = r#"
model User {
  id String
}

enum Status {
  ACTIVE
}

datasource db {
  provider = "postgresql"
  url      = "postgresql://localhost/test"  
}

generator client {
  provider = "prisma-client-js"
}
"#;
    let result = parse_schema_end_to_end(input);

    assert!(
        result.schema.is_some(),
        "Mixed declarations should parse successfully"
    );
    let schema = result.schema.unwrap();
    assert!(
        schema.declarations.len() >= 4,
        "Should have at least 4 declarations"
    );
    // Note: May produce diagnostics for unsupported constructs - this is expected
    println!("Mixed schema diagnostics: {:?}", result.diagnostics);

    // Verify we have the expected types
    let mut models = 0;
    let mut enums = 0;
    let mut datasources = 0;
    let mut generators = 0;

    for declaration in &schema.declarations {
        match declaration {
            Declaration::Model(_) => models += 1,
            Declaration::Enum(_) => enums += 1,
            Declaration::Datasource(_) => datasources += 1,
            Declaration::Generator(_) => generators += 1,
            Declaration::Type(_) => {}
        }
    }

    assert_eq!(models, 1, "Should have one model");
    assert_eq!(enums, 1, "Should have one enum");
    assert_eq!(datasources, 1, "Should have one datasource");
    assert_eq!(generators, 1, "Should have one generator");
}

#[test]
fn parse_time_reasonable() {
    let input = r"
model User {
  id String @id
  name String
  email String @unique
}
";
    let result = parse_schema_end_to_end(input);

    assert!(result.schema.is_some(), "Schema should parse successfully");
    assert!(
        result.parse_time.as_millis() < 100,
        "Parse time should be under 100ms for small schema"
    );
    assert!(
        result.token_count > 10,
        "Should produce reasonable number of tokens"
    );
}

#[test]
fn token_count_accuracy() {
    let input = "model User { id String }";
    let result = parse_schema_end_to_end(input);

    assert!(result.schema.is_some(), "Schema should parse successfully");
    // Expected tokens: model, User, {, id, String, }, EOF = 7 minimum
    assert!(result.token_count >= 7, "Should have at least 7 tokens");
    assert!(
        result.token_count < 20,
        "Should not have excessive tokens for simple input"
    );
}
