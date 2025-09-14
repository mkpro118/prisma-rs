//! Integration tests for doc comment association across all parsers.

use crate::core::parser::components::attributes::{
    BlockAttributeParser, FieldAttributeParser,
};
use crate::core::parser::components::declarations::{
    DatasourceParser, EnumParser, GeneratorParser, ModelParser, TypeDeclParser,
};
use crate::core::parser::components::members::{
    AssignmentParser, EnumValueParser, FieldDeclParser,
};
use crate::core::parser::config::{FeatureSupport, ParserOptions};
use crate::core::parser::stream::VectorTokenStream;
use crate::core::parser::traits::Parser;
use crate::core::scanner::tokens::{Token, TokenType};

/// Helper to create a `DocComment` token.
fn doc_token(text: &str, line: u32) -> Token {
    Token::new(
        TokenType::DocComment(text.to_string()),
        (line, 1),
        (line, 4 + u32::try_from(text.len()).unwrap_or(0)),
    )
}

/// Helper to create other tokens.
fn tok(token_type: TokenType, line: u32) -> Token {
    Token::new(token_type, (line, 1), (line, 5))
}

fn ident(name: &str, line: u32) -> Token {
    Token::new(
        TokenType::Identifier(name.to_string()),
        (line, 1),
        (line, u32::try_from(name.len()).unwrap_or(0)),
    )
}

#[test]
fn model_with_doc_comments() {
    let mut parser = ModelParser;
    let tokens = vec![
        doc_token(" User model for authentication", 1),
        doc_token(" and authorization purposes", 2),
        tok(TokenType::Model, 3),
        ident("User", 3),
        tok(TokenType::LeftBrace, 3),
        tok(TokenType::RightBrace, 4),
    ];
    let mut stream = VectorTokenStream::new(tokens);
    let options = ParserOptions::default();

    let result = parser.parse(&mut stream, &options);

    assert!(result.value.is_some());
    let model = result.value.unwrap();
    assert_eq!(model.name.text, "User");

    // Check that docs were properly associated
    assert!(model.docs.is_some());
    let docs = model.docs.unwrap();
    assert_eq!(docs.lines.len(), 2);
    assert_eq!(docs.lines[0], "User model for authentication");
    assert_eq!(docs.lines[1], "and authorization purposes");
}

#[test]
fn enum_with_doc_comments() {
    let mut parser = EnumParser;
    let tokens = vec![
        doc_token(" User roles in the system", 1),
        tok(TokenType::Enum, 2),
        ident("Role", 2),
        tok(TokenType::LeftBrace, 2),
        tok(TokenType::RightBrace, 3),
    ];
    let mut stream = VectorTokenStream::new(tokens);
    let options = ParserOptions::default();

    let result = parser.parse(&mut stream, &options);

    assert!(result.value.is_some());
    let enum_decl = result.value.unwrap();
    assert_eq!(enum_decl.name.text, "Role");

    // Check docs
    assert!(enum_decl.docs.is_some());
    let docs = enum_decl.docs.unwrap();
    assert_eq!(docs.lines.len(), 1);
    assert_eq!(docs.lines[0], "User roles in the system");
}

#[test]
fn field_with_doc_comments() {
    let mut parser = FieldDeclParser;
    let tokens = vec![
        doc_token(" Primary key field", 1),
        ident("id", 2),
        tok(TokenType::String, 2),
    ];
    let mut stream = VectorTokenStream::new(tokens);
    let options = ParserOptions::default();

    let result = parser.parse(&mut stream, &options);

    assert!(result.value.is_some());
    let field = result.value.unwrap();
    assert_eq!(field.name.text, "id");

    // Check docs
    assert!(field.docs.is_some());
    let docs = field.docs.unwrap();
    assert_eq!(docs.lines.len(), 1);
    assert_eq!(docs.lines[0], "Primary key field");
}

#[test]
fn enum_value_with_doc_comments() {
    let mut parser = EnumValueParser;
    let tokens = vec![doc_token(" Administrator role", 1), ident("ADMIN", 2)];
    let mut stream = VectorTokenStream::new(tokens);
    let options = ParserOptions::default();

    let result = parser.parse(&mut stream, &options);

    assert!(result.value.is_some());
    let enum_value = result.value.unwrap();
    assert_eq!(enum_value.name.text, "ADMIN");

    // Check docs
    assert!(enum_value.docs.is_some());
    let docs = enum_value.docs.unwrap();
    assert_eq!(docs.lines.len(), 1);
    assert_eq!(docs.lines[0], "Administrator role");
}

#[test]
fn assignment_with_doc_comments() {
    let mut parser = AssignmentParser;
    let tokens = vec![
        doc_token(" Database provider configuration", 1),
        ident("provider", 2),
        tok(TokenType::Assign, 2),
        Token::new(
            TokenType::Literal("\"postgresql\"".to_string()),
            (2, 10),
            (2, 22),
        ),
    ];
    let mut stream = VectorTokenStream::new(tokens);
    let options = ParserOptions::default();

    let result = parser.parse(&mut stream, &options);

    assert!(result.value.is_some());
    let assignment = result.value.unwrap();
    assert_eq!(assignment.key.text, "provider");

    // Check docs
    assert!(assignment.docs.is_some());
    let docs = assignment.docs.unwrap();
    assert_eq!(docs.lines.len(), 1);
    assert_eq!(docs.lines[0], "Database provider configuration");
}

#[test]
fn field_attribute_with_doc_comments() {
    let mut parser = FieldAttributeParser::new();
    let tokens = vec![
        doc_token(" Primary key attribute", 1),
        tok(TokenType::At, 2),
        ident("id", 2),
    ];
    let mut stream = VectorTokenStream::new(tokens);
    let options = ParserOptions::default();

    let result = parser.parse(&mut stream, &options);

    assert!(result.value.is_some());
    let attr = result.value.unwrap();
    assert_eq!(attr.name.parts[0].text, "id");

    // Check docs
    assert!(attr.docs.is_some());
    let docs = attr.docs.unwrap();
    assert_eq!(docs.lines.len(), 1);
    assert_eq!(docs.lines[0], "Primary key attribute");
}

#[test]
fn block_attribute_with_doc_comments() {
    let mut parser = BlockAttributeParser::new();
    let tokens = vec![
        doc_token(" Unique constraint", 1),
        tok(TokenType::DoubleAt, 2),
        ident("unique", 2),
    ];
    let mut stream = VectorTokenStream::new(tokens);
    let options = ParserOptions::default();

    let result = parser.parse(&mut stream, &options);

    assert!(result.value.is_some());
    let attr = result.value.unwrap();
    assert_eq!(attr.name.parts[0].text, "unique");

    // Check docs
    assert!(attr.docs.is_some());
    let docs = attr.docs.unwrap();
    assert_eq!(docs.lines.len(), 1);
    assert_eq!(docs.lines[0], "Unique constraint");
}

#[test]
fn datasource_with_doc_comments() {
    let mut parser = DatasourceParser;
    let tokens = vec![
        doc_token(" Main database connection", 1),
        tok(TokenType::DataSource, 2),
        ident("db", 2),
        tok(TokenType::LeftBrace, 2),
        tok(TokenType::RightBrace, 3),
    ];
    let mut stream = VectorTokenStream::new(tokens);
    let options = ParserOptions::default();

    let result = parser.parse(&mut stream, &options);

    assert!(result.value.is_some());
    let datasource = result.value.unwrap();
    assert_eq!(datasource.name.text, "db");

    // Check docs
    assert!(datasource.docs.is_some());
    let docs = datasource.docs.unwrap();
    assert_eq!(docs.lines.len(), 1);
    assert_eq!(docs.lines[0], "Main database connection");
}

#[test]
fn generator_with_doc_comments() {
    let mut parser = GeneratorParser;
    let tokens = vec![
        doc_token(" Prisma client generator", 1),
        tok(TokenType::Generator, 2),
        ident("client", 2),
        tok(TokenType::LeftBrace, 2),
        tok(TokenType::RightBrace, 3),
    ];
    let mut stream = VectorTokenStream::new(tokens);
    let options = ParserOptions::default();

    let result = parser.parse(&mut stream, &options);

    assert!(result.value.is_some());
    let generator = result.value.unwrap();
    assert_eq!(generator.name.text, "client");

    // Check docs
    assert!(generator.docs.is_some());
    let docs = generator.docs.unwrap();
    assert_eq!(docs.lines.len(), 1);
    assert_eq!(docs.lines[0], "Prisma client generator");
}

#[test]
fn type_decl_with_doc_comments() {
    let mut parser = TypeDeclParser;
    let tokens = vec![
        doc_token(" Custom user ID type", 1),
        tok(TokenType::Type, 2),
        ident("UserId", 2),
        tok(TokenType::Assign, 2),
        ident("String", 2),
    ];
    let mut stream = VectorTokenStream::new(tokens);
    let options = ParserOptions {
        feature_support: FeatureSupport::WithExperimental,
        ..ParserOptions::default()
    };

    let result = parser.parse(&mut stream, &options);

    assert!(result.value.is_some());
    let type_decl = result.value.unwrap();
    assert_eq!(type_decl.name.text, "UserId");

    // Check docs
    assert!(type_decl.docs.is_some());
    let docs = type_decl.docs.unwrap();
    assert_eq!(docs.lines.len(), 1);
    assert_eq!(docs.lines[0], "Custom user ID type");
}
