//! Declaration parsers for top-level schema constructs.
//!
//! Implements the productions in `grammar/v1.md` for top-level declarations:
//! - `model_decl`      := MODEL ident `LEFT_BRACE` `model_member`* `RIGHT_BRACE`
//! - `enum_decl`       := ENUM ident `LEFT_BRACE` `enum_member`* `RIGHT_BRACE`
//! - `datasource_decl` := DATASOURCE ident `LEFT_BRACE` assignment* `RIGHT_BRACE`
//! - `generator_decl`  := GENERATOR ident `LEFT_BRACE` assignment* `RIGHT_BRACE`
//! - `type_decl`       := TYPE ident ASSIGN `type_ref`    /* experimental, gated */
//!
//! Each parser implements both `Parser<T>` and `ItemParser<T>` for uniform
//! dispatch in higher-level orchestration. `can_parse` checks the leading
//! keyword, ignoring comments via `peek_non_comment`.

use crate::core::parser::ast::{
    DatasourceDecl, Declaration, EnumDecl, EnumMember, GeneratorDecl, HasSpan,
    Ident, ModelDecl, ModelMember, TypeDecl,
};
use crate::core::parser::config::{
    Diagnostic, FeatureSupport, ParseResult, ParserOptions,
};
use crate::core::parser::stream::TokenStreamExt;
use crate::core::parser::traits::{
    DeclarationType, ItemParser, Parser, TokenStream,
};
use crate::core::scanner::tokens::{
    SymbolLocation, SymbolSpan, Token, TokenType,
};

use super::helpers::parse_leading_docs;
use super::members::{AssignmentParser, EnumMemberParser, ModelMemberParser};
use super::types::TypeRefParser;

/// Build a span from the start of `a` to the end of `b`.
fn span_from_to(a: &SymbolSpan, b: &SymbolSpan) -> SymbolSpan {
    SymbolSpan {
        start: SymbolLocation {
            line: a.start.line,
            column: a.start.column,
        },
        end: SymbolLocation {
            line: b.end.line,
            column: b.end.column,
        },
    }
}

/// Clone a token's span.
fn tspan(t: &Token) -> SymbolSpan {
    t.span().clone()
}

/// Convert an identifier token into an `Ident` AST node.
fn ident_from_token(tok: &Token) -> Option<Ident> {
    match tok.r#type() {
        TokenType::Identifier(s) => Some(Ident {
            text: s.clone(),
            span: tspan(tok),
        }),
        _ => None,
    }
}

/// Build an error diagnostic at `current` or a default position.
fn expected_diag(current: Option<&Token>, msg: &str) -> Diagnostic {
    let span = current.map_or(
        SymbolSpan {
            start: SymbolLocation { line: 0, column: 0 },
            end: SymbolLocation { line: 0, column: 0 },
        },
        tspan,
    );
    Diagnostic::error(span, msg)
}

/// Parses: `model ident { model_member* }`
#[derive(Debug, Default)]
pub struct ModelParser;

impl Parser<ModelDecl> for ModelParser {
    /// Parse a model declaration block.
    ///
    /// Consumes `model`, a name, and a braced block containing model members.
    /// Spans cover from the `model` keyword through the closing brace.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::parser::components::declarations::ModelParser;
    /// # use prisma_rs::core::parser::traits::Parser;
    /// # use prisma_rs::core::parser::stream::VectorTokenStream;
    /// # use prisma_rs::core::parser::config::ParserOptions;
    /// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
    /// let mut s = VectorTokenStream::new(vec![
    ///     Token::new(TokenType::Model, (1, 1), (1, 5)),
    ///     Token::new(TokenType::Identifier("User".into()), (1, 7), (1, 10)),
    ///     Token::new(TokenType::LeftBrace, (1, 12), (1, 12)),
    ///     Token::new(TokenType::RightBrace, (1, 13), (1, 13)),
    /// ]);
    /// let mut p = ModelParser::default();
    /// let m = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
    /// assert_eq!(m.name.text, "User");
    /// ```
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<ModelDecl> {
        // Parse leading documentation comments
        let docs = parse_leading_docs(stream);

        // Consume 'model' keyword
        let Some(model_tok) = stream.match_token(TokenType::Model) else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected 'model' keyword",
            ));
        };

        // Model name
        let Some(name_tok) = stream.next() else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected model name after 'model'",
            ));
        };
        let Some(name_ident) = ident_from_token(&name_tok) else {
            return ParseResult::error(expected_diag(
                Some(&name_tok),
                "expected identifier for model name",
            ));
        };

        // Opening brace
        let Some(_open_brace) = stream.match_token(TokenType::LeftBrace) else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected '{' after model name",
            ));
        };

        // Parse members
        let mut members = Vec::new();
        let mut attrs = Vec::new();
        let mut diags = Vec::new();
        let mut member_parser = ModelMemberParser;

        while !stream.check(TokenType::RightBrace) && !stream.is_at_end() {
            if member_parser.can_parse(stream) {
                let mut res = member_parser.parse(stream, options);
                diags.append(&mut res.diagnostics);

                if let Some(member) = res.value.take() {
                    // Separate block attributes from regular members
                    if let ModelMember::BlockAttribute(attr) = member {
                        attrs.push(attr);
                    } else {
                        members.push(member);
                    }
                } else {
                    // Failed to parse member, attempt error recovery
                    if !stream.synchronize_to(&[
                        TokenType::RightBrace,
                        TokenType::DoubleAt,
                    ]) {
                        break;
                    }
                }
            } else {
                // Invalid start for a member; synchronize like Enum parser
                if !stream.synchronize_to(&[
                    TokenType::RightBrace,
                    TokenType::DoubleAt,
                ]) {
                    break;
                }
            }
        }

        // Closing brace
        let Some(close_brace) = stream.match_token(TokenType::RightBrace)
        else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected '}' to close model block",
            ));
        };

        let span = span_from_to(&tspan(&model_tok), &tspan(&close_brace));
        let mut result = ParseResult::success(ModelDecl {
            name: name_ident,
            members,
            attrs,
            docs,
            span,
        });
        result.diagnostics.append(&mut diags);
        result
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        stream.check_non_comment(TokenType::Model)
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::RightBrace,
            TokenType::Model,
            TokenType::Enum,
            TokenType::DataSource,
            TokenType::Generator,
            TokenType::Type,
        ]
    }
}

impl ItemParser<ModelDecl> for ModelParser {
    fn declaration_type(&self) -> DeclarationType {
        DeclarationType::Model
    }

    fn to_declaration(&self, item: ModelDecl) -> Declaration {
        Declaration::Model(item)
    }
}

/// Parses: `enum ident { enum_member* }`
#[derive(Debug, Default)]
pub struct EnumParser;

impl Parser<EnumDecl> for EnumParser {
    /// Parse an enum declaration block.
    ///
    /// Consumes `enum`, a name, and a braced block containing enum members.
    /// Spans cover from the `enum` keyword through the closing brace.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::parser::components::declarations::EnumParser;
    /// # use prisma_rs::core::parser::traits::Parser;
    /// # use prisma_rs::core::parser::stream::VectorTokenStream;
    /// # use prisma_rs::core::parser::config::ParserOptions;
    /// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
    /// let mut s = VectorTokenStream::new(vec![
    ///     Token::new(TokenType::Enum, (1, 1), (1, 4)),
    ///     Token::new(TokenType::Identifier("Role".into()), (1, 6), (1, 9)),
    ///     Token::new(TokenType::LeftBrace, (1, 11), (1, 11)),
    ///     Token::new(TokenType::RightBrace, (1, 12), (1, 12)),
    /// ]);
    /// let mut p = EnumParser::default();
    /// let e = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
    /// assert_eq!(e.name.text, "Role");
    /// ```
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<EnumDecl> {
        // Parse leading documentation comments
        let docs = parse_leading_docs(stream);

        // Consume 'enum' keyword
        let Some(enum_tok) = stream.match_token(TokenType::Enum) else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected 'enum' keyword",
            ));
        };

        // Enum name
        let Some(name_tok) = stream.next() else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected enum name after 'enum'",
            ));
        };
        let Some(name_ident) = ident_from_token(&name_tok) else {
            return ParseResult::error(expected_diag(
                Some(&name_tok),
                "expected identifier for enum name",
            ));
        };

        // Opening brace
        let Some(_open_brace) = stream.match_token(TokenType::LeftBrace) else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected '{' after enum name",
            ));
        };

        // Parse members
        let mut members = Vec::new();
        let mut attrs = Vec::new();
        let mut diags = Vec::new();
        let mut member_parser = EnumMemberParser;

        while !stream.check(TokenType::RightBrace) && !stream.is_at_end() {
            if member_parser.can_parse(stream) {
                let mut res = member_parser.parse(stream, options);
                diags.append(&mut res.diagnostics);

                if let Some(member) = res.value.take() {
                    match member {
                        EnumMember::BlockAttribute(attr) => attrs.push(attr),
                        EnumMember::Value(v) => {
                            members.push(EnumMember::Value(v));
                        }
                    }
                } else {
                    // Failed to parse member, attempt error recovery
                    if !stream.synchronize_to(&[
                        TokenType::RightBrace,
                        TokenType::DoubleAt,
                    ]) {
                        break;
                    }
                }
            } else {
                // Failed to parse member, attempt error recovery
                if !stream.synchronize_to(&[
                    TokenType::RightBrace,
                    TokenType::DoubleAt,
                ]) {
                    break;
                }
            }
        }

        // Closing brace
        let Some(close_brace) = stream.match_token(TokenType::RightBrace)
        else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected '}' to close enum block",
            ));
        };

        let span = span_from_to(&tspan(&enum_tok), &tspan(&close_brace));
        let mut result = ParseResult::success(EnumDecl {
            name: name_ident,
            members,
            attrs,
            docs,
            span,
        });
        result.diagnostics.append(&mut diags);
        result
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        stream.check_non_comment(TokenType::Enum)
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::RightBrace,
            TokenType::Model,
            TokenType::Enum,
            TokenType::DataSource,
            TokenType::Generator,
            TokenType::Type,
        ]
    }
}

impl ItemParser<EnumDecl> for EnumParser {
    fn declaration_type(&self) -> DeclarationType {
        DeclarationType::Enum
    }

    fn to_declaration(&self, item: EnumDecl) -> Declaration {
        Declaration::Enum(item)
    }
}

/// Parses: `datasource ident { assignment* }`
#[derive(Debug, Default)]
pub struct DatasourceParser;

impl Parser<DatasourceDecl> for DatasourceParser {
    /// Parse a datasource declaration block.
    ///
    /// Consumes `datasource`, a name, and a braced block containing
    /// assignments. Spans cover from the keyword through the closing brace.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::parser::components::declarations::DatasourceParser;
    /// # use prisma_rs::core::parser::traits::Parser;
    /// # use prisma_rs::core::parser::stream::VectorTokenStream;
    /// # use prisma_rs::core::parser::config::ParserOptions;
    /// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
    /// let mut s = VectorTokenStream::new(vec![
    ///     Token::new(TokenType::DataSource, (1,1), (1,10)),
    ///     Token::new(TokenType::Identifier("db".into()), (1,12), (1,13)),
    ///     Token::new(TokenType::LeftBrace, (1,15), (1,15)),
    ///     Token::new(TokenType::RightBrace, (1,16), (1,16)),
    /// ]);
    /// let mut p = DatasourceParser::default();
    /// let d = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
    /// assert_eq!(d.name.text, "db");
    /// ```
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<DatasourceDecl> {
        // Parse leading documentation comments
        let docs = parse_leading_docs(stream);

        // Consume 'datasource' keyword
        let Some(datasource_tok) = stream.match_token(TokenType::DataSource)
        else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected 'datasource' keyword",
            ));
        };

        // Datasource name
        let Some(name_tok) = stream.next() else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected datasource name after 'datasource'",
            ));
        };
        let Some(name_ident) = ident_from_token(&name_tok) else {
            return ParseResult::error(expected_diag(
                Some(&name_tok),
                "expected identifier for datasource name",
            ));
        };

        // Opening brace
        let Some(_open_brace) = stream.match_token(TokenType::LeftBrace) else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected '{' after datasource name",
            ));
        };

        // Parse assignments
        let mut assignments = Vec::new();
        let mut diags = Vec::new();
        let mut assignment_parser = AssignmentParser;

        while !stream.check(TokenType::RightBrace) && !stream.is_at_end() {
            if assignment_parser.can_parse(stream) {
                let mut res = assignment_parser.parse(stream, options);
                diags.append(&mut res.diagnostics);

                if let Some(assignment) = res.value.take() {
                    assignments.push(assignment);
                } else {
                    // Failed to parse assignment, attempt error recovery
                    if !stream.synchronize_to(&[TokenType::RightBrace]) {
                        break;
                    }
                }
            } else {
                // Can't parse as assignment, this might be a syntax error
                diags.push(expected_diag(stream.peek(), "expected assignment"));
                if !stream.synchronize_to(&[TokenType::RightBrace]) {
                    break;
                }
            }
        }

        // Closing brace
        let Some(close_brace) = stream.match_token(TokenType::RightBrace)
        else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected '}' to close datasource block",
            ));
        };

        let span = span_from_to(&tspan(&datasource_tok), &tspan(&close_brace));
        let mut result = ParseResult::success(DatasourceDecl {
            name: name_ident,
            assignments,
            docs,
            span,
        });
        result.diagnostics.append(&mut diags);
        result
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        stream.check_non_comment(TokenType::DataSource)
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::RightBrace,
            TokenType::Model,
            TokenType::Enum,
            TokenType::DataSource,
            TokenType::Generator,
            TokenType::Type,
        ]
    }
}

impl ItemParser<DatasourceDecl> for DatasourceParser {
    fn declaration_type(&self) -> DeclarationType {
        DeclarationType::Datasource
    }

    fn to_declaration(&self, item: DatasourceDecl) -> Declaration {
        Declaration::Datasource(item)
    }
}

/// Parses: `generator ident { assignment* }`
#[derive(Debug, Default)]
pub struct GeneratorParser;

impl Parser<GeneratorDecl> for GeneratorParser {
    /// Parse a generator declaration block.
    ///
    /// Consumes `generator`, a name, and a braced block containing
    /// assignments. Spans cover from the keyword through the closing brace.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::parser::components::declarations::GeneratorParser;
    /// # use prisma_rs::core::parser::traits::Parser;
    /// # use prisma_rs::core::parser::stream::VectorTokenStream;
    /// # use prisma_rs::core::parser::config::ParserOptions;
    /// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
    /// let mut s = VectorTokenStream::new(vec![
    ///     Token::new(TokenType::Generator, (1,1), (1,9)),
    ///     Token::new(TokenType::Identifier("client".into()), (1,11), (1,16)),
    ///     Token::new(TokenType::LeftBrace, (1,18), (1,18)),
    ///     Token::new(TokenType::RightBrace, (1,19), (1,19)),
    /// ]);
    /// let mut p = GeneratorParser::default();
    /// let g = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
    /// assert_eq!(g.name.text, "client");
    /// ```
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<GeneratorDecl> {
        // Parse leading documentation comments
        let docs = parse_leading_docs(stream);

        // Consume 'generator' keyword
        let Some(generator_tok) = stream.match_token(TokenType::Generator)
        else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected 'generator' keyword",
            ));
        };

        // Generator name
        let Some(name_tok) = stream.next() else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected generator name after 'generator'",
            ));
        };
        let Some(name_ident) = ident_from_token(&name_tok) else {
            return ParseResult::error(expected_diag(
                Some(&name_tok),
                "expected identifier for generator name",
            ));
        };

        // Opening brace
        let Some(_open_brace) = stream.match_token(TokenType::LeftBrace) else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected '{' after generator name",
            ));
        };

        // Parse assignments
        let mut assignments = Vec::new();
        let mut diags = Vec::new();
        let mut assignment_parser = AssignmentParser;

        while !stream.check(TokenType::RightBrace) && !stream.is_at_end() {
            if assignment_parser.can_parse(stream) {
                let mut res = assignment_parser.parse(stream, options);
                diags.append(&mut res.diagnostics);

                if let Some(assignment) = res.value.take() {
                    assignments.push(assignment);
                } else {
                    // Failed to parse assignment, attempt error recovery
                    if !stream.synchronize_to(&[TokenType::RightBrace]) {
                        break;
                    }
                }
            } else {
                // Can't parse as assignment, this might be a syntax error
                diags.push(expected_diag(stream.peek(), "expected assignment"));
                if !stream.synchronize_to(&[TokenType::RightBrace]) {
                    break;
                }
            }
        }

        // Closing brace
        let Some(close_brace) = stream.match_token(TokenType::RightBrace)
        else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected '}' to close generator block",
            ));
        };

        let span = span_from_to(&tspan(&generator_tok), &tspan(&close_brace));
        let mut result = ParseResult::success(GeneratorDecl {
            name: name_ident,
            assignments,
            docs,
            span,
        });
        result.diagnostics.append(&mut diags);
        result
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        stream.check_non_comment(TokenType::Generator)
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::RightBrace,
            TokenType::Model,
            TokenType::Enum,
            TokenType::DataSource,
            TokenType::Generator,
            TokenType::Type,
        ]
    }
}

impl ItemParser<GeneratorDecl> for GeneratorParser {
    fn declaration_type(&self) -> DeclarationType {
        DeclarationType::Generator
    }

    fn to_declaration(&self, item: GeneratorDecl) -> Declaration {
        Declaration::Generator(item)
    }
}

/// Parses: `type ident = type_ref` (experimental feature, gated)
#[derive(Debug, Default)]
pub struct TypeDeclParser;

impl Parser<TypeDecl> for TypeDeclParser {
    /// Parse an experimental type alias declaration.
    ///
    /// Requires `ParserOptions.feature_support = FeatureSupport::WithExperimental`.
    /// Spans cover from the `type` keyword through the aliased type.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::parser::components::declarations::TypeDeclParser;
    /// # use prisma_rs::core::parser::traits::Parser;
    /// # use prisma_rs::core::parser::stream::VectorTokenStream;
    /// # use prisma_rs::core::parser::config::{ParserOptions, FeatureSupport};
    /// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
    /// let mut s = VectorTokenStream::new(vec![
    ///     Token::new(TokenType::Type, (1,1), (1,4)),
    ///     Token::new(TokenType::Identifier("UserId".into()), (1,6), (1,11)),
    ///     Token::new(TokenType::Assign, (1,13), (1,13)),
    ///     Token::new(TokenType::String, (1,15), (1,20)),
    /// ]);
    /// let mut p = TypeDeclParser::default();
    /// let mut opts = ParserOptions::default();
    /// opts.feature_support = FeatureSupport::WithExperimental;
    /// let t = p.parse(&mut s, &opts).value.unwrap();
    /// assert_eq!(t.name.text, "UserId");
    /// ```
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &ParserOptions,
    ) -> ParseResult<TypeDecl> {
        // Parse leading documentation comments
        let docs = parse_leading_docs(stream);

        // Consume 'type' keyword first to avoid infinite loops
        let Some(type_tok) = stream.match_token(TokenType::Type) else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected 'type' keyword",
            ));
        };

        // Check if experimental type declarations are enabled
        if options.feature_support != FeatureSupport::WithExperimental {
            return ParseResult::error(expected_diag(
                Some(&type_tok),
                "type declarations require enabling experimental features",
            ));
        }

        // Type alias name
        let Some(name_tok) = stream.next() else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected type name after 'type'",
            ));
        };
        let Some(name_ident) = ident_from_token(&name_tok) else {
            return ParseResult::error(expected_diag(
                Some(&name_tok),
                "expected identifier for type name",
            ));
        };

        // Assignment operator
        let Some(_assign_tok) = stream.match_token(TokenType::Assign) else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected '=' after type name",
            ));
        };

        // Parse the aliased type
        let mut type_parser = TypeRefParser::default();
        let mut type_res = type_parser.parse(stream, options);
        let Some(rhs_type) = type_res.value.take() else {
            let mut result = ParseResult::error(expected_diag(
                stream.peek(),
                "expected type reference after '='",
            ));
            result.diagnostics.append(&mut type_res.diagnostics);
            return result;
        };

        let span = span_from_to(&tspan(&type_tok), rhs_type.span());
        let mut result = ParseResult::success(TypeDecl {
            name: name_ident,
            rhs: rhs_type,
            docs,
            span,
        });
        result.diagnostics.append(&mut type_res.diagnostics);
        result
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        stream.check_non_comment(TokenType::Type)
    }

    fn sync_tokens(&self) -> &[TokenType] {
        &[
            TokenType::Model,
            TokenType::Enum,
            TokenType::DataSource,
            TokenType::Generator,
            TokenType::Type,
        ]
    }
}

impl ItemParser<TypeDecl> for TypeDeclParser {
    fn declaration_type(&self) -> DeclarationType {
        DeclarationType::Type
    }

    fn to_declaration(&self, item: TypeDecl) -> Declaration {
        Declaration::Type(item)
    }
}

/// Creates a `Declaration` enum variant from a parsed declaration parser result.
pub trait DeclarationWrapper<T> {
    fn wrap_declaration(value: T) -> Declaration;
}

impl DeclarationWrapper<ModelDecl> for ModelParser {
    fn wrap_declaration(value: ModelDecl) -> Declaration {
        Declaration::Model(value)
    }
}

impl DeclarationWrapper<EnumDecl> for EnumParser {
    fn wrap_declaration(value: EnumDecl) -> Declaration {
        Declaration::Enum(value)
    }
}

impl DeclarationWrapper<DatasourceDecl> for DatasourceParser {
    fn wrap_declaration(value: DatasourceDecl) -> Declaration {
        Declaration::Datasource(value)
    }
}

impl DeclarationWrapper<GeneratorDecl> for GeneratorParser {
    fn wrap_declaration(value: GeneratorDecl) -> Declaration {
        Declaration::Generator(value)
    }
}

impl DeclarationWrapper<TypeDecl> for TypeDeclParser {
    fn wrap_declaration(value: TypeDecl) -> Declaration {
        Declaration::Type(value)
    }
}

#[cfg(test)]
mod tests {
    #![expect(clippy::unwrap_used)]

    use crate::core::parser::components::declarations::{
        DatasourceParser, EnumParser, GeneratorParser, ModelParser,
        TypeDeclParser,
    };
    use crate::core::parser::config::{FeatureSupport, ParserOptions};
    use crate::core::parser::stream::VectorTokenStream;
    use crate::core::parser::traits::{ItemParser, Parser};
    use crate::core::scanner::tokens::{Token, TokenType};

    /// Helper to create a test token.
    fn tok(token_type: TokenType) -> Token {
        Token::new(token_type, (1, 1), (1, 5))
    }

    /// Helper to create an identifier token.
    fn ident(name: &str) -> Token {
        tok(TokenType::Identifier(name.to_string()))
    }

    /// Helper to create a literal token.
    fn lit(value: &str) -> Token {
        tok(TokenType::Literal(format!("\"{value}\"")))
    }

    #[test]
    fn enum_parser_collects_block_attrs_and_values() {
        let mut parser = EnumParser;
        // enum Role { @@map("role") ADMIN @map("admin") }
        let tokens = vec![
            tok(TokenType::Enum),
            ident("Role"),
            tok(TokenType::LeftBrace),
            // @@map("role")
            tok(TokenType::DoubleAt),
            ident("map"),
            tok(TokenType::LeftParen),
            lit("role"),
            tok(TokenType::RightParen),
            // ADMIN @map("admin")
            ident("ADMIN"),
            tok(TokenType::At),
            ident("map"),
            tok(TokenType::LeftParen),
            lit("admin"),
            tok(TokenType::RightParen),
            tok(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);
        assert!(
            result.value.is_some(),
            "parse should succeed: {:?}",
            result.diagnostics
        );
        let enum_decl = result.value.unwrap();

        // One block attribute collected separately
        assert_eq!(enum_decl.attrs.len(), 1);

        // One member which is a value, carrying its field attribute
        assert_eq!(enum_decl.members.len(), 1);
        match &enum_decl.members[0] {
            crate::core::parser::ast::EnumMember::Value(v) => {
                assert_eq!(v.name.text, "ADMIN");
                assert_eq!(v.attrs.len(), 1);
            }
            crate::core::parser::ast::EnumMember::BlockAttribute(_) => {
                panic!("expected enum value member")
            }
        }
    }

    #[test]
    fn enum_parser_error_recovery_on_invalid_member_token() {
        let mut parser = EnumParser;
        // enum E { @ }  -> '@' cannot start enum member; parser should recover to '}'
        let tokens = vec![
            tok(TokenType::Enum),
            ident("E"),
            tok(TokenType::LeftBrace),
            tok(TokenType::At), // invalid start for enum member
            tok(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);
        // Should produce a value with empty members/attrs and not crash
        assert!(result.value.is_some());
        let enum_decl = result.value.unwrap();
        assert!(enum_decl.members.is_empty());
        // Some diagnostics are expected or at least allowed
    }

    #[test]
    fn model_parser_error_recovery_on_invalid_member_token() {
        let mut parser = ModelParser;
        // model M { @ }  -> '@' cannot start model member; parser should recover to '}'
        let tokens = vec![
            tok(TokenType::Model),
            ident("M"),
            tok(TokenType::LeftBrace),
            tok(TokenType::At), // invalid start for model member
            tok(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);
        // Should produce a value with empty members/attrs and not crash
        assert!(result.value.is_some());
        let model_decl = result.value.unwrap();
        assert!(model_decl.members.is_empty());
        assert!(model_decl.attrs.is_empty());
        // Some diagnostics are expected or at least allowed
    }

    #[test]
    fn model_parser_can_parse() {
        let parser = ModelParser;

        // Should parse when starts with 'model'
        let stream = VectorTokenStream::new(vec![tok(TokenType::Model)]);
        assert!(parser.can_parse(&stream));

        // Should not parse when doesn't start with 'model'
        let stream = VectorTokenStream::new(vec![tok(TokenType::Enum)]);
        assert!(!parser.can_parse(&stream));

        // Should not parse empty stream
        let stream = VectorTokenStream::new(vec![]);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn model_parser_item_type() {
        let parser = ModelParser;
        assert_eq!(parser.item_type().to_lowercase(), "model");
    }

    #[test]
    fn model_parser_simple_empty_model() {
        let mut parser = ModelParser;
        let tokens = vec![
            tok(TokenType::Model),
            ident("User"),
            tok(TokenType::LeftBrace),
            tok(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.value.is_some());
        let model = result.value.unwrap();
        assert_eq!(model.name.text, "User");
        assert!(model.members.is_empty());
        assert!(model.attrs.is_empty());
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn enum_parser_can_parse() {
        let parser = EnumParser;

        // Should parse when starts with 'enum'
        let stream = VectorTokenStream::new(vec![tok(TokenType::Enum)]);
        assert!(parser.can_parse(&stream));

        // Should not parse when doesn't start with 'enum'
        let stream = VectorTokenStream::new(vec![tok(TokenType::Model)]);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn enum_parser_item_type() {
        let parser = EnumParser;
        assert_eq!(parser.item_type().to_lowercase(), "enum");
    }

    #[test]
    fn enum_parser_simple_empty_enum() {
        let mut parser = EnumParser;
        let tokens = vec![
            tok(TokenType::Enum),
            ident("Role"),
            tok(TokenType::LeftBrace),
            tok(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.value.is_some());
        let enum_decl = result.value.unwrap();
        assert_eq!(enum_decl.name.text, "Role");
        assert!(enum_decl.members.is_empty());
        assert!(enum_decl.attrs.is_empty());
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn datasource_parser_can_parse() {
        let parser = DatasourceParser;

        // Should parse when starts with 'datasource'
        let stream = VectorTokenStream::new(vec![tok(TokenType::DataSource)]);
        assert!(parser.can_parse(&stream));

        // Should not parse when doesn't start with 'datasource'
        let stream = VectorTokenStream::new(vec![tok(TokenType::Generator)]);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn datasource_parser_item_type() {
        let parser = DatasourceParser;
        assert_eq!(parser.item_type().to_lowercase(), "datasource");
    }

    #[test]
    fn datasource_parser_simple_empty_datasource() {
        let mut parser = DatasourceParser;
        let tokens = vec![
            tok(TokenType::DataSource),
            ident("db"),
            tok(TokenType::LeftBrace),
            tok(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.value.is_some());
        let datasource = result.value.unwrap();
        assert_eq!(datasource.name.text, "db");
        assert!(datasource.assignments.is_empty());
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn datasource_parser_with_assignment() {
        let mut parser = DatasourceParser;
        let tokens = vec![
            tok(TokenType::DataSource),
            ident("db"),
            tok(TokenType::LeftBrace),
            ident("provider"),
            tok(TokenType::Assign),
            lit("postgresql"),
            tok(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        if result.value.is_none() {
            println!("Result value is None");
            println!("Diagnostics: {:?}", result.diagnostics);
        }
        assert!(result.value.is_some());
        let datasource = result.value.unwrap();
        assert_eq!(datasource.name.text, "db");

        // Check that there are no errors
        assert!(result.diagnostics.iter().all(|d| !matches!(
            d.severity,
            crate::core::parser::config::DiagnosticSeverity::Error
        )));

        assert_eq!(datasource.assignments.len(), 1);
        assert_eq!(datasource.assignments[0].key.text, "provider");
        // Note: We can't easily test the expression value without more complex setup
    }

    #[test]
    fn generator_parser_can_parse() {
        let parser = GeneratorParser;

        // Should parse when starts with 'generator'
        let stream = VectorTokenStream::new(vec![tok(TokenType::Generator)]);
        assert!(parser.can_parse(&stream));

        // Should not parse when doesn't start with 'generator'
        let stream = VectorTokenStream::new(vec![tok(TokenType::DataSource)]);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn generator_parser_item_type() {
        let parser = GeneratorParser;
        assert_eq!(parser.item_type().to_lowercase(), "generator");
    }

    #[test]
    fn generator_parser_simple_empty_generator() {
        let mut parser = GeneratorParser;
        let tokens = vec![
            tok(TokenType::Generator),
            ident("client"),
            tok(TokenType::LeftBrace),
            tok(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.value.is_some());
        let generator = result.value.unwrap();
        assert_eq!(generator.name.text, "client");
        assert!(generator.assignments.is_empty());
        assert!(result.diagnostics.is_empty());
    }

    #[test]
    fn type_decl_parser_can_parse() {
        let parser = TypeDeclParser;

        // Should parse when starts with 'type'
        let stream = VectorTokenStream::new(vec![tok(TokenType::Type)]);
        assert!(parser.can_parse(&stream));

        // Should not parse when doesn't start with 'type'
        let stream = VectorTokenStream::new(vec![tok(TokenType::Model)]);
        assert!(!parser.can_parse(&stream));
    }

    #[test]
    fn model_parser_can_parse_with_comments() {
        let parser = ModelParser;
        let tokens = vec![
            tok(TokenType::Comment("// comment".to_string())),
            tok(TokenType::DocComment("/// doc comment".to_string())),
            tok(TokenType::Model),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));
    }

    #[test]
    fn enum_parser_can_parse_with_comments() {
        let parser = EnumParser;
        let tokens = vec![
            tok(TokenType::Comment("// comment".to_string())),
            tok(TokenType::DocComment("/// doc comment".to_string())),
            tok(TokenType::Enum),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));
    }

    #[test]
    fn datasource_parser_can_parse_with_comments() {
        let parser = DatasourceParser;
        let tokens = vec![
            tok(TokenType::Comment("// comment".to_string())),
            tok(TokenType::DocComment("/// doc comment".to_string())),
            tok(TokenType::DataSource),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));
    }

    #[test]
    fn generator_parser_can_parse_with_comments() {
        let parser = GeneratorParser;
        let tokens = vec![
            tok(TokenType::Comment("// comment".to_string())),
            tok(TokenType::DocComment("/// doc comment".to_string())),
            tok(TokenType::Generator),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));
    }

    #[test]
    fn type_decl_parser_can_parse_with_comments() {
        let parser = TypeDeclParser;
        let tokens = vec![
            tok(TokenType::Comment("// comment".to_string())),
            tok(TokenType::DocComment("/// doc comment".to_string())),
            tok(TokenType::Type),
        ];
        let stream = VectorTokenStream::new(tokens);
        assert!(parser.can_parse(&stream));
    }

    #[test]
    fn type_decl_parser_item_type() {
        let parser = TypeDeclParser;
        assert_eq!(parser.item_type().to_lowercase(), "type");
    }

    #[test]
    fn type_decl_parser_experimental_disabled() {
        let mut parser = TypeDeclParser;
        let tokens = vec![
            tok(TokenType::Type),
            ident("UserId"),
            tok(TokenType::Assign),
            tok(TokenType::String),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions {
            feature_support: FeatureSupport::StableOnly,
            ..ParserOptions::default()
        };

        let result = parser.parse(&mut stream, &options);

        assert!(result.value.is_none());
        assert!(!result.diagnostics.is_empty());
        assert!(result.diagnostics[0].message.contains("experimental"));
    }

    #[test]
    fn type_decl_parser_simple_type_alias() {
        let mut parser = TypeDeclParser;
        let tokens = vec![
            tok(TokenType::Type),
            ident("UserId"),
            tok(TokenType::Assign),
            ident("String"),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions {
            feature_support: FeatureSupport::WithExperimental,
            ..ParserOptions::default()
        };

        let result = parser.parse(&mut stream, &options);

        // Should succeed without errors
        assert!(result.value.is_some());
        let type_decl = result.value.unwrap();
        assert_eq!(type_decl.name.text, "UserId");
        // Note: We can't easily test the RHS type without more complex setup
    }

    #[test]
    fn model_parser_missing_name() {
        let mut parser = ModelParser;
        let tokens = vec![tok(TokenType::Model), tok(TokenType::LeftBrace)];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.value.is_none());
        assert!(!result.diagnostics.is_empty());
        assert!(result.diagnostics[0].message.contains("model name"));
    }

    #[test]
    fn model_parser_missing_opening_brace() {
        let mut parser = ModelParser;
        let tokens = vec![
            tok(TokenType::Model),
            ident("User"),
            tok(TokenType::RightBrace),
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.value.is_none());
        assert!(!result.diagnostics.is_empty());
        assert!(result.diagnostics[0].message.contains("'{'"));
    }

    #[test]
    fn model_parser_missing_closing_brace() {
        let mut parser = ModelParser;
        let tokens = vec![
            tok(TokenType::Model),
            ident("User"),
            tok(TokenType::LeftBrace),
            // Missing closing brace - EOF
        ];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.value.is_none());
        assert!(!result.diagnostics.is_empty());
        assert!(result.diagnostics[0].message.contains("'}'"));
    }

    #[test]
    fn enum_parser_missing_name() {
        let mut parser = EnumParser;
        let tokens = vec![tok(TokenType::Enum), tok(TokenType::LeftBrace)];
        let mut stream = VectorTokenStream::new(tokens);
        let options = ParserOptions::default();

        let result = parser.parse(&mut stream, &options);

        assert!(result.value.is_none());
        assert!(!result.diagnostics.is_empty());
        assert!(result.diagnostics[0].message.contains("enum name"));
    }

    #[test]
    fn sync_tokens_include_top_level_keywords() {
        let model_parser = ModelParser;
        let enum_parser = EnumParser;
        let datasource_parser = DatasourceParser;
        let generator_parser = GeneratorParser;
        let type_parser = TypeDeclParser;

        // All declaration parsers should have synchronization tokens for recovery
        assert!(!model_parser.sync_tokens().is_empty());
        assert!(!enum_parser.sync_tokens().is_empty());
        assert!(!datasource_parser.sync_tokens().is_empty());
        assert!(!generator_parser.sync_tokens().is_empty());
        assert!(!type_parser.sync_tokens().is_empty());

        // They should all include top-level keywords for recovery
        assert!(model_parser.sync_tokens().contains(&TokenType::Model));
        assert!(enum_parser.sync_tokens().contains(&TokenType::Model));
        assert!(datasource_parser.sync_tokens().contains(&TokenType::Model));
    }
}
