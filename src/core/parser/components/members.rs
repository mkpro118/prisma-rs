//! Parsers for declaration members (fields, enum values, assignments).
//!
//! Implements the productions in `grammar.md` for members:
//! - `field_decl`    := ident `type_ref` `opt_marker`? `field_attribute`*
//! - `enum_value`    := ident `field_attribute`*
//! - assignment    := ident ASSIGN expr
//! - `model_member`  := `field_decl` | `block_attribute`
//! - `enum_member`   := `enum_value` | `block_attribute`

use crate::core::parser::ast::{
    Assignment, BlockAttribute, EnumMember, EnumValue, FieldAttribute,
    FieldDecl, HasSpan, Ident, ListType, ModelMember, NamedType,
    QualifiedIdent, TypeRef,
};
use crate::core::parser::config::{Diagnostic, ParseResult};
use crate::core::parser::stream::TokenStreamExt;
use crate::core::parser::traits::{Parser, TokenStream};
use crate::core::scanner::tokens::{
    SymbolLocation, SymbolSpan, Token, TokenType,
};

use super::attributes::{BlockAttributeParser, FieldAttributeParser};
use super::expressions::ExpressionParser;
use super::helpers::parse_leading_docs;
use super::helpers::span_from_to;
use super::types::TypeRefParser;

/// Clone the span from a token.
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

/// Convert a failed/diagnostic result from one `ParseResult<T>` into a
/// `ParseResult<U>` with an extra diagnostic message.
/// Convert a failed `ParseResult<T>` into a failed `ParseResult<U>` with an
/// extra diagnostic.
fn promote_error<T, U>(
    from: ParseResult<T>,
    extra: Diagnostic,
) -> ParseResult<U> {
    let mut diags = from.diagnostics;
    diags.push(extra);
    ParseResult {
        value: None,
        diagnostics: diags,
    }
}

/// Parses: `identifier = expression`
#[derive(Debug, Default)]
pub struct AssignmentParser;

impl Parser<Assignment> for AssignmentParser {
    /// Parse an assignment: `ident = expr`.
    ///
    /// Spans cover from the identifier to the end of the expression.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::parser::components::members::AssignmentParser;
    /// # use prisma_rs::core::parser::traits::Parser;
    /// # use prisma_rs::core::parser::stream::VectorTokenStream;
    /// # use prisma_rs::core::parser::config::ParserOptions;
    /// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
    /// let mut s = VectorTokenStream::new(vec![
    ///     Token::new(TokenType::Identifier("provider".into()), (1, 1), (1, 8)),
    ///     Token::new(TokenType::Assign, (1, 10), (1, 10)),
    ///     Token::new(
    ///         TokenType::Literal("\"postgresql\"".into()),
    ///         (1, 12),
    ///         (1, 23),
    ///     ),
    /// ]);
    /// let mut p = AssignmentParser::default();
    /// let a = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
    /// assert_eq!(a.key.text, "provider");
    /// ```
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &crate::core::parser::config::ParserOptions,
    ) -> ParseResult<Assignment> {
        // Parse leading documentation comments
        let docs = parse_leading_docs(stream);

        // key: ident
        let Some(key_tok) = stream.next() else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected identifier for assignment key",
            ));
        };
        let Some(key_ident) = ident_from_token(&key_tok) else {
            return ParseResult::error(expected_diag(
                Some(&key_tok),
                "expected identifier for assignment key",
            ));
        };

        // '='
        let Some(assign_tok) = stream.match_token(TokenType::Assign) else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected '=' in assignment",
            ));
        };

        // value: expr
        let mut expr_parser = ExpressionParser::default();
        let mut expr_res = expr_parser.parse(stream, options);
        let Some(value) = expr_res.value.take() else {
            let mut out = ParseResult::error(expected_diag(
                stream.peek(),
                "expected expression after '='",
            ));
            out.diagnostics.append(&mut expr_res.diagnostics);
            return out;
        };

        let span = span_from_to(key_ident.span(), value.span());
        let mut result = ParseResult::success(Assignment {
            key: key_ident,
            value,
            docs,
            span,
        });
        // keep diagnostics from expression parsing
        result.diagnostics.append(&mut expr_res.diagnostics);
        let _ = assign_tok; // silence unused var
        result
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        if let (Some(cur), Some(next)) =
            (stream.peek_non_comment(), stream.peek_ahead_non_comment(1))
        {
            matches!(cur.r#type(), TokenType::Identifier(_))
                && matches!(next.r#type(), TokenType::Assign)
        } else {
            false
        }
    }

    fn sync_tokens(&self) -> &[TokenType] {
        const SYNC: &[TokenType] = &[TokenType::RightBrace, TokenType::Comma];
        SYNC
    }
}

/// Parses: `ident field_attribute*` for enum values.
#[derive(Debug, Default)]
pub struct EnumValueParser;

impl Parser<EnumValue> for EnumValueParser {
    /// Parse an enum value: `ident field_attribute*`.
    ///
    /// Attributes are optional. The span covers the identifier and any
    /// following attributes.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::parser::components::members::EnumValueParser;
    /// # use prisma_rs::core::parser::traits::Parser;
    /// # use prisma_rs::core::parser::stream::VectorTokenStream;
    /// # use prisma_rs::core::parser::config::ParserOptions;
    /// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
    /// let mut s = VectorTokenStream::new(vec![Token::new(
    ///     TokenType::Identifier("Active".into()),
    ///     (1, 1),
    ///     (1, 6),
    /// )]);
    /// let mut p = EnumValueParser::default();
    /// let v = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
    /// assert_eq!(v.name.text, "Active");
    /// ```
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &crate::core::parser::config::ParserOptions,
    ) -> ParseResult<EnumValue> {
        // Parse leading documentation comments
        let docs = parse_leading_docs(stream);

        // name: ident
        let Some(name_tok) = stream.next() else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected identifier for enum value",
            ));
        };
        let Some(name_ident) = ident_from_token(&name_tok) else {
            return ParseResult::error(expected_diag(
                Some(&name_tok),
                "expected identifier for enum value",
            ));
        };

        // attrs: field_attribute*
        let mut attrs: Vec<FieldAttribute> = Vec::new();
        let mut diags = Vec::new();
        let mut last_span = name_ident.span().clone();

        while stream.check(TokenType::At) {
            let mut p = FieldAttributeParser::default();
            let mut r = p.parse(stream, options);
            diags.append(&mut r.diagnostics);
            if let Some(attr) = r.value.take() {
                last_span = attr.span().clone();
                attrs.push(attr);
            } else {
                // Failed to parse an attribute; break to avoid infinite loop.
                break;
            }
        }

        let span = span_from_to(name_ident.span(), &last_span);
        let mut res = ParseResult::success(EnumValue {
            name: name_ident,
            attrs,
            docs,
            span,
        });
        res.diagnostics.append(&mut diags);
        res
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        stream
            .peek_non_comment()
            .is_some_and(|t| matches!(t.r#type(), TokenType::Identifier(_)))
    }

    fn sync_tokens(&self) -> &[TokenType] {
        const SYNC: &[TokenType] = &[
            TokenType::RightBrace,
            TokenType::Comma,
            TokenType::At,
            TokenType::DoubleAt,
        ];
        SYNC
    }
}

/// Try to parse a scalar type keyword and an optional list marker `[]`.
/// If a scalar is present, returns `Ok(Some(TypeRef))`.
/// If no scalar is present at the cursor, returns `Ok(None)` without consuming anything.
/// Never returns an error; fallback parsers (e.g. `TypeRefParser`) handle that case.
fn try_parse_scalar_typeref(stream: &mut dyn TokenStream) -> Option<TypeRef> {
    use TokenType::{
        Boolean, Bytes, DateTime, Decimal, Float, Int, Json, List,
    };

    // Check the current token for a scalar keyword
    let scalar_tok = match stream.peek().map(Token::r#type) {
        Some(
            TokenType::String
            | Int
            | Float
            | Boolean
            | DateTime
            | Json
            | Bytes
            | Decimal,
        ) => {
            // Safe to consume
            stream.next()
        }
        _ => return None,
    }?;

    // Map token kind -> canonical variant name (e.g., "Int", "String")
    let name_text = scalar_tok.r#type().name().to_string();

    // Build NamedType with a single-part QualifiedIdent
    let id = Ident {
        text: name_text,
        span: tspan(&scalar_tok),
    };
    let q = QualifiedIdent {
        parts: vec![id],
        span: tspan(&scalar_tok),
    };
    let named = NamedType {
        name: q,
        span: tspan(&scalar_tok),
    };
    let mut ty = TypeRef::Named(named);

    // Optional list `[]` directly after the base type
    if let Some(list_tok) = stream.match_token(List) {
        let base_span = ty.span().clone();
        ty = TypeRef::List(ListType {
            inner: Box::new(ty),
            span: span_from_to(&base_span, &tspan(&list_tok)),
        });
    }

    Some(ty)
}

/// Parses: `ident type_ref opt_marker? field_attribute*`
#[derive(Debug, Default)]
pub struct FieldDeclParser;

impl Parser<FieldDecl> for FieldDeclParser {
    /// Parse a field declaration: `ident type_ref opt_marker? field_attribute*`.
    ///
    /// The span covers the field name through the last attribute or marker.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::parser::components::members::FieldDeclParser;
    /// # use prisma_rs::core::parser::traits::Parser;
    /// # use prisma_rs::core::parser::stream::VectorTokenStream;
    /// # use prisma_rs::core::parser::config::ParserOptions;
    /// # use prisma_rs::core::parser::ast::TypeRef;
    /// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
    /// let mut s = VectorTokenStream::new(vec![
    ///     Token::new(TokenType::Identifier("id".into()), (1, 1), (1, 2)),
    ///     Token::new(TokenType::String, (1, 4), (1, 9)),
    /// ]);
    /// let mut p = FieldDeclParser::default();
    /// let f = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
    /// assert_eq!(f.name.text, "id");
    /// if let TypeRef::Named(n) = f.r#type {
    ///     assert_eq!(n.name.parts[0].text, "String");
    /// } else {
    ///     panic!("expected named");
    /// }
    /// ```
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &crate::core::parser::config::ParserOptions,
    ) -> ParseResult<FieldDecl> {
        // Parse leading documentation comments
        let docs = parse_leading_docs(stream);

        // Field name
        let Some(name_tok) = stream.next() else {
            return ParseResult::error(expected_diag(
                stream.peek(),
                "expected field name",
            ));
        };
        let Some(name_ident) = ident_from_token(&name_tok) else {
            return ParseResult::error(expected_diag(
                Some(&name_tok),
                "expected field name",
            ));
        };

        // Field type
        // First, try scalar keywords (String, Int, ...). If none, fall back to TypeRefParser.
        let (ty, mut diags) = if let Some(t) = try_parse_scalar_typeref(stream)
        {
            (t, Vec::new())
        } else {
            let mut type_parser = TypeRefParser::default();
            let mut type_res = type_parser.parse(stream, options);
            let Some(t) = type_res.value.take() else {
                let mut out = ParseResult::error(expected_diag(
                    stream.peek(),
                    "expected field type",
                ));
                out.diagnostics.append(&mut type_res.diagnostics);
                return out;
            };
            (t, type_res.diagnostics)
        };

        let mut last_span = ty.span().clone();

        // Optional '?'
        let mut optional = false;
        if let Some(tok) = stream.match_token(TokenType::Optional) {
            optional = true;
            last_span = tspan(&tok);
        }

        // Attributes: `@...` repeating
        let mut attrs: Vec<FieldAttribute> = Vec::new();

        while stream.check(TokenType::At) {
            let mut p = FieldAttributeParser::default();
            let mut r = p.parse(stream, options);
            diags.append(&mut r.diagnostics);
            if let Some(attr) = r.value.take() {
                last_span = attr.span().clone();
                attrs.push(attr);
            } else {
                break;
            }
        }

        let span = span_from_to(name_ident.span(), &last_span);
        let mut res = ParseResult::success(FieldDecl {
            name: name_ident,
            r#type: ty,
            optional,
            modifiers: Vec::new(),
            attrs,
            docs,
            span,
        });
        res.diagnostics.append(&mut diags);
        res
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        stream
            .peek_non_comment()
            .is_some_and(|t| matches!(t.r#type(), TokenType::Identifier(_)))
    }

    fn sync_tokens(&self) -> &[TokenType] {
        const SYNC: &[TokenType] = &[
            TokenType::RightBrace,
            TokenType::At,
            TokenType::DoubleAt,
            TokenType::Comma,
        ];
        SYNC
    }
}

/// Parses: `model_member := field_decl | block_attribute`
#[derive(Debug, Default)]
pub struct ModelMemberParser;

impl Parser<ModelMember> for ModelMemberParser {
    /// Parse a model member: `field_decl | block_attribute`.
    ///
    /// The span and structure reflect the chosen alternative.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::parser::components::members::ModelMemberParser;
    /// # use prisma_rs::core::parser::traits::Parser;
    /// # use prisma_rs::core::parser::stream::VectorTokenStream;
    /// # use prisma_rs::core::parser::config::ParserOptions;
    /// # use prisma_rs::core::parser::ast::ModelMember;
    /// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
    /// let mut s = VectorTokenStream::new(vec![
    ///     Token::new(TokenType::Identifier("name".into()), (1,1), (1,4)),
    ///     Token::new(TokenType::String, (1,6), (1,11)),
    /// ]);
    /// let mut p = ModelMemberParser::default();
    /// let m = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
    /// assert!(matches!(m, ModelMember::Field(_)));
    /// ```
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &crate::core::parser::config::ParserOptions,
    ) -> ParseResult<ModelMember> {
        if stream.check(TokenType::DoubleAt) {
            let mut p = BlockAttributeParser::default();
            let mut r = p.parse(stream, options);
            if let Some(attr) = r.value.take() {
                let mut out =
                    ParseResult::success(ModelMember::BlockAttribute(attr));
                out.diagnostics.append(&mut r.diagnostics);
                return out;
            }
            return promote_error::<BlockAttribute, ModelMember>(
                r,
                expected_diag(stream.peek(), "invalid block attribute"),
            );
        }

        // Otherwise, expect a field declaration
        let mut p = FieldDeclParser;
        let mut r = p.parse(stream, options);
        if let Some(field) = r.value.take() {
            let mut out = ParseResult::success(ModelMember::Field(field));
            out.diagnostics.append(&mut r.diagnostics);
            return out;
        }
        promote_error::<FieldDecl, ModelMember>(
            r,
            expected_diag(stream.peek(), "expected field or block attribute"),
        )
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        if let Some(t) = stream.peek_non_comment() {
            matches!(t.r#type(), TokenType::Identifier(_) | TokenType::DoubleAt)
        } else {
            false
        }
    }

    fn sync_tokens(&self) -> &[TokenType] {
        const SYNC: &[TokenType] = &[
            TokenType::RightBrace,
            TokenType::DoubleAt,
            TokenType::Identifier(String::new()),
        ];
        SYNC
    }
}

/// Parses: `enum_member := enum_value | block_attribute`
#[derive(Debug, Default)]
pub struct EnumMemberParser;

impl Parser<EnumMember> for EnumMemberParser {
    /// Parse an enum member: `enum_value | block_attribute`.
    ///
    /// The span and structure reflect the chosen alternative.
    ///
    /// ## Examples
    /// ```
    /// # use prisma_rs::core::parser::components::members::EnumMemberParser;
    /// # use prisma_rs::core::parser::traits::Parser;
    /// # use prisma_rs::core::parser::stream::VectorTokenStream;
    /// # use prisma_rs::core::parser::config::ParserOptions;
    /// # use prisma_rs::core::parser::ast::EnumMember;
    /// # use prisma_rs::core::scanner::tokens::{Token, TokenType};
    /// let mut s = VectorTokenStream::new(vec![Token::new(
    ///     TokenType::Identifier("A".into()),
    ///     (1, 1),
    ///     (1, 1),
    /// )]);
    /// let mut p = EnumMemberParser::default();
    /// let m = p.parse(&mut s, &ParserOptions::default()).value.unwrap();
    /// assert!(matches!(m, EnumMember::Value(_)));
    /// ```
    fn parse(
        &mut self,
        stream: &mut dyn TokenStream,
        options: &crate::core::parser::config::ParserOptions,
    ) -> ParseResult<EnumMember> {
        if stream.check(TokenType::DoubleAt) {
            let mut p = BlockAttributeParser::default();
            let mut r = p.parse(stream, options);
            if let Some(attr) = r.value.take() {
                let mut out =
                    ParseResult::success(EnumMember::BlockAttribute(attr));
                out.diagnostics.append(&mut r.diagnostics);
                return out;
            }
            return promote_error::<BlockAttribute, EnumMember>(
                r,
                expected_diag(stream.peek(), "invalid block attribute"),
            );
        }

        let mut p = EnumValueParser;
        let mut r = p.parse(stream, options);
        if let Some(val) = r.value.take() {
            let mut out = ParseResult::success(EnumMember::Value(val));
            out.diagnostics.append(&mut r.diagnostics);
            return out;
        }
        promote_error::<EnumValue, EnumMember>(
            r,
            expected_diag(
                stream.peek(),
                "expected enum value or block attribute",
            ),
        )
    }

    fn can_parse(&self, stream: &dyn TokenStream) -> bool {
        if let Some(t) = stream.peek_non_comment() {
            matches!(t.r#type(), TokenType::Identifier(_) | TokenType::DoubleAt)
        } else {
            false
        }
    }

    fn sync_tokens(&self) -> &[TokenType] {
        const SYNC: &[TokenType] = &[
            TokenType::RightBrace,
            TokenType::DoubleAt,
            TokenType::Identifier(String::new()),
        ];
        SYNC
    }
}

#[cfg(test)]
mod tests {
    #![expect(clippy::expect_used, clippy::unwrap_used)]

    use crate::core::parser::ast::{
        EnumMember, Expr, HasNodeType, ModelMember, NamedType, TypeRef,
    };
    use crate::core::parser::components::members::{
        AssignmentParser, EnumMemberParser, EnumValueParser, FieldDeclParser,
        ModelMemberParser,
    };
    use crate::core::parser::stream::TokenStreamExt;
    use crate::core::parser::traits::{Parser, TokenStream};
    use crate::core::scanner::tokens::{Token, TokenType};

    fn tok(t: TokenType, start: (u32, u32), end: (u32, u32)) -> Token {
        Token::new(t, start, end)
    }

    struct V(Vec<Token>, usize);
    impl TokenStream for V {
        fn peek(&self) -> Option<&Token> {
            self.0.get(self.1)
        }
        fn peek_ahead(&self, o: usize) -> Option<&Token> {
            self.0.get(self.1 + o)
        }
        fn next(&mut self) -> Option<Token> {
            if self.1 < self.0.len() {
                let t = self.0[self.1].clone();
                self.1 += 1;
                Some(t)
            } else {
                None
            }
        }
        fn is_at_end(&self) -> bool {
            self.1 >= self.0.len()
        }
        fn position(&self) -> usize {
            self.1
        }
        fn checkpoint(&self) -> usize {
            self.1
        }
        fn restore(&mut self, c: usize) {
            self.1 = c.min(self.0.len());
        }
    }

    #[test]
    fn parses_simple_enum_value_without_attrs() {
        let mut s = V(
            vec![tok(TokenType::Identifier("ADMIN".into()), (1, 1), (1, 6))],
            0,
        );
        let mut p = EnumValueParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.is_success());
        let v = res.value.expect("expected EnumValue in successful result");
        assert_eq!(v.name.text, "ADMIN");
    }

    #[test]
    fn model_member_can_parse_field_or_block_attr() {
        let s1 = V(
            vec![tok(TokenType::Identifier("id".into()), (1, 1), (1, 3))],
            0,
        );
        let p = ModelMemberParser;
        assert!(p.can_parse(&s1));

        let s2 = V(vec![tok(TokenType::DoubleAt, (1, 1), (1, 3))], 0);
        assert!(p.can_parse(&s2));
    }

    #[test]
    fn assignment_can_parse_ident_assign() {
        let s = V(
            vec![
                tok(TokenType::Identifier("provider".into()), (1, 1), (1, 9)),
                tok(TokenType::Assign, (1, 10), (1, 11)),
                tok(TokenType::Literal("\"sqlite\"".into()), (1, 12), (1, 21)),
            ],
            0,
        );
        let p = AssignmentParser;
        assert!(p.can_parse(&s));
    }

    #[test]
    fn field_decl_simple_int() {
        // id Int
        let mut s = V(
            vec![
                tok(TokenType::Identifier("id".into()), (1, 1), (1, 3)),
                tok(TokenType::Int, (1, 4), (1, 7)),
            ],
            0,
        );

        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(
            res.is_success(),
            "expected success, diagnostics: {:?}",
            res.diagnostics
        );

        let field = res.value.expect("expected FieldDecl in successful result");

        assert_eq!(field.name.text, "id");
        assert!(!field.optional);
        assert_eq!(field.attrs.len(), 0);
        // End span should be at the Int token end
        assert_eq!(field.span.end.line, 1);
        assert_eq!(field.span.end.column, 7);
    }

    #[test]
    fn field_decl_optional_with_attrs_default_autoincrement() {
        // id Int? @id @default(autoincrement())
        let mut s = V(
            vec![
                tok(TokenType::Identifier("id".into()), (1, 1), (1, 3)),
                tok(TokenType::Int, (1, 4), (1, 7)),
                tok(TokenType::Optional, (1, 7), (1, 8)),
                tok(TokenType::At, (1, 9), (1, 10)),
                tok(TokenType::Identifier("id".into()), (1, 10), (1, 12)),
                tok(TokenType::At, (1, 13), (1, 14)),
                tok(TokenType::Identifier("default".into()), (1, 14), (1, 21)),
                tok(TokenType::LeftParen, (1, 21), (1, 22)),
                tok(
                    TokenType::Identifier("autoincrement".into()),
                    (1, 22),
                    (1, 36),
                ),
                tok(TokenType::LeftParen, (1, 36), (1, 37)),
                tok(TokenType::RightParen, (1, 37), (1, 38)),
                tok(TokenType::RightParen, (1, 38), (1, 39)),
            ],
            0,
        );

        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(
            res.is_success(),
            "expected success, diagnostics: {:?}",
            res.diagnostics
        );

        let field = res.value.expect("expected FieldDecl");

        assert_eq!(field.name.text, "id");
        assert!(field.optional);
        assert_eq!(field.attrs.len(), 2);

        // Check attribute names
        let a0 = &field.attrs[0];
        assert!(a0.name.is_simple());
        assert_eq!(a0.name.as_simple().unwrap().text, "id"); // unwrap on &Ident (not Option), safe: we checked is_simple()
        let a1 = &field.attrs[1];
        assert!(a1.name.is_simple());
        assert_eq!(a1.name.as_simple().unwrap().text, "default");

        // Span should end after last RightParen
        assert_eq!(field.span.end.column, 39);
    }

    #[test]
    fn field_decl_list_string() {
        // tags String[]
        let mut s = V(
            vec![
                tok(TokenType::Identifier("tags".into()), (1, 1), (1, 5)),
                tok(TokenType::String, (1, 6), (1, 12)),
                tok(TokenType::List, (1, 12), (1, 14)),
            ],
            0,
        );

        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(
            res.is_success(),
            "expected success, diagnostics: {:?}",
            res.diagnostics
        );

        let field = res.value.expect("expected FieldDecl");

        assert_eq!(field.name.text, "tags");
        assert!(!field.optional);
        // End span should be at the list marker end
        assert_eq!(field.span.end.column, 14);
    }

    #[test]
    fn model_member_block_attribute_map() {
        // @@map("user")
        let mut s = V(
            vec![
                tok(TokenType::DoubleAt, (1, 1), (1, 3)),
                tok(TokenType::Identifier("map".into()), (1, 3), (1, 6)),
                tok(TokenType::LeftParen, (1, 6), (1, 7)),
                tok(TokenType::Literal("\"user\"".into()), (1, 7), (1, 13)),
                tok(TokenType::RightParen, (1, 13), (1, 14)),
            ],
            0,
        );

        let mut p = ModelMemberParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(
            res.is_success(),
            "expected success, diagnostics: {:?}",
            res.diagnostics
        );

        let mm = res.value.expect("expected ModelMember");

        match mm {
            ModelMember::BlockAttribute(attr) => {
                assert!(attr.name.is_simple());
                assert_eq!(attr.name.as_simple().unwrap().text, "map");
                assert!(attr.args.is_some());
            }
            ModelMember::Field(_) => panic!("expected BlockAttribute"),
        }
    }

    #[test]
    fn enum_member_value_with_attr_map() {
        // ADMIN @map("admin")
        let mut s = V(
            vec![
                tok(TokenType::Identifier("ADMIN".into()), (1, 1), (1, 6)),
                tok(TokenType::At, (1, 7), (1, 8)),
                tok(TokenType::Identifier("map".into()), (1, 8), (1, 11)),
                tok(TokenType::LeftParen, (1, 11), (1, 12)),
                tok(TokenType::Literal("\"admin\"".into()), (1, 12), (1, 19)),
                tok(TokenType::RightParen, (1, 19), (1, 20)),
            ],
            0,
        );

        let mut p = EnumMemberParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(
            res.is_success(),
            "expected success, diagnostics: {:?}",
            res.diagnostics
        );

        let em = res.value.expect("expected EnumMember");

        match em {
            EnumMember::Value(v) => {
                assert_eq!(v.name.text, "ADMIN");
                assert_eq!(v.attrs.len(), 1);
                assert_eq!(v.attrs[0].name.as_simple().unwrap().text, "map");
            }
            EnumMember::BlockAttribute(_) => {
                panic!("expected EnumMember::Value")
            }
        }
    }

    #[test]
    fn assignment_parse_full_literal_string() {
        // provider = "sqlite"
        let mut s = V(
            vec![
                tok(TokenType::Identifier("provider".into()), (1, 1), (1, 9)),
                tok(TokenType::Assign, (1, 10), (1, 11)),
                tok(TokenType::Literal("\"sqlite\"".into()), (1, 12), (1, 21)),
            ],
            0,
        );

        let mut p = AssignmentParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(
            res.is_success(),
            "expected success, diagnostics: {:?}",
            res.diagnostics
        );

        let asn = res.value.expect("expected Assignment");

        assert_eq!(asn.key.text, "provider");
        // Basic shape check on expression kind
        match asn.value {
            Expr::StringLit(_)
            | Expr::IdentRef(_)
            | Expr::FuncCall(_)
            | Expr::IntLit(_) => {}
            other => panic!("unexpected expr variant: {:?}", other.node_type()),
        }
    }

    #[test]
    fn model_member_can_parse_is_false_for_single_at() {
        // A stray field attribute line cannot start a model member
        let s = V(vec![tok(TokenType::At, (1, 1), (1, 2))], 0);
        let p = ModelMemberParser;
        assert!(!p.can_parse(&s));
    }

    #[test]
    fn field_decl_span_covers_optional_and_attrs() {
        // createdAt DateTime? @default(now())
        let mut s = V(
            vec![
                tok(TokenType::Identifier("createdAt".into()), (1, 1), (1, 10)),
                tok(TokenType::DateTime, (1, 11), (1, 19)),
                tok(TokenType::Optional, (1, 19), (1, 20)),
                tok(TokenType::At, (1, 21), (1, 22)),
                tok(TokenType::Identifier("default".into()), (1, 22), (1, 29)),
                tok(TokenType::LeftParen, (1, 29), (1, 30)),
                tok(TokenType::Identifier("now".into()), (1, 30), (1, 33)),
                tok(TokenType::LeftParen, (1, 33), (1, 34)),
                tok(TokenType::RightParen, (1, 34), (1, 35)),
                tok(TokenType::RightParen, (1, 35), (1, 36)),
            ],
            0,
        );

        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(
            res.is_success(),
            "expected success, diagnostics: {:?}",
            res.diagnostics
        );
        let field = res.value.expect("value must be present on success");
        assert!(field.optional);
        assert_eq!(field.attrs.len(), 1);
        assert_eq!(field.span.start.column, 1);
        assert_eq!(field.span.end.column, 36);
    }

    #[test]
    fn field_decl_with_qualified_type_user() {
        // post User
        let mut s = V(
            vec![
                tok(TokenType::Identifier("post".into()), (1, 1), (1, 5)),
                tok(TokenType::Identifier("User".into()), (1, 6), (1, 10)),
            ],
            0,
        );

        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(
            res.is_success(),
            "expected success, diagnostics: {:?}",
            res.diagnostics
        );
        let field = res.value.expect("value must be present");
        assert_eq!(field.name.text, "post");
        // TypeRef is Named(NamedType { name: QualifiedIdent { parts: [Ident("User")] } })
        match field.r#type {
            TypeRef::Named(NamedType { ref name, .. }) => {
                assert!(name.is_simple());
                assert_eq!(name.as_simple().unwrap().text, "User");
            }
            TypeRef::List(_) => panic!("expected Named type"),
        }
    }

    #[test]
    fn block_attribute_unique_array_argument() {
        // @@unique([name, email])
        let mut s = V(
            vec![
                tok(TokenType::DoubleAt, (1, 1), (1, 3)),
                tok(TokenType::Identifier("unique".into()), (1, 3), (1, 9)),
                tok(TokenType::LeftParen, (1, 9), (1, 10)),
                tok(TokenType::LeftBracket, (1, 10), (1, 11)),
                tok(TokenType::Identifier("name".into()), (1, 11), (1, 15)),
                tok(TokenType::Comma, (1, 15), (1, 16)),
                tok(TokenType::Identifier("email".into()), (1, 17), (1, 22)),
                tok(TokenType::RightBracket, (1, 22), (1, 23)),
                tok(TokenType::RightParen, (1, 23), (1, 24)),
            ],
            0,
        );

        let mut p = ModelMemberParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(
            res.is_success(),
            "expected success, diagnostics: {:?}",
            res.diagnostics
        );
        let mm = res.value.expect("value must be present");
        match mm {
            ModelMember::BlockAttribute(attr) => {
                assert_eq!(attr.name.as_simple().unwrap().text, "unique");
                assert!(attr.args.is_some());
            }
            ModelMember::Field(_) => panic!("expected BlockAttribute"),
        }
    }

    #[test]
    fn field_attribute_with_qualified_ident_db_varchar() {
        // title String @db.VarChar(255)
        let mut s = V(
            vec![
                tok(TokenType::Identifier("title".into()), (1, 1), (1, 6)),
                tok(TokenType::String, (1, 7), (1, 13)),
                tok(TokenType::At, (1, 14), (1, 15)),
                tok(TokenType::Identifier("db".into()), (1, 15), (1, 17)),
                tok(TokenType::Dot, (1, 17), (1, 18)),
                tok(TokenType::Identifier("VarChar".into()), (1, 18), (1, 25)),
                tok(TokenType::LeftParen, (1, 25), (1, 26)),
                tok(TokenType::Literal("255".into()), (1, 26), (1, 29)),
                tok(TokenType::RightParen, (1, 29), (1, 30)),
            ],
            0,
        );

        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(
            res.is_success(),
            "expected success, diagnostics: {:?}",
            res.diagnostics
        );

        let field = res.value.expect("value must be present");
        assert_eq!(field.attrs.len(), 1);
        let a = &field.attrs[0];
        assert!(!a.name.is_simple());
        assert_eq!(a.name.parts.len(), 2);
        assert_eq!(a.name.parts[0].text, "db");
        assert_eq!(a.name.parts[1].text, "VarChar");
        assert!(a.args.is_some());
    }

    #[test]
    fn field_decl_missing_type_is_error() {
        // id @id   (type is missing)
        let mut s = V(
            vec![
                tok(TokenType::Identifier("id".into()), (1, 1), (1, 3)),
                tok(TokenType::At, (1, 4), (1, 5)),
                tok(TokenType::Identifier("id".into()), (1, 5), (1, 7)),
            ],
            0,
        );

        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(!res.is_success(), "parse should fail");
        assert!(!res.diagnostics.is_empty(), "should emit diagnostics");
    }

    #[test]
    fn field_decl_scalar_then_invalid_attr_breaks_with_diagnostic() {
        // id Int @          <-- invalid attribute after '@'
        let mut s = V(
            vec![
                tok(TokenType::Identifier("id".into()), (1, 1), (1, 3)),
                tok(TokenType::Int, (1, 4), (1, 7)),
                tok(TokenType::At, (1, 8), (1, 9)),
            ],
            0,
        );

        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );

        // Even with an attribute error, the parser should still return a FieldDecl value.
        assert!(res.value.is_some(), "field should still be produced");
        assert!(res.has_errors(), "should record attribute parse error(s)");

        let field = res.value.expect("expected FieldDecl value");
        assert_eq!(field.name.text, "id");
        assert_eq!(field.attrs.len(), 0, "no valid attrs parsed");

        // Span should end at the type (since attr failed and we didn’t extend span)
        assert_eq!(field.span.end.column, 7);
    }

    #[test]
    fn enum_value_attr_parse_failure_breaks_and_keeps_span_at_name() {
        // ADMIN @           <-- invalid attr after '@'
        let mut s = V(
            vec![
                tok(TokenType::Identifier("ADMIN".into()), (1, 1), (1, 6)),
                tok(TokenType::At, (1, 7), (1, 8)),
            ],
            0,
        );

        let mut p = EnumValueParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );

        // We still get a value, but with error diagnostics from the bad attribute.
        assert!(res.value.is_some(), "enum value should still be produced");
        assert!(res.has_errors(), "should capture attribute parse error(s)");

        let v = res.value.expect("expected EnumValue");
        assert_eq!(v.attrs.len(), 0);
        // Span should end at the name because attr failed
        assert_eq!(v.span.start.column, 1);
        assert_eq!(v.span.end.column, 6);
    }

    #[test]
    fn model_member_invalid_block_attribute_errors() {
        // @@               <-- incomplete block attribute
        let mut s = V(vec![tok(TokenType::DoubleAt, (1, 1), (1, 3))], 0);

        let mut p = ModelMemberParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );

        assert!(!res.is_success(), "should fail");
        assert!(
            res.diagnostics
                .iter()
                .any(|d| d.message.contains("invalid block attribute")),
            "diagnostics should mention invalid block attribute: {:?}",
            res.diagnostics
        );
    }

    #[test]
    fn enum_member_invalid_block_attribute_errors() {
        // @@               <-- incomplete block attribute inside enum
        let mut s = V(vec![tok(TokenType::DoubleAt, (1, 1), (1, 3))], 0);

        let mut p = EnumMemberParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );

        assert!(!res.is_success(), "should fail");
        assert!(
            res.diagnostics
                .iter()
                .any(|d| d.message.contains("invalid block attribute"))
        );
    }

    #[test]
    fn model_member_field_parse_error_promoted() {
        // id @id            <-- missing type (field parse fails)
        let mut s = V(
            vec![
                tok(TokenType::Identifier("id".into()), (1, 1), (1, 3)),
                tok(TokenType::At, (1, 4), (1, 5)),
                tok(TokenType::Identifier("id".into()), (1, 5), (1, 7)),
            ],
            0,
        );

        let mut p = ModelMemberParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );

        assert!(!res.is_success(), "should fail");
        assert!(
            res.diagnostics.iter().any(|d| d
                .message
                .contains("expected field or block attribute"))
        );
    }

    #[test]
    fn assignment_missing_equals_parse_error() {
        // provider "sqlite" <-- missing '='
        let mut s = V(
            vec![
                tok(TokenType::Identifier("provider".into()), (1, 1), (1, 9)),
                tok(TokenType::Literal("\"sqlite\"".into()), (1, 10), (1, 19)),
            ],
            0,
        );

        let mut p = AssignmentParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(!res.is_success(), "should error");
        assert!(
            res.diagnostics
                .iter()
                .any(|d| d.message.contains("expected '=' in assignment"))
        );
    }

    #[test]
    fn assignment_missing_value_parse_error() {
        // provider =        <-- missing value
        let mut s = V(
            vec![
                tok(TokenType::Identifier("provider".into()), (1, 1), (1, 9)),
                tok(TokenType::Assign, (1, 10), (1, 11)),
            ],
            0,
        );

        let mut p = AssignmentParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(!res.is_success(), "should error");
        assert!(
            res.diagnostics
                .iter()
                .any(|d| d.message.contains("expected expression after '='"))
        );
    }

    #[test]
    fn assignment_identref_value_success() {
        // mode = development
        let mut s = V(
            vec![
                tok(TokenType::Identifier("mode".into()), (1, 1), (1, 5)),
                tok(TokenType::Assign, (1, 6), (1, 7)),
                tok(
                    TokenType::Identifier("development".into()),
                    (1, 8),
                    (1, 19),
                ),
            ],
            0,
        );

        let mut p = AssignmentParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.is_success(), "expected success: {:?}", res.diagnostics);

        let asn = res.value.expect("expected Assignment");
        match asn.value {
            Expr::IdentRef(_) => {}
            other => panic!("expected IdentRef, got {:?}", other.node_type()),
        }
    }

    #[test]
    fn assignment_func_call_value_success() {
        // url = env("DATABASE_URL")
        let mut s = V(
            vec![
                tok(TokenType::Identifier("url".into()), (1, 1), (1, 4)),
                tok(TokenType::Assign, (1, 5), (1, 6)),
                tok(TokenType::Identifier("env".into()), (1, 7), (1, 10)),
                tok(TokenType::LeftParen, (1, 10), (1, 11)),
                tok(
                    TokenType::Literal("\"DATABASE_URL\"".into()),
                    (1, 11),
                    (1, 26),
                ),
                tok(TokenType::RightParen, (1, 26), (1, 27)),
            ],
            0,
        );

        let mut p = AssignmentParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.is_success(), "expected success: {:?}", res.diagnostics);

        let asn = res.value.expect("expected Assignment");
        match asn.value {
            Expr::FuncCall(_) => {}
            other => panic!("expected FuncCall, got {:?}", other.node_type()),
        }
    }

    #[test]
    fn enum_value_multiple_attrs() {
        // ADMIN @map("admin") @deprecated()
        let mut s = V(
            vec![
                tok(TokenType::Identifier("ADMIN".into()), (1, 1), (1, 6)),
                tok(TokenType::At, (1, 7), (1, 8)),
                tok(TokenType::Identifier("map".into()), (1, 8), (1, 11)),
                tok(TokenType::LeftParen, (1, 11), (1, 12)),
                tok(TokenType::Literal("\"admin\"".into()), (1, 12), (1, 19)),
                tok(TokenType::RightParen, (1, 19), (1, 20)),
                tok(TokenType::At, (1, 21), (1, 22)),
                tok(
                    TokenType::Identifier("deprecated".into()),
                    (1, 22),
                    (1, 32),
                ),
                tok(TokenType::LeftParen, (1, 32), (1, 33)),
                tok(TokenType::RightParen, (1, 33), (1, 34)),
            ],
            0,
        );

        let mut p = EnumValueParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.is_success(), "expected success: {:?}", res.diagnostics);
        let v = res.value.expect("expected EnumValue");
        assert_eq!(v.attrs.len(), 2);
    }

    #[test]
    fn model_member_block_attribute_qualified_ident() {
        // @@db.Index()
        let mut s = V(
            vec![
                tok(TokenType::DoubleAt, (1, 1), (1, 3)),
                tok(TokenType::Identifier("db".into()), (1, 3), (1, 5)),
                tok(TokenType::Dot, (1, 5), (1, 6)),
                tok(TokenType::Identifier("Index".into()), (1, 6), (1, 11)),
                tok(TokenType::LeftParen, (1, 11), (1, 12)),
                tok(TokenType::RightParen, (1, 12), (1, 13)),
            ],
            0,
        );

        let mut p = ModelMemberParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.is_success(), "expected success: {:?}", res.diagnostics);
        match res.value.expect("value must be present") {
            ModelMember::BlockAttribute(attr) => {
                assert_eq!(attr.name.parts.len(), 2);
                assert_eq!(attr.name.parts[0].text, "db");
                assert_eq!(attr.name.parts[1].text, "Index");
            }
            ModelMember::Field(_) => panic!("expected BlockAttribute"),
        }
    }

    #[test]
    fn field_decl_list_scalar_optional() {
        // tags String[]?
        let mut s = V(
            vec![
                tok(TokenType::Identifier("tags".into()), (1, 1), (1, 5)),
                tok(TokenType::String, (1, 6), (1, 12)),
                tok(TokenType::List, (1, 12), (1, 14)),
                tok(TokenType::Optional, (1, 14), (1, 15)),
            ],
            0,
        );

        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.is_success(), "expected success: {:?}", res.diagnostics);
        let f = res.value.expect("expected FieldDecl");
        assert!(f.optional);
        match f.r#type {
            TypeRef::List(_) => {}
            TypeRef::Named(_) => panic!("expected list type"),
        }
        assert_eq!(f.span.end.column, 15);
    }

    #[test]
    fn enum_member_can_parse_is_false_for_single_at() {
        let s = V(vec![tok(TokenType::At, (1, 1), (1, 2))], 0);
        let p = EnumMemberParser;
        assert!(!p.can_parse(&s));
    }

    #[test]
    fn assignment_can_parse_false_without_equal() {
        let s = V(
            vec![
                tok(TokenType::Identifier("provider".into()), (1, 1), (1, 9)),
                tok(TokenType::Identifier("sqlite".into()), (1, 10), (1, 16)),
            ],
            0,
        );
        let p = AssignmentParser;
        assert!(!p.can_parse(&s));
    }

    #[test]
    fn assignment_empty_stream_emits_error_with_zero_span() {
        // empty input -> expected_diag(None) path (span 0:0..0:0)
        let mut s = V(vec![], 0);
        let mut p = AssignmentParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.value.is_none());
        assert!(res.has_errors());
        let d = &res.diagnostics[0];
        assert!(d.message.contains("expected identifier for assignment key"));
        assert_eq!(d.span.start.line, 0);
        assert_eq!(d.span.start.column, 0);
        assert_eq!(d.span.end.line, 0);
        assert_eq!(d.span.end.column, 0);
    }

    #[test]
    fn enum_value_rejects_non_identifier_start_token() {
        // starts with a type keyword, not an identifier
        let mut s = V(vec![tok(TokenType::Int, (1, 1), (1, 4))], 0);
        let mut p = EnumValueParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.value.is_none());
        assert!(res.has_errors());
        assert!(
            res.diagnostics.iter().any(|d| d
                .message
                .contains("expected identifier for enum value"))
        );
    }

    #[test]
    fn model_member_can_parse_false_on_empty_stream() {
        let s = V(vec![], 0);
        let p = ModelMemberParser;
        assert!(!p.can_parse(&s));
    }

    #[test]
    fn field_decl_can_parse_false_when_starts_with_scalar() {
        // starts with `Int` (no field name), so FieldDeclParser::can_parse must be false
        let s = V(vec![tok(TokenType::Int, (1, 1), (1, 4))], 0);
        let p = FieldDeclParser;
        assert!(!p.can_parse(&s));
    }

    #[test]
    fn field_decl_other_scalar_kinds_boolean_float_json_bytes_decimal() {
        // Flags Boolean
        let mut s1 = V(
            vec![
                tok(TokenType::Identifier("flags".into()), (1, 1), (1, 6)),
                tok(TokenType::Boolean, (1, 7), (1, 14)),
            ],
            0,
        );
        let mut p = FieldDeclParser;
        let r1 = p.parse(
            &mut s1,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(r1.is_success(), "{:?}", r1.diagnostics);
        let f1 = r1.value.expect("FieldDecl");
        match f1.r#type {
            TypeRef::Named(NamedType { name, .. }) => {
                assert!(name.as_simple().unwrap().text.contains("Boolean"));
            }
            TypeRef::List(_) => panic!("expected Named(Boolean)"),
        }

        // price Float
        let mut s2 = V(
            vec![
                tok(TokenType::Identifier("price".into()), (1, 1), (1, 6)),
                tok(TokenType::Float, (1, 7), (1, 12)),
            ],
            0,
        );
        let r2 = p.parse(
            &mut s2,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(r2.is_success(), "{:?}", r2.diagnostics);
        match r2.value.expect("FieldDecl").r#type {
            TypeRef::Named(NamedType { name, .. }) => {
                assert!(name.as_simple().unwrap().text.contains("Float"));
            }
            TypeRef::List(_) => panic!("expected Named(Float)"),
        }

        // meta Json
        let mut s3 = V(
            vec![
                tok(TokenType::Identifier("meta".into()), (1, 1), (1, 5)),
                tok(TokenType::Json, (1, 6), (1, 10)),
            ],
            0,
        );
        let r3 = p.parse(
            &mut s3,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(r3.is_success(), "{:?}", r3.diagnostics);
        match r3.value.expect("FieldDecl").r#type {
            TypeRef::Named(NamedType { name, .. }) => {
                assert!(name.as_simple().unwrap().text.contains("Json"));
            }
            TypeRef::List(_) => panic!("expected Named(Json)"),
        }

        // blob Bytes
        let mut s4 = V(
            vec![
                tok(TokenType::Identifier("blob".into()), (1, 1), (1, 5)),
                tok(TokenType::Bytes, (1, 6), (1, 11)),
            ],
            0,
        );
        let r4 = p.parse(
            &mut s4,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(r4.is_success(), "{:?}", r4.diagnostics);
        match r4.value.expect("FieldDecl").r#type {
            TypeRef::Named(NamedType { name, .. }) => {
                assert!(name.as_simple().unwrap().text.contains("Bytes"));
            }
            TypeRef::List(_) => panic!("expected Named(Bytes)"),
        }

        // amount Decimal
        let mut s5 = V(
            vec![
                tok(TokenType::Identifier("amount".into()), (1, 1), (1, 7)),
                tok(TokenType::Decimal, (1, 8), (1, 15)),
            ],
            0,
        );
        let r5 = p.parse(
            &mut s5,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(r5.is_success(), "{:?}", r5.diagnostics);
        match r5.value.expect("FieldDecl").r#type {
            TypeRef::Named(NamedType { name, .. }) => {
                assert!(name.as_simple().unwrap().text.contains("Decimal"));
            }
            TypeRef::List(_) => panic!("expected Named(D9ecimal)"),
        }
    }

    #[test]
    fn field_decl_bytes_list_variant() {
        // payload Bytes[]
        let mut s = V(
            vec![
                tok(TokenType::Identifier("payload".into()), (1, 1), (1, 8)),
                tok(TokenType::Bytes, (1, 9), (1, 14)),
                tok(TokenType::List, (1, 14), (1, 16)),
            ],
            0,
        );
        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.is_success(), "{:?}", res.diagnostics);
        match res.value.expect("FieldDecl").r#type {
            TypeRef::List(_) => {}
            TypeRef::Named(_) => panic!("expected list Bytes[]"),
        }
    }

    #[test]
    fn field_decl_valid_attr_then_invalid_attr_keeps_first_and_errors() {
        // id Int @id @
        let mut s = V(
            vec![
                tok(TokenType::Identifier("id".into()), (1, 1), (1, 3)),
                tok(TokenType::Int, (1, 4), (1, 7)),
                tok(TokenType::At, (1, 8), (1, 9)),
                tok(TokenType::Identifier("id".into()), (1, 9), (1, 11)),
                tok(TokenType::At, (1, 12), (1, 13)), // invalid second attribute start
            ],
            0,
        );
        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.value.is_some(), "{:?}", res.diagnostics);
        assert!(res.has_errors(), "should record error for second attr");
        let f = res.value.expect("FieldDecl");
        assert_eq!(f.attrs.len(), 1, "only first attr should be kept");
        assert_eq!(f.attrs[0].name.as_simple().unwrap().text, "id");
    }

    #[test]
    fn enum_value_valid_attr_then_invalid_attr_keeps_first_and_errors() {
        // ADMIN @map("x") @
        let mut s = V(
            vec![
                tok(TokenType::Identifier("ADMIN".into()), (1, 1), (1, 6)),
                tok(TokenType::At, (1, 7), (1, 8)),
                tok(TokenType::Identifier("map".into()), (1, 8), (1, 11)),
                tok(TokenType::LeftParen, (1, 11), (1, 12)),
                tok(TokenType::Literal("\"x\"".into()), (1, 12), (1, 15)),
                tok(TokenType::RightParen, (1, 15), (1, 16)),
                tok(TokenType::At, (1, 17), (1, 18)), // invalid second attribute start
            ],
            0,
        );
        let mut p = EnumValueParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.value.is_some());
        assert!(res.has_errors());
        let v = res.value.expect("EnumValue");
        assert_eq!(v.attrs.len(), 1);
        assert_eq!(v.attrs[0].name.as_simple().unwrap().text, "map");
    }

    #[test]
    fn enum_member_promotes_error_when_value_invalid() {
        // single '@' is not a block attribute (requires @@) and not a value -> forces EnumValue error path + promotion
        let mut s = V(vec![tok(TokenType::At, (1, 1), (1, 2))], 0);
        let mut p = EnumMemberParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.value.is_none());
        assert!(res.has_errors());
        assert!(res.diagnostics.iter().any(|d| {
            d.message.contains("expected enum value or block attribute")
        }));
    }

    #[test]
    fn enum_value_can_parse_false_when_not_identifier() {
        let s = V(vec![tok(TokenType::DoubleAt, (1, 1), (1, 3))], 0);
        let p = EnumValueParser;
        assert!(!p.can_parse(&s));
    }

    #[test]
    fn assignment_can_parse_false_when_first_not_identifier() {
        // Int = 1   -> first token is not Identifier
        let s = V(
            vec![
                tok(TokenType::Int, (1, 1), (1, 4)),
                tok(TokenType::Assign, (1, 5), (1, 6)),
                tok(TokenType::Literal("1".into()), (1, 7), (1, 8)),
            ],
            0,
        );
        let p = AssignmentParser;
        assert!(!p.can_parse(&s));
    }

    #[test]
    fn assignment_can_parse_false_when_empty_input() {
        let s = V(vec![], 0);
        let p = AssignmentParser;
        assert!(!p.can_parse(&s));
    }

    #[test]
    fn assignment_can_parse_with_comments() {
        let s = V(
            vec![
                tok(
                    TokenType::Comment("// comment".to_string()),
                    (1, 1),
                    (1, 10),
                ),
                tok(
                    TokenType::DocComment("/// doc comment".to_string()),
                    (2, 1),
                    (2, 15),
                ),
                tok(TokenType::Identifier("provider".into()), (3, 1), (3, 9)),
                tok(TokenType::Assign, (3, 10), (3, 11)),
                tok(TokenType::Literal("\"sqlite\"".into()), (3, 12), (3, 21)),
            ],
            0,
        );
        let p = AssignmentParser;
        assert!(p.can_parse(&s));
    }

    #[test]
    fn enum_value_can_parse_with_comments() {
        let s = V(
            vec![
                tok(
                    TokenType::Comment("// comment".to_string()),
                    (1, 1),
                    (1, 10),
                ),
                tok(
                    TokenType::DocComment("/// doc comment".to_string()),
                    (2, 1),
                    (2, 15),
                ),
                tok(TokenType::Identifier("ADMIN".into()), (3, 1), (3, 6)),
            ],
            0,
        );
        let p = EnumValueParser;
        assert!(p.can_parse(&s));
    }

    #[test]
    fn field_decl_can_parse_with_comments() {
        let s = V(
            vec![
                tok(
                    TokenType::Comment("// comment".to_string()),
                    (1, 1),
                    (1, 10),
                ),
                tok(
                    TokenType::DocComment("/// doc comment".to_string()),
                    (2, 1),
                    (2, 15),
                ),
                tok(TokenType::Identifier("id".into()), (3, 1), (3, 3)),
                tok(TokenType::Int, (3, 4), (3, 7)),
            ],
            0,
        );
        let p = FieldDeclParser;
        assert!(p.can_parse(&s));
    }

    #[test]
    fn model_member_can_parse_with_comments() {
        let s_id = V(
            vec![
                tok(
                    TokenType::Comment("// comment".to_string()),
                    (1, 1),
                    (1, 10),
                ),
                tok(
                    TokenType::DocComment("/// doc comment".to_string()),
                    (2, 1),
                    (2, 15),
                ),
                tok(TokenType::Identifier("id".into()), (3, 1), (3, 3)),
            ],
            0,
        );
        let p = ModelMemberParser;
        assert!(p.can_parse(&s_id));

        let s_da = V(
            vec![
                tok(
                    TokenType::Comment("// comment".to_string()),
                    (1, 1),
                    (1, 10),
                ),
                tok(
                    TokenType::DocComment("/// doc comment".to_string()),
                    (2, 1),
                    (2, 15),
                ),
                tok(TokenType::DoubleAt, (3, 1), (3, 3)),
            ],
            0,
        );
        assert!(p.can_parse(&s_da));
    }

    #[test]
    fn enum_member_can_parse_with_comments() {
        let s_id = V(
            vec![
                tok(
                    TokenType::Comment("// comment".to_string()),
                    (1, 1),
                    (1, 10),
                ),
                tok(
                    TokenType::DocComment("/// doc comment".to_string()),
                    (2, 1),
                    (2, 15),
                ),
                tok(TokenType::Identifier("A".into()), (3, 1), (3, 2)),
            ],
            0,
        );
        let p = EnumMemberParser;
        assert!(p.can_parse(&s_id));

        let s_da = V(
            vec![
                tok(
                    TokenType::Comment("// comment".to_string()),
                    (1, 1),
                    (1, 10),
                ),
                tok(
                    TokenType::DocComment("/// doc comment".to_string()),
                    (2, 1),
                    (2, 15),
                ),
                tok(TokenType::DoubleAt, (3, 1), (3, 3)),
            ],
            0,
        );
        assert!(p.can_parse(&s_da));
    }

    #[test]
    fn enum_value_can_parse_false_when_empty() {
        let s = V(vec![], 0);
        let p = EnumValueParser;
        assert!(!p.can_parse(&s));
    }

    #[test]
    fn field_decl_can_parse_false_when_double_at() {
        let s = V(vec![tok(TokenType::DoubleAt, (1, 1), (1, 3))], 0);
        let p = FieldDeclParser;
        assert!(!p.can_parse(&s));
    }

    #[test]
    fn enum_member_can_parse_true_for_identifier_and_double_at() {
        let s_id = V(
            vec![tok(TokenType::Identifier("A".into()), (1, 1), (1, 2))],
            0,
        );
        let s_da = V(vec![tok(TokenType::DoubleAt, (1, 1), (1, 3))], 0);
        let p = EnumMemberParser;
        assert!(p.can_parse(&s_id));
        assert!(p.can_parse(&s_da));
    }

    // ---------- explicit "expected ..." error paths ----------

    #[test]
    fn field_decl_expected_field_name_when_non_identifier_starts() {
        // starts with Int -> not a valid field name
        let mut s = V(vec![tok(TokenType::Int, (2, 4), (2, 7))], 0);
        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.value.is_none());
        assert!(res.has_errors());
        let d = &res.diagnostics[0];
        assert!(d.message.contains("expected field name"));
        // span should be the offending token (not zero)
        assert_eq!(d.span.start.line, 2);
        assert_eq!(d.span.start.column, 4);
        assert_eq!(d.span.end.line, 2);
        assert_eq!(d.span.end.column, 7);
    }

    #[test]
    fn field_decl_expected_field_name_when_stream_empty() {
        let mut s = V(vec![], 0);
        let mut p = FieldDeclParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.value.is_none());
        assert!(res.has_errors());
        let d = &res.diagnostics[0];
        assert!(d.message.contains("expected field name"));
        // zero span path via expected_diag(None)
        assert_eq!(d.span.start.line, 0);
        assert_eq!(d.span.start.column, 0);
        assert_eq!(d.span.end.line, 0);
        assert_eq!(d.span.end.column, 0);
    }

    #[test]
    fn assignment_expected_identifier_for_key_when_non_identifier_starts() {
        // Int = "x"  -> key must be Identifier
        let mut s = V(
            vec![
                tok(TokenType::Int, (3, 1), (3, 4)),
                tok(TokenType::Assign, (3, 5), (3, 6)),
                tok(TokenType::Literal("\"x\"".into()), (3, 7), (3, 10)),
            ],
            0,
        );
        let mut p = AssignmentParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.value.is_none());
        assert!(res.has_errors());
        let d = &res.diagnostics[0];
        assert!(d.message.contains("expected identifier for assignment key"));
        // span points at the bad first token (Int)
        assert_eq!(d.span.start.line, 3);
        assert_eq!(d.span.start.column, 1);
        assert_eq!(d.span.end.line, 3);
        assert_eq!(d.span.end.column, 4);
    }

    #[test]
    fn enum_value_expected_identifier_when_stream_empty() {
        let mut s = V(vec![], 0);
        let mut p = EnumValueParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.value.is_none());
        assert!(res.has_errors());
        let d = &res.diagnostics[0];
        assert!(d.message.contains("expected identifier for enum value"));
        assert_eq!(d.span.start.line, 0);
        assert_eq!(d.span.start.column, 0);
        assert_eq!(d.span.end.line, 0);
        assert_eq!(d.span.end.column, 0);
    }

    #[test]
    fn model_member_promotes_field_error_on_at_instead_of_name() {
        // starts with single '@' -> not a field name and not a block attr; field parse fails,
        // ModelMemberParser promotes with its own message.
        let mut s = V(vec![tok(TokenType::At, (1, 9), (1, 10))], 0);
        let mut p = ModelMemberParser;
        let res = p.parse(
            &mut s,
            &crate::core::parser::config::ParserOptions::default(),
        );
        assert!(res.value.is_none());
        assert!(res.has_errors());
        // Should include the promotion message
        assert!(
            res.diagnostics.iter().any(|d| d
                .message
                .contains("expected field or block attribute"))
        );
        // And very likely the inner field error too
        assert!(
            res.diagnostics
                .iter()
                .any(|d| d.message.contains("expected field name"))
        );
    }

    // ---------- sync_tokens() recovery behavior ----------

    #[test]
    fn sync_tokens_assignment_synchronizes_to_comma() {
        // junk ... ,   -> stops on COMMA
        let mut s = V(
            vec![
                tok(TokenType::Identifier("junk".into()), (1, 1), (1, 5)),
                tok(TokenType::At, (1, 6), (1, 7)),
                tok(TokenType::LeftParen, (1, 7), (1, 8)),
                tok(TokenType::RightParen, (1, 8), (1, 9)),
                tok(TokenType::Comma, (1, 10), (1, 11)),
                tok(TokenType::Identifier("next".into()), (1, 12), (1, 16)),
            ],
            0,
        );
        let p = AssignmentParser;
        s.synchronize(p.sync_tokens());
        // Should stop before consuming the COMMA; peek is COMMA
        let cur = s.peek().expect("should not be at end");
        assert!(matches!(cur.r#type(), TokenType::Comma));
    }

    #[test]
    fn sync_tokens_fielddecl_synchronizes_to_double_at() {
        // junk ... @@
        let mut s = V(
            vec![
                tok(TokenType::Identifier("junk".into()), (1, 1), (1, 5)),
                tok(TokenType::LeftParen, (1, 6), (1, 7)),
                tok(TokenType::Literal("1".into()), (1, 7), (1, 8)),
                tok(TokenType::RightParen, (1, 8), (1, 9)),
                tok(TokenType::DoubleAt, (1, 10), (1, 12)),
            ],
            0,
        );
        let p = FieldDeclParser;
        s.synchronize(p.sync_tokens());
        let cur = s.peek().expect("should not be at end");
        assert!(matches!(cur.r#type(), TokenType::DoubleAt));
    }

    #[test]
    fn sync_tokens_enumvalue_synchronizes_to_comma() {
        // junk ... ,
        let mut s = V(
            vec![
                tok(TokenType::Identifier("junk".into()), (1, 1), (1, 5)),
                tok(TokenType::Float, (1, 6), (1, 11)),
                tok(TokenType::Comma, (1, 12), (1, 13)),
                tok(TokenType::Identifier("after".into()), (1, 14), (1, 19)),
            ],
            0,
        );
        let p = EnumValueParser;
        s.synchronize(p.sync_tokens());
        let cur = s.peek().expect("should not be at end");
        assert!(matches!(cur.r#type(), TokenType::Comma));
    }

    #[test]
    fn sync_tokens_modelmember_synchronizes_to_identifier() {
        // junk ... Identifier -> ModelMember sync includes Identifier discriminant
        let mut s = V(
            vec![
                tok(TokenType::Float, (1, 1), (1, 6)),
                tok(TokenType::Identifier("stop".into()), (1, 7), (1, 11)),
                tok(TokenType::DoubleAt, (1, 12), (1, 14)),
            ],
            0,
        );
        let p = ModelMemberParser;
        s.synchronize(p.sync_tokens());
        let cur = s.peek().expect("should not be at end");
        assert!(matches!(cur.r#type(), TokenType::Identifier(_)));
    }

    #[test]
    fn sync_tokens_enummember_synchronizes_to_double_at() {
        // junk ... @@
        let mut s = V(
            vec![
                tok(TokenType::Json, (1, 1), (1, 5)),
                tok(TokenType::DoubleAt, (1, 6), (1, 8)),
                tok(TokenType::Identifier("after".into()), (1, 9), (1, 14)),
            ],
            0,
        );
        let p = EnumMemberParser;
        s.synchronize(p.sync_tokens());
        let cur = s.peek().expect("should not be at end");
        assert!(matches!(cur.r#type(), TokenType::DoubleAt));
    }
}
