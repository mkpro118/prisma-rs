//! Progress behavior tests for component parsers.
//!
//! Verifies that parsing via ModelParser and ExpressionParser advances a
//! progress-tracked token stream, which in turn exercises the supervision
//! code path at the component boundary.

use crate::core::parser::components::declarations::ModelParser;
use crate::core::parser::components::expressions::ExpressionParser;
use crate::core::parser::config::ParserOptions;
use crate::core::parser::progress::{
    ObservedTokenStream, ProgressObserver, ProgressTuning,
};
use crate::core::parser::stream::VectorTokenStream;
use crate::core::parser::traits::{Parser, TokenStream};
use crate::core::scanner::tokens::{Token, TokenType};
use std::time::Duration;

#[derive(Default)]
struct CountingSup {
    count: std::sync::Mutex<usize>,
}

impl CountingSup {
    fn get(&self) -> usize {
        self.count.lock().ok().copied().unwrap_or(0)
    }
}

impl ProgressObserver for CountingSup {
    fn on_advance(
        &self,
        _parser_id: usize,
        _pos: usize,
        _tok: Option<&TokenType>,
    ) {
        if let Ok(mut g) = self.count.lock() {
            *g = g.saturating_add(1);
        }
    }
    fn allow_continue(&self, _parser_id: usize) -> bool {
        true
    }
    fn max_duration(&self) -> Duration {
        ProgressTuning::default().max_parse_time
    }
    fn recently_active(&self, _parser_id: usize, _min: Duration) -> bool {
        self.get() > 0
    }
}

fn t(tt: TokenType) -> Token {
    Token::new(tt, (1, 1), (1, 1))
}

#[test]
fn model_parser_reports_progress() {
    let mut toks = vec![
        t(TokenType::Model),
        t(TokenType::Identifier("User".into())),
        t(TokenType::LeftBrace),
        t(TokenType::RightBrace),
        t(TokenType::EOF),
    ];
    let mut stream = VectorTokenStream::new(std::mem::take(&mut toks));
    let sup = CountingSup::default();
    let mut tracked = ObservedTokenStream::new(&mut stream, &sup, 0, 1);
    let mut parser = ModelParser;
    let res = parser.parse(&mut tracked, &ParserOptions::default());
    assert!(res.is_success());
    assert!(
        sup.get() > 0,
        "expected progress reports during model parse"
    );
}

#[test]
fn expression_parser_reports_progress() {
    // Parse a simple array literal
    let mut toks = vec![
        t(TokenType::LeftBracket),
        t(TokenType::Literal("1".into())),
        t(TokenType::Comma),
        t(TokenType::Literal("2".into())),
        t(TokenType::RightBracket),
        t(TokenType::EOF),
    ];
    let mut stream = VectorTokenStream::new(std::mem::take(&mut toks));
    let sup = CountingSup::default();
    let mut tracked = ObservedTokenStream::new(&mut stream, &sup, 0, 1);
    let mut parser = ExpressionParser::new();
    let res = parser.parse(&mut tracked, &ParserOptions::default());
    assert!(res.is_success());
    assert!(
        sup.get() > 0,
        "expected progress reports during expression parse"
    );
}
