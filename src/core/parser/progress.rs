//! Progress observation utilities embedded into normal parsing.
//!
//! Provides a progress observer trait, a default observer implementation,
//! implementation, and an `ObservedTokenStream` that wraps an inner
//! `TokenStream` to report progress as tokens are consumed. The orchestrator
//! constructs an observer and wraps streams before invoking existing
//! component parsers; no parser APIs change.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::core::parser::config::ParserOptions;
use crate::core::parser::traits::TokenStream;
use crate::core::scanner::tokens::{Token, TokenType};

/// Configuration for progress supervision with defaults derived when not
/// explicitly set by external callers.
#[derive(Debug, Clone, Copy)]
pub struct ProgressTuning {
    pub max_parse_time: Duration,
    pub progress_check_interval: Duration,
    pub stall_threshold: Duration,
    pub report_interval: usize,
    pub enabled: bool,
}

impl Default for ProgressTuning {
    fn default() -> Self {
        Self {
            max_parse_time: Duration::from_millis(300),
            progress_check_interval: Duration::from_millis(25),
            stall_threshold: Duration::from_millis(100),
            report_interval: 16,
            enabled: true,
        }
    }
}

/// Extension trait to derive progress tuning from `ParserOptions` without
/// modifying its shape.
pub trait ProgressConfig {
    fn progress_tuning(&self) -> ProgressTuning;
}

impl ProgressConfig for ParserOptions {
    fn progress_tuning(&self) -> ProgressTuning {
        ProgressTuning {
            max_parse_time: self.max_parse_time,
            progress_check_interval: self.progress_check_interval,
            stall_threshold: self.stall_threshold,
            report_interval: self.report_interval,
            enabled: self.enable_progress_validation,
        }
    }
}

/// Observe token consumption and provide continuation decisions.
pub trait ProgressObserver: Send + Sync {
    fn on_advance(
        &self,
        parser_id: usize,
        position: usize,
        current: Option<&TokenType>,
    );

    fn allow_continue(&self, parser_id: usize) -> bool;
    fn max_duration(&self) -> Duration;

    /// Returns true if the parser has reported progress within `min_interval`.
    fn recently_active(&self, parser_id: usize, min_interval: Duration)
    -> bool;
}

#[derive(Debug, Clone)]
struct ParserProgress {
    last_position: usize,
    last_update: Instant,
    total_advances: usize,
}

impl ParserProgress {
    fn new() -> Self {
        Self {
            last_position: 0,
            last_update: Instant::now(),
            total_advances: 0,
        }
    }
}

/// Thread-safe default supervisor using a shared map.
#[derive(Debug, Clone)]
pub struct DefaultProgressObserver {
    progress: Arc<Mutex<HashMap<usize, ParserProgress>>>,
    tuning: ProgressTuning,
}

impl DefaultProgressObserver {
    #[must_use]
    pub fn new(tuning: ProgressTuning) -> Self {
        Self {
            progress: Arc::new(Mutex::new(HashMap::new())),
            tuning,
        }
    }
}

impl ProgressObserver for DefaultProgressObserver {
    fn on_advance(
        &self,
        parser_id: usize,
        position: usize,
        _current: Option<&TokenType>,
    ) {
        if !self.tuning.enabled {
            return;
        }
        if let Ok(mut m) = self.progress.lock() {
            let e = m.entry(parser_id).or_insert_with(ParserProgress::new);
            e.last_position = position;
            e.last_update = Instant::now();
            e.total_advances = e.total_advances.saturating_add(1);
        }
    }

    fn allow_continue(&self, parser_id: usize) -> bool {
        if !self.tuning.enabled {
            return true;
        }
        if let Ok(m) = self.progress.lock()
            && let Some(e) = m.get(&parser_id)
        {
            e.last_update.elapsed() < self.tuning.max_parse_time
        } else {
            true
        }
    }

    fn max_duration(&self) -> Duration {
        self.tuning.max_parse_time
    }

    fn recently_active(
        &self,
        parser_id: usize,
        min_interval: Duration,
    ) -> bool {
        if let Ok(m) = self.progress.lock()
            && let Some(e) = m.get(&parser_id)
        {
            e.last_update.elapsed() < min_interval && e.total_advances > 0
        } else {
            false
        }
    }
}

/// Token stream wrapper that reports progress periodically.
pub struct ObservedTokenStream<'a> {
    inner: &'a mut dyn TokenStream,
    supervisor: &'a dyn ProgressObserver,
    parser_id: usize,
    last_reported_position: usize,
    report_interval: usize,
    cutoff: bool,
    eof_emitted: bool,
}

impl<'a> ObservedTokenStream<'a> {
    #[must_use]
    pub fn new(
        inner: &'a mut dyn TokenStream,
        supervisor: &'a dyn ProgressObserver,
        parser_id: usize,
        report_interval: usize,
    ) -> Self {
        let pos = inner.position();
        Self {
            inner,
            supervisor,
            parser_id,
            last_reported_position: pos,
            report_interval: report_interval.max(1),
            cutoff: false,
            eof_emitted: false,
        }
    }
}

impl TokenStream for ObservedTokenStream<'_> {
    fn peek(&self) -> Option<&Token> {
        if self.cutoff {
            return None;
        }
        self.inner.peek()
    }

    fn peek_ahead(&self, offset: usize) -> Option<&Token> {
        if self.cutoff {
            return None;
        }
        self.inner.peek_ahead(offset)
    }

    fn next(&mut self) -> Option<Token> {
        if self.cutoff {
            if self.eof_emitted {
                return None;
            }
            self.eof_emitted = true;
            return Some(Token::new(TokenType::EOF, (1, 1), (1, 1)));
        }

        if !self.supervisor.allow_continue(self.parser_id) {
            self.cutoff = true;
            self.eof_emitted = true;
            return Some(Token::new(TokenType::EOF, (1, 1), (1, 1)));
        }

        let tok = self.inner.next();
        let pos = self.inner.position();
        if pos >= self.last_reported_position + self.report_interval {
            self.supervisor.on_advance(
                self.parser_id,
                pos,
                tok.as_ref().map(Token::r#type),
            );
            self.last_reported_position = pos;
        }
        tok
    }

    fn is_at_end(&self) -> bool {
        self.cutoff || self.inner.is_at_end()
    }

    fn position(&self) -> usize {
        self.inner.position()
    }

    fn checkpoint(&self) -> usize {
        self.inner.checkpoint()
    }

    fn restore(&mut self, checkpoint: usize) {
        self.inner.restore(checkpoint);
    }
}

#[cfg(test)]
mod tests {
    #![expect(clippy::expect_used)]
    use super::*;
    use crate::core::parser::stream::VectorTokenStream;

    #[test]
    fn supervisor_detects_progress() {
        let sup = DefaultProgressObserver::new(ProgressTuning::default());
        let mut stream = VectorTokenStream::new(vec![
            Token::new(TokenType::Model, (1, 1), (1, 5)),
            Token::new(TokenType::Identifier("X".into()), (1, 7), (1, 7)),
            Token::new(TokenType::LeftBrace, (1, 8), (1, 8)),
            Token::new(TokenType::RightBrace, (1, 9), (1, 9)),
            Token::new(TokenType::EOF, (1, 10), (1, 10)),
        ]);
        let mut pt = ObservedTokenStream::new(&mut stream, &sup, 1, 1);
        // Before any advances, progress is false
        assert!(!sup.recently_active(1, Duration::from_secs(1)));
        // Consume a few tokens to trigger reporting
        let _ = pt.next();
        let _ = pt.next();
        assert!(sup.recently_active(1, Duration::from_secs(1)));
    }

    struct CountingSupervisor {
        count: std::sync::Mutex<usize>,
        cont: std::sync::Mutex<bool>,
        tuning: ProgressTuning,
    }

    impl CountingSupervisor {
        fn new(tuning: ProgressTuning) -> Self {
            Self {
                count: std::sync::Mutex::new(0),
                cont: std::sync::Mutex::new(true),
                tuning,
            }
        }
        fn set_continue(&self, v: bool) {
            if let Ok(mut g) = self.cont.lock() {
                *g = v;
            }
        }
        fn get_count(&self) -> usize {
            self.count.lock().ok().map_or(0, |value| *value)
        }
    }

    impl ProgressObserver for CountingSupervisor {
        fn on_advance(
            &self,
            _parser_id: usize,
            _position: usize,
            _tok: Option<&TokenType>,
        ) {
            if let Ok(mut g) = self.count.lock() {
                *g = g.saturating_add(1);
            }
        }
        fn allow_continue(&self, _parser_id: usize) -> bool {
            self.cont.lock().map(|g| *g).unwrap_or(true)
        }
        fn max_duration(&self) -> Duration {
            self.tuning.max_parse_time
        }
        fn recently_active(&self, _parser_id: usize, _min: Duration) -> bool {
            self.get_count() > 0
        }
    }

    #[test]
    fn report_interval_is_respected() {
        let mut stream = VectorTokenStream::new(vec![
            Token::new(TokenType::Model, (1, 1), (1, 5)),
            Token::new(TokenType::Identifier("A".into()), (1, 7), (1, 7)),
            Token::new(TokenType::LeftBrace, (1, 8), (1, 8)),
            Token::new(TokenType::RightBrace, (1, 9), (1, 9)),
            Token::new(TokenType::EOF, (1, 10), (1, 10)),
        ]);
        let sup = CountingSupervisor::new(ProgressTuning::default());
        let mut pt = ObservedTokenStream::new(&mut stream, &sup, 0, 3);
        let _ = pt.next(); // 1
        assert_eq!(sup.get_count(), 0, "should not report before interval");
        let _ = pt.next(); // 2
        assert_eq!(sup.get_count(), 0, "still below interval");
        let _ = pt.next(); // 3
        assert!(sup.get_count() >= 1, "should report on reaching interval");
    }

    #[test]
    fn allow_continue_synthesizes_eof() {
        let mut stream = VectorTokenStream::new(vec![
            Token::new(TokenType::Model, (1, 1), (1, 5)),
            Token::new(TokenType::Identifier("A".into()), (1, 7), (1, 7)),
        ]);
        let sup = CountingSupervisor::new(ProgressTuning::default());
        let mut pt = ObservedTokenStream::new(&mut stream, &sup, 0, 1);
        let t1 = pt.next().expect("expected first token to be present");
        assert!(matches!(t1.r#type(), TokenType::Model));
        // Flip continuation to false; next should return synthesized EOF
        sup.set_continue(false);
        let t2 = pt.next().expect("expected synthesized EOF token");
        assert!(matches!(t2.r#type(), TokenType::EOF));
    }

    #[test]
    fn test_cutoff_prevents_infinite_loop() {
        let tokens = vec![
            Token::new(
                TokenType::Identifier("model".to_owned()),
                (1, 1),
                (1, 5),
            ),
            Token::new(TokenType::Identifier("Foo".to_owned()), (1, 6), (1, 9)),
            Token::new(TokenType::LeftBrace, (1, 10), (1, 11)), // "{"
        ];

        let mut stream = VectorTokenStream::new(tokens);
        let observer = DefaultProgressObserver::new(ProgressTuning {
            max_parse_time: Duration::from_millis(1), // Very short timeout
            ..Default::default()
        });

        let mut observed_stream =
            ObservedTokenStream::new(&mut stream, &observer, 0, 1);

        // Simulate parser loop - this should NOT infinite loop
        let mut iterations = 0;
        while !observed_stream.is_at_end() && iterations < 1000 {
            let _token = observed_stream.next();
            iterations += 1;
            // Simulate some processing time to trigger timeout
            std::thread::sleep(Duration::from_millis(2));
        }

        // Should exit loop due to timeout, not hit iteration limit
        assert!(
            iterations < 1000,
            "Parser should have been cut off, not looped infinitely"
        );
        assert!(
            observed_stream.is_at_end(),
            "Stream should report as at end after cutoff"
        );
    }
}
