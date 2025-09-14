//! Performance and Benchmarking Tests
//!
//! Tests that validate parsing performance characteristics and use
//! the `PerformanceMetrics` utilities for detailed pipeline analysis.

use crate::scanner_parser::benchmark_parsing_pipeline;
use std::fs;

fn load_fixture(path: &str) -> String {
    fs::read_to_string(format!("tests/fixtures/schemas/{path}"))
        .unwrap_or_else(|_| panic!("Failed to load fixture: {path}"))
}

#[test]
#[ignore = "benchmark test - run with: cargo test -- --include-ignored"]
fn benchmark_empty_schema() {
    let input = "";
    let metrics = benchmark_parsing_pipeline(input);

    // Empty schema should be very fast
    assert!(
        metrics.total_time.as_micros() < 10_000,
        "Empty schema should parse in under 10ms"
    );
    assert!(
        metrics.scan_time.as_micros() < 5_000,
        "Scanning empty should be very fast"
    );
    assert!(
        metrics.parse_time.as_micros() < 5_000,
        "Parsing empty should be very fast"
    );

    // Should have minimal tokens and nodes
    assert!(metrics.token_count >= 1, "Should have at least EOF token");
    assert!(
        metrics.token_count <= 5,
        "Empty schema should have minimal tokens"
    );
    assert_eq!(
        metrics.ast_node_count, 1,
        "Empty schema should have just the root Schema node"
    );

    println!("Empty schema metrics: {metrics:?}");
}

#[test]
#[ignore = "benchmark test - run with: cargo test -- --include-ignored"]
fn benchmark_simple_model() {
    let input = r"
model User {
  id String @id
  name String
  email String @unique
}
";
    let metrics = benchmark_parsing_pipeline(input);

    // Simple model should parse reasonably fast
    assert!(
        metrics.total_time.as_millis() < 50,
        "Simple model should parse in under 50ms"
    );

    // Should have reasonable token/node counts
    assert!(
        metrics.token_count >= 15,
        "Simple model should have reasonable token count"
    );
    assert!(
        metrics.token_count <= 30,
        "Simple model token count should be bounded"
    );
    assert!(
        metrics.ast_node_count >= 5,
        "Should have Schema + Model + Fields"
    );

    // Scan time should be reasonable compared to parse time
    // Note: timing can vary based on system performance, so we use a generous multiplier
    assert!(
        metrics.scan_time <= metrics.parse_time * 10,
        "Scan time should be reasonable vs parse time"
    );

    println!("Simple model metrics: {metrics:?}");
}

#[test]
#[ignore = "benchmark test - run with: cargo test -- --include-ignored"]
fn benchmark_comprehensive_schema() {
    let schema_content = load_fixture("comprehensive/blog_schema.prisma");
    let metrics = benchmark_parsing_pipeline(&schema_content);

    // Complex schema should still parse in reasonable time
    assert!(
        metrics.total_time.as_millis() < 500,
        "Complex schema should parse in under 500ms"
    );

    // Should have significant token and node counts
    assert!(
        metrics.token_count >= 100,
        "Complex schema should have many tokens"
    );
    assert!(
        metrics.ast_node_count >= 20,
        "Complex schema should have many AST nodes"
    );

    // Memory usage should be reasonable
    assert!(
        metrics.memory_usage < 1_000_000,
        "Memory usage should be under 1MB for complex schema"
    );

    println!("Complex schema metrics: {metrics:?}");
    println!(
        "Tokens: {}, AST nodes: {}, Memory: {} bytes",
        metrics.token_count, metrics.ast_node_count, metrics.memory_usage
    );
}

#[test]
#[ignore = "benchmark test - run with: cargo test -- --include-ignored"]
fn performance_scaling() {
    let test_cases = [
        ("", "empty"),
        ("model User { id String }", "tiny"),
        (&load_fixture("minimal/single_model.prisma"), "minimal"),
        (&load_fixture("comprehensive/blog_schema.prisma"), "complex"),
    ];

    let mut prev_total_time = std::time::Duration::from_nanos(0);

    for (input, case_name) in test_cases {
        let metrics = benchmark_parsing_pipeline(input);

        println!(
            "{}: total={}μs, scan={}μs, parse={}μs, tokens={}, nodes={}",
            case_name,
            metrics.total_time.as_micros(),
            metrics.scan_time.as_micros(),
            metrics.parse_time.as_micros(),
            metrics.token_count,
            metrics.ast_node_count
        );

        // Each larger schema should take more time (generally)
        if !prev_total_time.is_zero() && case_name != "empty" {
            // Allow some variance, but larger schemas should generally take longer.
            // Compare using integers to avoid float precision.
            let now = metrics.total_time.as_micros();
            let prev = prev_total_time.as_micros();
            assert!(
                now < prev.saturating_mul(100),
                "Performance shouldn't degrade drastically for {case_name} (now={now}μs, prev={prev}μs)"
            );
        }

        prev_total_time = metrics.total_time;
    }
}

#[test]
#[ignore = "benchmark test - run with: cargo test -- --include-ignored"]
fn scan_vs_parse_time_distribution() {
    let test_cases = [
        &load_fixture("minimal/single_model.prisma"),
        &load_fixture("minimal/single_enum.prisma"),
        &load_fixture("comprehensive/blog_schema.prisma"),
    ];

    for input in test_cases {
        let metrics = benchmark_parsing_pipeline(input);

        // Both scan and parse should complete
        assert!(
            metrics.scan_time.as_nanos() > 0,
            "Scan time should be measurable"
        );
        assert!(
            metrics.parse_time.as_nanos() > 0,
            "Parse time should be measurable"
        );

        // Total time should be at least scan + parse time
        assert!(
            metrics.total_time >= metrics.scan_time + metrics.parse_time,
            "Total time should include scan and parse time"
        );

        // For most schemas, parsing should take longer than scanning
        println!(
            "Schema: scan={}μs, parse={}μs",
            metrics.scan_time.as_micros(),
            metrics.parse_time.as_micros(),
        );
    }
}

#[test]
#[ignore = "benchmark test - run with: cargo test -- --include-ignored"]
fn memory_usage_scaling() {
    let test_cases = [
        ("", 0),
        ("model User { id String }", 500),
        (&load_fixture("minimal/single_model.prisma"), 1000),
        (&load_fixture("comprehensive/blog_schema.prisma"), 10000),
    ];

    for (input, expected_min_bytes) in test_cases {
        let metrics = benchmark_parsing_pipeline(input);

        // Memory usage should scale with schema complexity
        assert!(
            metrics.memory_usage >= expected_min_bytes,
            "Memory usage {} should be at least {} for schema size",
            metrics.memory_usage,
            expected_min_bytes
        );

        // But shouldn't be excessively large
        assert!(
            metrics.memory_usage < 1_000_000,
            "Memory usage {} shouldn't exceed 1MB",
            metrics.memory_usage
        );

        println!("Schema memory usage: {} bytes", metrics.memory_usage);
    }
}

#[test]
#[ignore = "benchmark test - run with: cargo test -- --include-ignored"]
fn performance_consistency() {
    let input = load_fixture("minimal/single_model.prisma");
    let iterations = 5;
    let mut times = Vec::new();

    // Run multiple iterations to check consistency
    for i in 0..iterations {
        let metrics = benchmark_parsing_pipeline(&input);
        times.push(metrics.total_time.as_micros());

        println!("Iteration {}: {}μs", i + 1, metrics.total_time.as_micros());

        // Each run should be reasonably fast
        assert!(
            metrics.total_time.as_millis() < 100,
            "Each iteration should complete in under 100ms"
        );
    }

    // Calculate simple dispersion: max/min around integer average
    let sum: u128 = times.iter().copied().sum();
    let n = times.len() as u128;
    let avg: u128 = if n > 0 { sum / n } else { 0 };
    let min = *times.iter().min().expect("times non-empty");
    let max = *times.iter().max().expect("times non-empty");
    let max_dev = max.saturating_sub(avg);
    let min_dev = avg.saturating_sub(min);

    println!("Average: {avg}μs, MaxDev: {max_dev}μs, MinDev: {min_dev}μs");

    // Deviation shouldn't be more than 50% of average (allowing for some variance)
    assert!(
        max_dev <= avg / 2 && min_dev <= avg / 2,
        "Performance should be relatively consistent (avg={avg}μs, max_dev={max_dev}μs, min_dev={min_dev}μs)"
    );
}
