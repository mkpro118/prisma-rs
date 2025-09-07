//! Main semantic analyzer orchestrator.
//!
//! The `SemanticAnalyzer` manages the execution of multiple analysis phases
//! in dependency order, handles parallelization where possible, and collects
//! results from all analyzers.

use crate::core::parser::ast::Schema;
use crate::core::semantic_analyzer::{
    AnalyzerOptions, ConcurrencyMode, ValidationMode,
    context::{AnalysisContext, AnalysisResult, RelationshipGraph},
    diagnostics::DiagnosticCollector,
    symbol_table::SymbolTable,
    traits::PhaseAnalyzer,
    type_resolver::TypeResolver,
};
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, RwLock};
use std::time::Instant;

/// Main orchestrator for semantic analysis.
///
/// The `SemanticAnalyzer` manages a collection of pluggable analyzers and
/// executes them in dependency order. It supports both sequential and parallel
/// execution modes based on analyzer capabilities and configuration.
///
/// The analyzer maintains shared state (`SymbolTable`, `TypeResolver`, `RelationshipGraph`)
/// that phases can read from and write to, enabling the pipeline architecture
/// where each phase builds upon the work of previous phases.
///
/// ## Examples
///
/// ```rust,ignore
/// use prisma_rs::core::semantic_analyzer::{SemanticAnalyzer, AnalyzerOptions};
///
/// let mut analyzer = SemanticAnalyzer::new();
/// let options = AnalyzerOptions::default();
/// let result = analyzer.analyze(&schema, &options)?;
///
/// for diagnostic in &result.diagnostics {
///     eprintln!("Error: {}", diagnostic.message);
/// }
/// ```
pub struct SemanticAnalyzer {
    /// Phase analyzers in registration order
    phase_analyzers: Vec<Box<dyn PhaseAnalyzer>>,

    /// Shared symbol table for tracking declarations and their metadata
    symbol_table: Arc<RwLock<SymbolTable>>,

    /// Shared type resolver for handling type references
    type_resolver: Arc<RwLock<TypeResolver>>,

    /// Shared relationship graph for tracking model relationships
    relationship_graph: Arc<RwLock<RelationshipGraph>>,

    /// Collector for diagnostics from all phases
    diagnostic_collector: DiagnosticCollector,

    /// Cached dependency graph for efficient execution planning
    dependency_graph: Option<DependencyGraph>,
}

impl SemanticAnalyzer {
    /// Create a new semantic analyzer with default phase analyzers.
    #[must_use]
    pub fn new() -> Self {
        Self {
            phase_analyzers: Self::create_default_analyzers(),
            symbol_table: Arc::new(RwLock::new(SymbolTable::new())),
            type_resolver: Arc::new(RwLock::new(TypeResolver::new())),
            relationship_graph: Arc::new(RwLock::new(
                RelationshipGraph::default(),
            )),
            diagnostic_collector: DiagnosticCollector::new(),
            dependency_graph: None,
        }
    }

    /// Create a new semantic analyzer with custom phase analyzers.
    #[must_use]
    pub fn with_analyzers(analyzers: Vec<Box<dyn PhaseAnalyzer>>) -> Self {
        Self {
            phase_analyzers: analyzers,
            symbol_table: Arc::new(RwLock::new(SymbolTable::new())),
            type_resolver: Arc::new(RwLock::new(TypeResolver::new())),
            relationship_graph: Arc::new(RwLock::new(
                RelationshipGraph::default(),
            )),
            diagnostic_collector: DiagnosticCollector::new(),
            dependency_graph: None,
        }
    }

    /// Add a phase analyzer to the analyzer chain.
    ///
    /// The analyzer will be incorporated into the dependency graph and
    /// executed in the appropriate order based on its dependencies.
    pub fn add_phase_analyzer(&mut self, analyzer: Box<dyn PhaseAnalyzer>) {
        self.phase_analyzers.push(analyzer);
        // Invalidate cached dependency graph
        self.dependency_graph = None;
    }

    /// Remove a phase analyzer by name.
    pub fn remove_phase_analyzer(&mut self, name: &str) -> bool {
        let initial_len = self.phase_analyzers.len();
        self.phase_analyzers
            .retain(|analyzer| analyzer.phase_name() != name);
        let removed = self.phase_analyzers.len() != initial_len;
        if removed {
            self.dependency_graph = None;
        }
        removed
    }

    /// Get the names of all registered phase analyzers.
    #[must_use]
    pub fn analyzer_names(&self) -> Vec<&str> {
        self.phase_analyzers
            .iter()
            .map(|analyzer| analyzer.phase_name())
            .collect()
    }

    /// Analyze a schema and return comprehensive results.
    ///
    /// This is the main entry point for semantic analysis. It will execute
    /// all registered analyzers in dependency order and return a complete
    /// analysis result.
    ///
    /// # Errors
    ///
    /// Returns an `AnalysisError` if:
    /// - Dependency graph construction fails
    /// - Circular dependencies are detected
    /// - Analysis times out
    /// - Invalid dependency graph structure is encountered
    pub fn analyze(
        &mut self,
        schema: &Schema,
        options: &AnalyzerOptions,
    ) -> Result<AnalysisResult, AnalysisError> {
        let start_time = Instant::now();

        // Build dependency graph if not cached
        if self.dependency_graph.is_none() {
            self.dependency_graph = Some(self.build_dependency_graph()?);
        }

        // Clear previous results
        self.diagnostic_collector.clear();
        *self.symbol_table.write().unwrap() = SymbolTable::new();
        *self.type_resolver.write().unwrap() = TypeResolver::new();
        *self.relationship_graph.write().unwrap() =
            RelationshipGraph::default();

        // Create analysis context with shared state
        let context = AnalysisContext::new(
            options,
            Arc::clone(&self.symbol_table),
            Arc::clone(&self.type_resolver),
            Arc::clone(&self.relationship_graph),
        );

        // Execute analysis phases
        let mut temp_diagnostics = DiagnosticCollector::new();
        match options.concurrency {
            ConcurrencyMode::Sequential => {
                self.analyze_sequential(
                    schema,
                    &context,
                    options,
                    &mut temp_diagnostics,
                )?;
                self.diagnostic_collector
                    .extend(temp_diagnostics.take_all());
            }
            ConcurrencyMode::Concurrent { .. } => {
                self.analyze_parallel(schema, &context, options)?;
            }
        }

        let analysis_time = start_time.elapsed();

        // Build final result
        Ok(AnalysisResult {
            symbol_table: (*self.symbol_table.read().unwrap()).clone(),
            type_resolver: (*self.type_resolver.read().unwrap()).clone(),
            diagnostics: self.diagnostic_collector.clone().take_all(),
            analysis_metadata: context.take_metadata(),
            analysis_time,
            analyzer_count: self.phase_analyzers.len(),
        })
    }

    /// Execute analyzers sequentially in dependency order.
    fn analyze_sequential(
        &self,
        schema: &Schema,
        context: &AnalysisContext,
        options: &AnalyzerOptions,
        diagnostic_collector: &mut DiagnosticCollector,
    ) -> Result<(), AnalysisError> {
        let Some(dependency_graph) = self.dependency_graph.as_ref() else {
            return Err(AnalysisError::InvalidDependencyGraph {
                message: "Dependency graph not built".to_string(),
            });
        };
        let execution_order = dependency_graph.topological_sort()?;

        for &analyzer_index in &execution_order {
            let analyzer = &self.phase_analyzers[analyzer_index];

            // Check timeout
            if context.elapsed_time() > options.phase_timeout {
                return Err(AnalysisError::Timeout {
                    phase: analyzer.phase_name().to_string(),
                    elapsed: context.elapsed_time(),
                });
            }

            // Execute the analyzer
            let phase_result = analyzer.analyze(schema, context);
            let has_fatal = phase_result.has_fatal_errors();
            diagnostic_collector.extend(phase_result.diagnostics);

            // Stop on fatal errors if configured
            if has_fatal
                && matches!(options.validation_mode, ValidationMode::Strict)
            {
                break;
            }

            // Stop if we've hit the diagnostic limit
            if diagnostic_collector.len() >= options.max_diagnostics {
                break;
            }
        }

        Ok(())
    }

    /// Execute analyzers in parallel where possible.
    fn analyze_parallel(
        &mut self,
        schema: &Schema,
        context: &AnalysisContext,
        options: &AnalyzerOptions,
    ) -> Result<(), AnalysisError> {
        let Some(dependency_graph) = self.dependency_graph.as_ref() else {
            return Err(AnalysisError::InvalidDependencyGraph {
                message: "Dependency graph not built".to_string(),
            });
        };

        // Compute execution layers where each layer can execute in parallel
        let execution_layers =
            Self::compute_execution_layers(dependency_graph)?;

        // Execute each layer in parallel
        for layer in execution_layers {
            self.execute_layer_parallel(schema, context, options, &layer)?;
        }

        Ok(())
    }

    /// Compute execution layers for parallel processing.
    fn compute_execution_layers(
        dependency_graph: &DependencyGraph,
    ) -> Result<Vec<Vec<usize>>, AnalysisError> {
        use std::collections::BTreeSet;

        let mut layers = Vec::new();
        let mut processed = HashSet::new();
        let mut in_degree: HashMap<usize, usize> = dependency_graph
            .nodes
            .keys()
            .map(|&node| {
                (
                    node,
                    dependency_graph
                        .reverse_edges
                        .get(&node)
                        .map_or(0, std::vec::Vec::len),
                )
            })
            .collect();

        while processed.len() < dependency_graph.nodes.len() {
            // Find all nodes with zero in-degree (can execute in parallel)
            let ready: BTreeSet<usize> = in_degree
                .iter()
                .filter(|&(&node, &deg)| deg == 0 && !processed.contains(&node))
                .map(|(&node, _)| node)
                .collect();

            if ready.is_empty() {
                return Err(AnalysisError::CircularDependency {
                    cycle: vec!["Unknown".to_string()], // Simplified for now
                });
            }

            let current_layer: Vec<usize> = ready.into_iter().collect();

            // Update in-degrees for next iteration
            for &node in &current_layer {
                processed.insert(node);
                if let Some(dependencies) = dependency_graph.edges.get(&node) {
                    for &dep_node in dependencies {
                        if let Some(deg) = in_degree.get_mut(&dep_node) {
                            *deg = deg.saturating_sub(1);
                        }
                    }
                }
            }

            layers.push(current_layer);
        }

        Ok(layers)
    }

    /// Execute a layer of analyzers in parallel.
    fn execute_layer_parallel(
        &mut self,
        schema: &Schema,
        context: &AnalysisContext,
        options: &AnalyzerOptions,
        layer: &[usize],
    ) -> Result<(), AnalysisError> {
        if layer.len() == 1 {
            // Single analyzer - no need for threading overhead
            let analyzer_index = layer[0];
            let analyzer = &self.phase_analyzers[analyzer_index];

            // Check timeout
            if context.elapsed_time() > options.phase_timeout {
                return Err(AnalysisError::Timeout {
                    phase: analyzer.phase_name().to_string(),
                    elapsed: context.elapsed_time(),
                });
            }

            let phase_result = analyzer.analyze(schema, context);
            let has_fatal = phase_result.has_fatal_errors();
            self.diagnostic_collector.extend(phase_result.diagnostics);

            // Stop on fatal errors if configured
            if has_fatal
                && matches!(options.validation_mode, ValidationMode::Strict)
            {
                return Ok(());
            }

            // Check diagnostic limit
            if self.diagnostic_collector.len() >= options.max_diagnostics {
                return Ok(());
            }

            return Ok(());
        }

        // Multiple analyzers - check if any support parallel execution
        let parallel_analyzers: Vec<_> = layer
            .iter()
            .filter(|&&index| {
                self.phase_analyzers[index].supports_parallel_execution()
            })
            .copied()
            .collect();

        let (max_threads, threshold) = match options.concurrency {
            ConcurrencyMode::Sequential => (1, 0),
            ConcurrencyMode::Concurrent {
                max_threads,
                threshold,
            } => (max_threads, threshold),
        };

        if parallel_analyzers.len() > threshold && parallel_analyzers.len() > 1
        {
            // Execute parallel analyzers - for now implemented sequentially
            // TODO: Implement true parallelism using scoped threads when data ownership is resolved
            for &analyzer_index in &parallel_analyzers {
                // Check timeout
                if context.elapsed_time() > options.phase_timeout {
                    return Err(AnalysisError::Timeout {
                        phase: self.phase_analyzers[analyzer_index]
                            .phase_name()
                            .to_string(),
                        elapsed: context.elapsed_time(),
                    });
                }

                let analyzer = &self.phase_analyzers[analyzer_index];
                let phase_result = analyzer.analyze(schema, context);
                self.diagnostic_collector.extend(phase_result.diagnostics);
            }

            // Execute remaining non-parallel analyzers sequentially
            let sequential_analyzers: Vec<_> = layer
                .iter()
                .filter(|&&index| !parallel_analyzers.contains(&index))
                .copied()
                .collect();

            for &analyzer_index in &sequential_analyzers {
                let analyzer = &self.phase_analyzers[analyzer_index];
                let phase_result = analyzer.analyze(schema, context);
                self.diagnostic_collector.extend(phase_result.diagnostics);
            }
        } else {
            // No parallel analyzers or only one - fall back to sequential
            for &analyzer_index in layer {
                let analyzer = &self.phase_analyzers[analyzer_index];

                // Check timeout
                if context.elapsed_time() > options.phase_timeout {
                    return Err(AnalysisError::Timeout {
                        phase: analyzer.phase_name().to_string(),
                        elapsed: context.elapsed_time(),
                    });
                }

                let phase_result = analyzer.analyze(schema, context);
                let has_fatal = phase_result.has_fatal_errors();
                self.diagnostic_collector.extend(phase_result.diagnostics);

                // Stop on fatal errors if configured
                if has_fatal
                    && matches!(options.validation_mode, ValidationMode::Strict)
                {
                    return Ok(());
                }

                // Check diagnostic limit
                if self.diagnostic_collector.len() >= options.max_diagnostics {
                    return Ok(());
                }
            }
        }

        Ok(())
    }

    /// Build the dependency graph for all registered analyzers.
    ///
    /// # Errors
    ///
    /// Returns an `AnalysisError` if:
    /// - Missing dependencies are found
    /// - Circular dependencies are detected
    /// - Invalid graph structure is encountered
    fn build_dependency_graph(&self) -> Result<DependencyGraph, AnalysisError> {
        let mut graph = DependencyGraph::new();

        // Create a mapping from analyzer name to index
        let name_to_index: HashMap<&str, usize> = self
            .phase_analyzers
            .iter()
            .enumerate()
            .map(|(i, analyzer)| (analyzer.phase_name(), i))
            .collect();

        // Add nodes for each analyzer
        for (index, analyzer) in self.phase_analyzers.iter().enumerate() {
            graph.add_node(index, analyzer.phase_name().to_string());
        }

        // Add edges for dependencies
        for (index, analyzer) in self.phase_analyzers.iter().enumerate() {
            for dep_name in analyzer.dependencies() {
                if let Some(&dep_index) = name_to_index.get(dep_name) {
                    graph.add_edge(dep_index, index)?;
                } else {
                    return Err(AnalysisError::MissingDependency {
                        analyzer: analyzer.phase_name().to_string(),
                        dependency: (*dep_name).to_string(),
                    });
                }
            }
        }

        // Check for cycles
        if graph.has_cycles() {
            let cycle = graph
                .find_cycle()
                .unwrap_or_else(|| vec!["Unknown cycle".to_string()]);
            return Err(AnalysisError::CircularDependency { cycle });
        }

        Ok(graph)
    }

    /// Create the default set of phase analyzers.
    fn create_default_analyzers() -> Vec<Box<dyn PhaseAnalyzer>> {
        use crate::core::semantic_analyzer::analyzers::{
            AttributeValidationAnalyzer, BusinessRuleAnalyzer,
            RelationshipAnalyzer, SymbolCollectionAnalyzer,
            TypeResolutionAnalyzer,
        };

        vec![
            Box::new(SymbolCollectionAnalyzer::new()),
            Box::new(TypeResolutionAnalyzer::new()),
            Box::new(RelationshipAnalyzer::new()),
            // Additional analyzers will be added as they are implemented:
            Box::new(AttributeValidationAnalyzer::new()),
            Box::new(BusinessRuleAnalyzer::new()),
        ]
    }
}

impl Default for SemanticAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

/// Dependency graph for managing analyzer execution order.
#[derive(Debug, Clone)]
struct DependencyGraph {
    nodes: HashMap<usize, String>,
    edges: HashMap<usize, Vec<usize>>,
    reverse_edges: HashMap<usize, Vec<usize>>,
}

impl DependencyGraph {
    fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            edges: HashMap::new(),
            reverse_edges: HashMap::new(),
        }
    }

    fn add_node(&mut self, id: usize, name: String) {
        self.nodes.insert(id, name);
        self.edges.entry(id).or_default();
        self.reverse_edges.entry(id).or_default();
    }

    /// Add an edge from one node to another.
    ///
    /// # Errors
    ///
    /// Returns an `AnalysisError` if either node doesn't exist in the graph.
    fn add_edge(
        &mut self,
        from: usize,
        to: usize,
    ) -> Result<(), AnalysisError> {
        if !self.nodes.contains_key(&from) || !self.nodes.contains_key(&to) {
            return Err(AnalysisError::InvalidDependencyGraph {
                message: "Edge references non-existent node".to_string(),
            });
        }

        self.edges.entry(from).or_default().push(to);
        self.reverse_edges.entry(to).or_default().push(from);
        Ok(())
    }

    /// Perform topological sort to determine execution order.
    ///
    /// # Errors
    ///
    /// Returns an `AnalysisError` if circular dependencies are detected.
    fn topological_sort(&self) -> Result<Vec<usize>, AnalysisError> {
        use std::collections::BTreeSet;

        // Compute in-degree
        let mut in_degree: HashMap<usize, usize> = self
            .nodes
            .keys()
            .map(|&node| {
                (
                    node,
                    self.reverse_edges.get(&node).map_or(0, std::vec::Vec::len),
                )
            })
            .collect();

        // Deterministic zero in-degree set (ascending by node id => registration order)
        let mut zero: BTreeSet<usize> = in_degree
            .iter()
            .filter(|&(_, &deg)| deg == 0)
            .map(|(&node, _)| node)
            .collect();

        let mut result = Vec::with_capacity(self.nodes.len());

        while let Some(&node) = zero.iter().next() {
            zero.remove(&node);
            result.push(node);

            if let Some(dependents) = self.edges.get(&node) {
                for &dependent in dependents {
                    if let Some(deg) = in_degree.get_mut(&dependent) {
                        *deg = deg.saturating_sub(1);
                        if *deg == 0 {
                            zero.insert(dependent);
                        }
                    }
                }
            }
        }

        if result.len() == self.nodes.len() {
            Ok(result)
        } else {
            Err(AnalysisError::CircularDependency {
                cycle: self.find_cycle().unwrap_or_else(|| {
                    vec!["Unknown cycle detected".to_string()]
                }),
            })
        }
    }

    fn has_cycles(&self) -> bool {
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();

        for &node in self.nodes.keys() {
            if !visited.contains(&node)
                && self.has_cycle_util(node, &mut visited, &mut rec_stack)
            {
                return true;
            }
        }
        false
    }

    fn has_cycle_util(
        &self,
        node: usize,
        visited: &mut HashSet<usize>,
        rec_stack: &mut HashSet<usize>,
    ) -> bool {
        visited.insert(node);
        rec_stack.insert(node);

        if let Some(neighbors) = self.edges.get(&node) {
            for &neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    if self.has_cycle_util(neighbor, visited, rec_stack) {
                        return true;
                    }
                } else if rec_stack.contains(&neighbor) {
                    return true;
                }
            }
        }

        rec_stack.remove(&node);
        false
    }

    fn find_cycle(&self) -> Option<Vec<String>> {
        // Return a concrete cycle path using DFS with recursion stack
        let mut visited: HashSet<usize> = HashSet::new();
        let mut stack: Vec<usize> = Vec::new();

        for &node in self.nodes.keys() {
            if !visited.contains(&node)
                && self.find_cycle_dfs(node, &mut visited, &mut stack)
            {
                // stack now contains a path ending in a back edge; extract cycle
                if let Some(&last) = stack.last()
                    && let Some(pos) = stack.iter().position(|&n| n == last)
                {
                    let cycle_nodes = &stack[pos..];
                    let mut names = Vec::with_capacity(cycle_nodes.len());
                    for &idx in cycle_nodes {
                        if let Some(name) = self.nodes.get(&idx) {
                            names.push(name.clone());
                        }
                    }
                    return Some(names);
                }
                break;
            }
        }
        None
    }

    fn find_cycle_dfs(
        &self,
        node: usize,
        visited: &mut HashSet<usize>,
        stack: &mut Vec<usize>,
    ) -> bool {
        visited.insert(node);
        stack.push(node);

        if let Some(neighbors) = self.edges.get(&node) {
            for &neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    if self.find_cycle_dfs(neighbor, visited, stack) {
                        return true;
                    }
                } else if stack.contains(&neighbor) {
                    stack.push(neighbor);
                    return true;
                }
            }
        }

        stack.pop();
        false
    }
}

/// Errors that can occur during semantic analysis.
#[derive(Debug, Clone)]
pub enum AnalysisError {
    /// A dependency is missing from the analyzer registry
    MissingDependency {
        analyzer: String,
        dependency: String,
    },

    /// Circular dependency detected in analyzer chain
    CircularDependency { cycle: Vec<String> },

    /// Analysis timed out
    Timeout {
        phase: String,
        elapsed: std::time::Duration,
    },

    /// Invalid dependency graph structure
    InvalidDependencyGraph { message: String },
}

impl std::fmt::Display for AnalysisError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AnalysisError::MissingDependency {
                analyzer,
                dependency,
            } => {
                write!(
                    f,
                    "Analyzer '{analyzer}' depends on '{dependency}' which is not registered"
                )
            }
            AnalysisError::CircularDependency { cycle } => {
                write!(
                    f,
                    "Circular dependency detected: {}",
                    cycle.join(" -> ")
                )
            }
            AnalysisError::Timeout { phase, elapsed } => {
                write!(
                    f,
                    "Analysis timed out in phase '{phase}' after {elapsed:?}"
                )
            }
            AnalysisError::InvalidDependencyGraph { message } => {
                write!(f, "Invalid dependency graph: {message}")
            }
        }
    }
}

impl std::error::Error for AnalysisError {}

#[cfg(test)]
#[expect(clippy::expect_used)]
mod tests {
    use super::*;
    use crate::core::parser::ast::Schema;
    use crate::core::semantic_analyzer::context::PhaseResult;
    use crate::core::semantic_analyzer::diagnostics::{
        DiagnosticCode, SemanticDiagnostic,
    };
    use crate::core::semantic_analyzer::traits::PhaseAnalyzer;

    // Mock analyzer for testing
    struct MockAnalyzer {
        name: &'static str,
        dependencies: Vec<&'static str>,
    }

    impl MockAnalyzer {
        fn new(name: &'static str) -> Self {
            Self {
                name,
                dependencies: Vec::new(),
            }
        }
    }

    impl PhaseAnalyzer for MockAnalyzer {
        fn phase_name(&self) -> &'static str {
            self.name
        }

        fn analyze(
            &mut self,
            _schema: &Schema,
            _context: &mut AnalysisContext,
        ) -> PhaseResult {
            PhaseResult::new(Vec::new())
        }

        fn dependencies(&self) -> &[&'static str] {
            &self.dependencies
        }
    }

    #[test]
    fn test_semantic_analyzer_creation() {
        let analyzer = SemanticAnalyzer::new();
        assert_eq!(analyzer.analyzer_names().len(), 5); // Symbol collector + type resolution + relationship + attribute validation + business rules by default
    }

    #[test]
    fn test_add_remove_analyzers() {
        let mut analyzer = SemanticAnalyzer::new();

        analyzer.add_phase_analyzer(Box::new(MockAnalyzer::new("Test")));
        assert_eq!(
            analyzer.analyzer_names(),
            vec![
                "symbol-collection",
                "type-resolution",
                "relationship-analysis",
                "attribute-validation",
                "business-rules",
                "Test"
            ]
        );

        assert!(analyzer.remove_phase_analyzer("Test"));
        assert_eq!(analyzer.analyzer_names().len(), 5); // Symbol collector + type resolution + relationship + attribute validation + business rules remain

        assert!(!analyzer.remove_phase_analyzer("NonExistent"));
    }

    #[test]
    fn test_dependency_graph_simple() {
        let mut graph = DependencyGraph::new();
        graph.add_node(0, "A".to_string());
        graph.add_node(1, "B".to_string());
        assert!(graph.add_edge(0, 1).is_ok(), "Should add edge successfully");

        let order = match graph.topological_sort() {
            Ok(order) => order,
            Err(e) => panic!("Should sort successfully: {e}"),
        };
        assert_eq!(order, vec![0, 1]);
    }

    #[test]
    fn test_dependency_graph_cycle_detection() {
        let mut graph = DependencyGraph::new();
        graph.add_node(0, "A".to_string());
        graph.add_node(1, "B".to_string());
        assert!(graph.add_edge(0, 1).is_ok(), "Should add edge successfully");
        assert!(graph.add_edge(1, 0).is_ok(), "Should add edge successfully"); // Creates cycle

        assert!(graph.has_cycles());
        assert!(graph.topological_sort().is_err());
        let cyc = graph.find_cycle();
        assert!(cyc.is_some());
    }

    struct FatalAnalyzer;

    impl PhaseAnalyzer for FatalAnalyzer {
        fn phase_name(&self) -> &'static str {
            "fatal-phase"
        }
        fn analyze(
            &mut self,
            _schema: &Schema,
            _context: &mut AnalysisContext,
        ) -> PhaseResult {
            PhaseResult::error(SemanticDiagnostic::error(
                crate::core::scanner::tokens::SymbolSpan {
                    start: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 1,
                    },
                    end: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 2,
                    },
                },
                "fatal".to_string(),
                DiagnosticCode::InternalError,
            ))
        }
    }

    struct WarningAnalyzer;
    impl PhaseAnalyzer for WarningAnalyzer {
        fn phase_name(&self) -> &'static str {
            "warn-phase"
        }
        fn analyze(
            &mut self,
            _schema: &Schema,
            _context: &mut AnalysisContext,
        ) -> PhaseResult {
            PhaseResult::new(vec![SemanticDiagnostic::warning(
                crate::core::scanner::tokens::SymbolSpan {
                    start: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 1,
                    },
                    end: crate::core::scanner::tokens::SymbolLocation {
                        line: 1,
                        column: 2,
                    },
                },
                "warning".to_string(),
                DiagnosticCode::PerformanceWarning,
            )])
        }
    }

    fn empty_schema() -> Schema {
        Schema {
            declarations: vec![],
            span: crate::core::scanner::tokens::SymbolSpan {
                start: crate::core::scanner::tokens::SymbolLocation {
                    line: 1,
                    column: 1,
                },
                end: crate::core::scanner::tokens::SymbolLocation {
                    line: 1,
                    column: 1,
                },
            },
        }
    }

    #[test]
    fn test_strict_mode_stops_on_fatal() {
        let mut sa = SemanticAnalyzer::with_analyzers(vec![
            Box::new(FatalAnalyzer),
            Box::new(WarningAnalyzer),
        ]);
        let schema = empty_schema();

        let opts = AnalyzerOptions {
            validation_mode: ValidationMode::Strict,
            ..AnalyzerOptions::default()
        };
        let res = match sa.analyze(&schema, &opts) {
            Ok(v) => v,
            Err(e) => panic!("analysis should succeed structurally: {e}"),
        };
        // Has the fatal error
        assert!(
            res.diagnostics
                .iter()
                .any(|d| d.diagnostic_code == DiagnosticCode::InternalError)
        );
        // Should not have the later phase's warning in strict mode
        assert!(
            res.diagnostics.iter().all(
                |d| d.diagnostic_code != DiagnosticCode::PerformanceWarning
            )
        );
    }

    #[test]
    fn test_lenient_mode_continues_after_fatal() {
        let mut sa = SemanticAnalyzer::with_analyzers(vec![
            Box::new(FatalAnalyzer),
            Box::new(WarningAnalyzer),
        ]);
        let schema = empty_schema();
        let opts = AnalyzerOptions {
            validation_mode: ValidationMode::Lenient,
            ..AnalyzerOptions::default()
        };
        let res = match sa.analyze(&schema, &opts) {
            Ok(v) => v,
            Err(e) => panic!("analysis should succeed structurally: {e}"),
        };
        // Both diagnostics should be present
        assert!(
            res.diagnostics
                .iter()
                .any(|d| d.diagnostic_code == DiagnosticCode::InternalError)
        );
        assert!(
            res.diagnostics.iter().any(
                |d| d.diagnostic_code == DiagnosticCode::PerformanceWarning
            )
        );
    }

    #[test]
    fn test_parallel_flag_path_equivalence() {
        let mut sa_a = SemanticAnalyzer::new();
        let mut sa_b = SemanticAnalyzer::new();
        let schema = empty_schema();
        let mut opts_a = AnalyzerOptions::default();
        opts_a.concurrency = ConcurrencyMode::Sequential;
        let opts_b = AnalyzerOptions::default();
        let res_a = match sa_a.analyze(&schema, &opts_a) {
            Ok(v) => v,
            Err(e) => panic!("{e}"),
        };
        let res_b = match sa_b.analyze(&schema, &opts_b) {
            Ok(v) => v,
            Err(e) => panic!("{e}"),
        };
        assert_eq!(res_a.diagnostics.len(), res_b.diagnostics.len());
        assert_eq!(res_a.analyzer_count, res_b.analyzer_count);
    }

    #[test]
    fn test_parallel_execution_layers() {
        let analyzer = SemanticAnalyzer::new();
        let dependency_graph = analyzer
            .build_dependency_graph()
            .expect("Should build graph");
        let layers =
            SemanticAnalyzer::compute_execution_layers(&dependency_graph)
                .expect("Should compute layers");

        // Verify all analyzers are included
        let total_analyzers: usize =
            layers.iter().map(std::vec::Vec::len).sum();
        assert_eq!(total_analyzers, analyzer.phase_analyzers.len());

        // Symbol collector should be in the first layer (no dependencies)
        let symbol_collector_index = analyzer
            .phase_analyzers
            .iter()
            .position(|a| a.phase_name() == "symbol-collection")
            .expect("Should find symbol collector");
        assert!(
            layers[0].contains(&symbol_collector_index),
            "Symbol collector should be in first layer"
        );

        // Verify no duplicates across layers
        let mut all_nodes = HashSet::new();
        for layer in &layers {
            for &node in layer {
                assert!(
                    all_nodes.insert(node),
                    "Node should not appear in multiple layers"
                );
            }
        }
    }
}
