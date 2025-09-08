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
    ///
    /// # Panics
    ///
    /// Panics if the symbol table write lock is poisoned due to a panic in another thread.
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
        *self.symbol_table.write().map_err(|e| {
            AnalysisError::InvalidDependencyGraph {
                message: format!("Failed to acquire symbol table lock: {e}"),
            }
        })? = SymbolTable::new();
        *self.type_resolver.write().map_err(|e| {
            AnalysisError::InvalidDependencyGraph {
                message: format!("Failed to acquire type resolver lock: {e}"),
            }
        })? = TypeResolver::new();
        *self.relationship_graph.write().map_err(|e| {
            AnalysisError::InvalidDependencyGraph {
                message: format!(
                    "Failed to acquire relationship graph lock: {e}"
                ),
            }
        })? = RelationshipGraph::default();

        // Create analysis context with shared state
        let mut context = AnalysisContext::new(
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
                    &mut context,
                    options,
                    &mut temp_diagnostics,
                )?;
                self.diagnostic_collector
                    .extend(temp_diagnostics.take_all());
            }
            ConcurrencyMode::Concurrent { .. } => {
                self.analyze_parallel(schema, &mut context, options)?;
            }
        }

        let analysis_time = start_time.elapsed();

        // Build final result
        Ok(AnalysisResult {
            symbol_table: (*self.symbol_table.read().map_err(|e| {
                AnalysisError::InvalidDependencyGraph {
                    message: format!(
                        "Failed to acquire symbol table read lock: {e}"
                    ),
                }
            })?)
            .clone(),
            type_resolver: (*self.type_resolver.read().map_err(|e| {
                AnalysisError::InvalidDependencyGraph {
                    message: format!(
                        "Failed to acquire type resolver read lock: {e}"
                    ),
                }
            })?)
            .clone(),
            relationship_graph: (*self.relationship_graph.read().map_err(
                |e| AnalysisError::InvalidDependencyGraph {
                    message: format!(
                        "Failed to acquire relationship graph read lock: {e}"
                    ),
                },
            )?)
            .clone(),
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
        context: &mut AnalysisContext,
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

            // Execute the analyzer with per-phase timing
            let phase_name = analyzer.phase_name().to_string();
            let started = Instant::now();
            let phase_result = analyzer.analyze(schema, context);
            let duration = started.elapsed();
            context.record_phase_timing(phase_name.clone(), duration);

            // Per-phase timeout check
            if duration > options.phase_timeout {
                return Err(AnalysisError::Timeout {
                    phase: phase_name,
                    elapsed: duration,
                });
            }
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
        context: &mut AnalysisContext,
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
                // Provide actual cycle if available
                let cycle = dependency_graph
                    .find_cycle()
                    .unwrap_or_else(|| vec!["Unknown".to_string()]);
                return Err(AnalysisError::CircularDependency { cycle });
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
        context: &mut AnalysisContext,
        options: &AnalyzerOptions,
        layer: &[usize],
    ) -> Result<(), AnalysisError> {
        if layer.len() == 1 {
            // Single analyzer - no need for threading overhead
            let analyzer_index = layer[0];
            let analyzer = &self.phase_analyzers[analyzer_index];

            let phase_name = analyzer.phase_name().to_string();
            let started = Instant::now();
            let phase_result = analyzer.analyze(schema, context);
            let duration = started.elapsed();
            context.record_phase_timing(phase_name.clone(), duration);

            if duration > options.phase_timeout {
                return Err(AnalysisError::Timeout {
                    phase: phase_name,
                    elapsed: duration,
                });
            }
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

        let (_max_threads, threshold) = match options.concurrency {
            ConcurrencyMode::Sequential => (1, 0),
            ConcurrencyMode::Concurrent {
                max_threads,
                threshold,
            } => (max_threads, threshold),
        };

        if parallel_analyzers.len() > threshold && parallel_analyzers.len() > 1
        {
            // Execute parallel analyzers using scoped threads for true parallelism
            use std::sync::Mutex;
            use std::thread;

            let results = Arc::new(Mutex::new(Vec::new()));

            // Convert to immutable reference for sharing across threads
            let context_ref: &AnalysisContext = context;

            thread::scope(|s| {
                let mut handles = Vec::new();

                for &analyzer_index in &parallel_analyzers {
                    let analyzer = &self.phase_analyzers[analyzer_index];
                    let results_clone = Arc::clone(&results);

                    let handle = s.spawn(move || {
                        let phase_name = analyzer.phase_name().to_string();
                        let started = Instant::now();
                        // Use immutable reference to context - safe to share across threads
                        let phase_result =
                            analyzer.analyze(schema, context_ref);
                        let duration = started.elapsed();

                        // Collect result for main thread processing
                        // (timing will be recorded by main thread)
                        match results_clone.lock() {
                            Ok(mut results_guard) => {
                                results_guard.push((
                                    phase_name,
                                    phase_result,
                                    duration,
                                ));
                            }
                            Err(poison_error) => {
                                panic!("Failed to acquire lock on results in thread: {poison_error:?}");
                            }
                        }
                    });

                    handles.push(handle);
                }

                // Wait for all threads to complete and handle panics
                for handle in handles {
                    if let Err(panic_payload) = handle.join() {
                        let panic_message = if let Some(s) =
                            panic_payload.downcast_ref::<&str>()
                        {
                            (*s).to_string()
                        } else if let Some(s) =
                            panic_payload.downcast_ref::<String>()
                        {
                            s.clone()
                        } else {
                            "Thread panicked with unknown payload".to_string()
                        };

                        return Err(AnalysisError::ThreadPanic {
                            phase: "parallel execution".to_string(),
                            message: panic_message,
                        });
                    }
                }
                Ok(())
            })?;

            // Process results from parallel execution
            let results = Arc::try_unwrap(results)
                .map_err(|_| AnalysisError::ThreadPanic {
                    phase: "parallel execution cleanup".to_string(), 
                    message: "Failed to unwrap results Arc - multiple references remain".to_string(),
                })?
                .into_inner()
                .map_err(|e| AnalysisError::ThreadPanic {
                    phase: "parallel execution cleanup".to_string(),
                    message: format!("Failed to acquire results mutex: {e:?}"),
                })?;
            for (phase_name, phase_result, duration) in results {
                // Record timing information
                context.record_phase_timing(phase_name.clone(), duration);

                if duration > options.phase_timeout {
                    return Err(AnalysisError::Timeout {
                        phase: phase_name,
                        elapsed: duration,
                    });
                }

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

                let phase_name = analyzer.phase_name().to_string();
                let started = Instant::now();
                let phase_result = analyzer.analyze(schema, context);
                let duration = started.elapsed();
                context.record_phase_timing(phase_name.clone(), duration);

                if duration > options.phase_timeout {
                    return Err(AnalysisError::Timeout {
                        phase: phase_name,
                        elapsed: duration,
                    });
                }
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
    /// Thread panic during parallel execution
    ThreadPanic { phase: String, message: String },
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
            AnalysisError::ThreadPanic { phase, message } => {
                write!(f, "Thread panic in phase '{phase}': {message}")
            }
        }
    }
}

impl std::error::Error for AnalysisError {}

#[cfg(test)]
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
            &self,
            _schema: &Schema,
            _context: &AnalysisContext,
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
            &self,
            _schema: &Schema,
            _context: &AnalysisContext,
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
            &self,
            _schema: &Schema,
            _context: &AnalysisContext,
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
        let opts_a = AnalyzerOptions {
            concurrency: ConcurrencyMode::Sequential,
            ..AnalyzerOptions::default()
        };
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

    #[test]
    fn test_pipeline_shared_state_end_to_end() {
        use crate::core::parser::ast::*;
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};

        #[rustfmt::skip]
        fn sp() -> SymbolSpan {
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 10 },
            }
        }

        // datasource
        #[rustfmt::skip]
        let datasource = DatasourceDecl {
            name: Ident { text: "db".into(), span: sp() },
            assignments: vec![Assignment {
                key: Ident { text: "provider".into(), span: sp() },
                value: Expr::StringLit(StringLit {
                    value: "postgresql".into(), span: sp(),
                }), docs: None, span: sp(),
            }], docs: None, span: sp(),
        };

        // Model Post
        #[rustfmt::skip]
        let post = ModelDecl {
            docs: None,
            name: Ident { text: "Post".into(), span: sp() },
            members: vec![ModelMember::Field(FieldDecl {
                docs: None,
                name: Ident { text: "title".into(), span: sp() },
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![Ident { text: "String".into(), span: sp() }],
                        span: sp(),
                    }, span: sp(),
                }),
                optional: false, modifiers: vec![], attrs: vec![], span: sp(),
            })],
            attrs: vec![], span: sp(),
        };

        // Model User with relation to Post
        #[rustfmt::skip]
        let user = ModelDecl {
            docs: None,
            name: Ident { text: "User".into(), span: sp() },
            members: vec![ModelMember::Field(FieldDecl {
                docs: None,
                name: Ident { text: "posts".into(), span: sp() },
                r#type: TypeRef::List(ListType {
                    inner: Box::new(TypeRef::Named(NamedType {
                        name: QualifiedIdent {
                            parts: vec![Ident { text: "Post".into(), span: sp() }],
                            span: sp(),
                        }, span: sp(),
                    })), span: sp(),
                }),
                optional: false, modifiers: vec![],
                attrs: vec![FieldAttribute {
                    docs: None,
                    name: QualifiedIdent {
                        parts: vec![Ident { text: "relation".into(), span: sp(),
                        }], span: sp(),
                    }, args: None, span: sp(),
                }], span: sp(),
            })], attrs: vec![], span: sp(),
        };

        #[rustfmt::skip]
        let schema = Schema {
            declarations: vec![
                Declaration::Datasource(datasource),
                Declaration::Model(user),
                Declaration::Model(post),
            ], span: sp(),
        };

        let options = AnalyzerOptions::default();
        let mut sa = SemanticAnalyzer::new();
        let result = sa.analyze(&schema, &options).expect("analysis ok");

        // Symbol table should contain our two models
        let model_names: Vec<_> = result
            .symbol_table
            .models()
            .map(|(n, _)| n.clone())
            .collect();
        assert!(model_names.contains(&"User".to_string()));
        assert!(model_names.contains(&"Post".to_string()));

        // No UnknownType errors expected
        #[rustfmt::skip]
        assert!(
            result.diagnostics.iter()
                .all(|d| d.diagnostic_code != DiagnosticCode::UnknownType)
        );

        // Ensure analysis produced per-phase timings for at least one phase
        let summary = result.summary();
        assert!(summary.total_symbols >= 2);
        // Expect symbol-collection phase timing to be present
        #[rustfmt::skip]
        assert!(result.analysis_metadata.get_phase_timing("symbol-collection").is_some());

        // Expect attribute-validation phase timing to be present (ran after symbol collection)
        #[rustfmt::skip]
        assert!(result.analysis_metadata.get_phase_timing("attribute-validation").is_some());

        // Relationship graph should include the User->posts relationship id
        let graph = &result.relationship_graph;
        let user_edges = graph.model_relationships.get("User");
        assert!(user_edges.is_some());
        let ids = user_edges.unwrap();
        assert!(ids.iter().any(|id| id == "User_posts"));
    }

    #[test]
    fn test_pipeline_attribute_invalid_argument_span() {
        use crate::core::parser::ast::*;
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
        use crate::core::semantic_analyzer::{AnalyzerOptions, DiagnosticCode};

        #[rustfmt::skip]
        fn sp() -> SymbolSpan {
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 20 },
            }
        }

        #[rustfmt::skip]
        let field = FieldDecl {
            docs: None,
            name: Ident { text: "email".into(), span: sp() },
            r#type: TypeRef::Named(NamedType {
                name: QualifiedIdent {
                    parts: vec![Ident { text: "String".into(), span: sp() }],
                    span: sp(),
                }, span: sp(),
            }),
            optional: false, modifiers: vec![],
            attrs: vec![FieldAttribute {
                docs: None,
                name: QualifiedIdent {
                    parts: vec![Ident { text: "unique".into(), span: sp() }],
                    span: sp(),
                },
                args: Some(ArgList {
                    items: vec![Arg::Named(NamedArg {
                        name: Ident { text: "invalid_arg".into(), span: sp() },
                        value: Expr::StringLit(StringLit { value: "value".into(), span: sp() }),
                        span: sp(),
                    })], span: sp(),
                }), span: sp(),
            }], span: sp(),
        };

        #[rustfmt::skip]
        let model = ModelDecl {
            docs: None, attrs: vec![], span: sp(),
            name: Ident { text: "User".into(), span: sp() },
            members: vec![ModelMember::Field(field)],
        };

        let datasource = DatasourceDecl {
            name: Ident {
                text: "db".into(),
                span: sp(),
            },
            assignments: vec![Assignment {
                key: Ident {
                    text: "provider".into(),
                    span: sp(),
                },
                value: Expr::StringLit(StringLit {
                    value: "postgresql".into(),
                    span: sp(),
                }),
                docs: None,
                span: sp(),
            }],
            docs: None,
            span: sp(),
        };

        #[rustfmt::skip]
        let schema = Schema {
            declarations: vec![
                Declaration::Datasource(datasource),
                Declaration::Model(model),
            ], span: sp(),
        };

        let options = AnalyzerOptions::default();
        let mut sa = SemanticAnalyzer::new();
        let result = sa.analyze(&schema, &options).expect("analysis ok");

        // Find invalid attribute argument diagnostic and ensure span is non-zero
        let invalids: Vec<_> = result
            .diagnostics
            .iter()
            .filter(|d| {
                d.diagnostic_code == DiagnosticCode::InvalidAttributeArgument
            })
            .collect();

        assert!(
            !invalids.is_empty(),
            "expected at least one InvalidAttributeArgument diagnostic"
        );
        assert!(invalids[0].span.start.line > 0);
        assert!(invalids[0].span.end.line > 0);
    }

    #[test]
    fn test_true_parallel_execution() {
        use crate::core::parser::ast::*;
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
        use std::time::Duration;

        fn sp() -> SymbolSpan {
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation {
                    line: 1,
                    column: 10,
                },
            }
        }

        // Create a schema that will trigger multiple analyzers
        let model = ModelDecl {
            docs: None,
            name: Ident {
                text: "User".into(),
                span: sp(),
            },
            members: vec![ModelMember::Field(FieldDecl {
                docs: None,
                name: Ident {
                    text: "id".into(),
                    span: sp(),
                },
                r#type: TypeRef::Named(NamedType {
                    name: QualifiedIdent {
                        parts: vec![Ident {
                            text: "Int".into(),
                            span: sp(),
                        }],
                        span: sp(),
                    },
                    span: sp(),
                }),
                optional: false,
                modifiers: Vec::new(),
                attrs: vec![FieldAttribute {
                    docs: None,
                    name: QualifiedIdent {
                        parts: vec![Ident {
                            text: "id".into(),
                            span: sp(),
                        }],
                        span: sp(),
                    },
                    args: None,
                    span: sp(),
                }],
                span: sp(),
            })],
            attrs: Vec::new(),
            span: sp(),
        };

        let schema = Schema {
            declarations: vec![Declaration::Model(model)],
            span: sp(),
        };

        // Test with concurrent mode to trigger parallel execution
        let mut analyzer = SemanticAnalyzer::new();
        let options = AnalyzerOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 1, // Low threshold to ensure parallel execution kicks in
            },
            ..AnalyzerOptions::default()
        };

        let start_time = std::time::Instant::now();
        let result = analyzer.analyze(&schema, &options);
        let duration = start_time.elapsed();

        // Analysis should succeed
        assert!(result.is_ok(), "Parallel analysis should succeed");
        let result = result.unwrap();

        // Analysis should have completed successfully
        assert!(result.analyzer_count > 0, "Should have run analyzers");

        // Should complete in reasonable time (parallel execution should be fast)
        assert!(
            duration < Duration::from_secs(5),
            "Analysis should complete quickly: {duration:?}"
        );
    }

    #[test]
    fn test_parallel_vs_sequential_consistency() {
        use crate::core::parser::ast::*;
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};

        fn sp() -> SymbolSpan {
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation {
                    line: 1,
                    column: 10,
                },
            }
        }

        // Create a schema with multiple models and relationships
        let schema = Schema {
            declarations: vec![Declaration::Model(ModelDecl {
                docs: None,
                name: Ident {
                    text: "User".into(),
                    span: sp(),
                },
                members: vec![ModelMember::Field(FieldDecl {
                    docs: None,
                    name: Ident {
                        text: "id".into(),
                        span: sp(),
                    },
                    r#type: TypeRef::Named(NamedType {
                        name: QualifiedIdent {
                            parts: vec![Ident {
                                text: "Int".into(),
                                span: sp(),
                            }],
                            span: sp(),
                        },
                        span: sp(),
                    }),
                    optional: false,
                    modifiers: Vec::new(),
                    attrs: vec![FieldAttribute {
                        docs: None,
                        name: QualifiedIdent {
                            parts: vec![Ident {
                                text: "id".into(),
                                span: sp(),
                            }],
                            span: sp(),
                        },
                        args: None,
                        span: sp(),
                    }],
                    span: sp(),
                })],
                attrs: Vec::new(),
                span: sp(),
            })],
            span: sp(),
        };

        // Run with sequential mode
        let mut analyzer_sequential = SemanticAnalyzer::new();
        let sequential_options = AnalyzerOptions {
            concurrency: ConcurrencyMode::Sequential,
            ..AnalyzerOptions::default()
        };
        let sequential_result = analyzer_sequential
            .analyze(&schema, &sequential_options)
            .expect("Sequential analysis should succeed");

        // Run with concurrent mode
        let mut analyzer_parallel = SemanticAnalyzer::new();
        let parallel_options = AnalyzerOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 1,
            },
            ..AnalyzerOptions::default()
        };
        let parallel_result = analyzer_parallel
            .analyze(&schema, &parallel_options)
            .expect("Parallel analysis should succeed");

        // Results should be consistent
        assert_eq!(
            sequential_result.diagnostics.len(),
            parallel_result.diagnostics.len(),
            "Sequential and parallel should produce same number of diagnostics"
        );

        // Both should have the same analyzers
        assert_eq!(
            sequential_result.analyzer_count, parallel_result.analyzer_count,
            "Should have same analyzer count"
        );

        // Symbol table contents should be equivalent
        assert_eq!(
            sequential_result.symbol_table.models().count(),
            parallel_result.symbol_table.models().count(),
            "Should have same number of models in symbol table"
        );
    }

    #[test]
    fn test_concurrent_mode_thread_safety() {
        // This test specifically tests the thread safety of the new parallel implementation
        use crate::core::parser::ast::*;
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
        use std::sync::Arc;
        use std::thread;

        fn sp() -> SymbolSpan {
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation {
                    line: 1,
                    column: 10,
                },
            }
        }

        let schema = Arc::new(Schema {
            declarations: vec![Declaration::Model(ModelDecl {
                docs: None,
                name: Ident {
                    text: "TestModel".into(),
                    span: sp(),
                },
                members: vec![ModelMember::Field(FieldDecl {
                    docs: None,
                    name: Ident {
                        text: "id".into(),
                        span: sp(),
                    },
                    r#type: TypeRef::Named(NamedType {
                        name: QualifiedIdent {
                            parts: vec![Ident {
                                text: "Int".into(),
                                span: sp(),
                            }],
                            span: sp(),
                        },
                        span: sp(),
                    }),
                    optional: false,
                    modifiers: Vec::new(),
                    attrs: vec![FieldAttribute {
                        docs: None,
                        name: QualifiedIdent {
                            parts: vec![Ident {
                                text: "id".into(),
                                span: sp(),
                            }],
                            span: sp(),
                        },
                        args: None,
                        span: sp(),
                    }],
                    span: sp(),
                })],
                attrs: Vec::new(),
                span: sp(),
            })],
            span: sp(),
        });

        let options = Arc::new(AnalyzerOptions {
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 2,
                threshold: 1,
            },
            ..AnalyzerOptions::default()
        });

        let mut handles = Vec::new();

        // Run multiple concurrent analyses to test thread safety
        for _ in 0..3 {
            let schema_clone = Arc::clone(&schema);
            let options_clone = Arc::clone(&options);

            let handle = thread::spawn(move || {
                let mut analyzer = SemanticAnalyzer::new();
                analyzer.analyze(&schema_clone, &options_clone)
            });

            handles.push(handle);
        }

        // Collect all results - they should all succeed
        let mut all_succeeded = true;
        for handle in handles {
            match handle.join() {
                Ok(Ok(_result)) => {
                    // Analysis succeeded
                }
                Ok(Err(_)) | Err(_) => {
                    all_succeeded = false;
                }
            }
        }

        assert!(all_succeeded, "All concurrent analyses should succeed");
    }

    #[test]
    fn test_parallel_execution_performance_characteristics() {
        // This test verifies that parallel execution actually provides some benefit
        // Note: This is more of a smoke test since performance can vary
        use crate::core::parser::ast::*;
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
        use std::time::Instant;

        fn sp() -> SymbolSpan {
            SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation {
                    line: 1,
                    column: 10,
                },
            }
        }

        // Create a more complex schema to potentially see parallel benefits
        let mut declarations = Vec::new();

        for i in 0..10 {
            declarations.push(Declaration::Model(ModelDecl {
                docs: None,
                name: Ident {
                    text: format!("Model{i}"),
                    span: sp(),
                },
                members: vec![ModelMember::Field(FieldDecl {
                    docs: None,
                    name: Ident {
                        text: "id".into(),
                        span: sp(),
                    },
                    r#type: TypeRef::Named(NamedType {
                        name: QualifiedIdent {
                            parts: vec![Ident {
                                text: "Int".into(),
                                span: sp(),
                            }],
                            span: sp(),
                        },
                        span: sp(),
                    }),
                    optional: false,
                    modifiers: Vec::new(),
                    attrs: vec![FieldAttribute {
                        docs: None,
                        name: QualifiedIdent {
                            parts: vec![Ident {
                                text: "id".into(),
                                span: sp(),
                            }],
                            span: sp(),
                        },
                        args: None,
                        span: sp(),
                    }],
                    span: sp(),
                })],
                attrs: Vec::new(),
                span: sp(),
            }));
        }

        let schema = Schema {
            declarations,
            span: sp(),
        };

        // Test sequential execution
        let start = Instant::now();
        let mut analyzer_seq = SemanticAnalyzer::new();
        let seq_result = analyzer_seq
            .analyze(
                &schema,
                &AnalyzerOptions {
                    concurrency: ConcurrencyMode::Sequential,
                    ..AnalyzerOptions::default()
                },
            )
            .expect("Sequential should work");
        let seq_duration = start.elapsed();

        // Test parallel execution
        let start = Instant::now();
        let mut analyzer_par = SemanticAnalyzer::new();
        let par_result = analyzer_par
            .analyze(
                &schema,
                &AnalyzerOptions {
                    concurrency: ConcurrencyMode::Concurrent {
                        max_threads: 4,
                        threshold: 1,
                    },
                    ..AnalyzerOptions::default()
                },
            )
            .expect("Parallel should work");
        let par_duration = start.elapsed();

        // Both should produce same results
        assert_eq!(seq_result.diagnostics.len(), par_result.diagnostics.len());
        assert_eq!(seq_result.analyzer_count, par_result.analyzer_count);

        // Both should complete in reasonable time (this is a smoke test)
        assert!(
            seq_duration.as_millis() < 1000,
            "Sequential should be reasonably fast"
        );
        assert!(
            par_duration.as_millis() < 1000,
            "Parallel should be reasonably fast"
        );

        println!("Sequential: {seq_duration:?}, Parallel: {par_duration:?}");
    }
}
