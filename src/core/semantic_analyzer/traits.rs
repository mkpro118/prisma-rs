//! Core traits for semantic analysis components.
//!
//! This module defines the trait-based architecture that makes the semantic
//! analyzer fully pluggable. Different analyzer implementations can be composed
//! together to create custom analysis pipelines.

use crate::core::parser::ast::{FieldAttribute, Schema};
use crate::core::semantic_analyzer::{
    context::{AnalysisContext, PhaseResult},
    diagnostics::SemanticDiagnostic,
};

/// Core trait for analysis phases.
///
/// Each semantic analysis phase implements this trait to provide a standardized
/// interface for the orchestrator. Phases can declare dependencies and specify
/// whether they support parallel execution.
///
/// ## Examples
///
/// ```rust,ignore
/// struct MyAnalyzer;
///
/// impl PhaseAnalyzer for MyAnalyzer {
///     fn phase_name(&self) -> &'static str {
///         "Custom Analysis"
///     }
///     
///     fn analyze(&self, schema: &Schema, context: &AnalysisContext) -> PhaseResult {
///         let mut diagnostics = Vec::new();
///         // Perform analysis...
///         PhaseResult::new(diagnostics)
///     }
/// }
/// ```
pub trait PhaseAnalyzer: Send + Sync {
    /// Get the name of this analysis phase for debugging and dependency resolution.
    fn phase_name(&self) -> &'static str;

    /// Analyze the schema in this phase.
    ///
    /// The analyzer should examine the schema and context, perform its specific
    /// analysis, and return diagnostics. It may also update the shared state
    /// through the context's Arc<`RwLock`<>> protected fields.
    fn analyze(
        &self,
        schema: &Schema,
        context: &AnalysisContext,
    ) -> PhaseResult;

    /// Get the analysis dependencies (phases that must run before this one).
    ///
    /// Dependencies are specified by phase name. The orchestrator will ensure
    /// that all dependencies are completed before running this analyzer.
    fn dependencies(&self) -> &[&'static str] {
        &[]
    }

    /// Whether this analyzer can run in parallel with others.
    ///
    /// Analyzers that only read from the context and don't modify shared state
    /// can often run in parallel with other analyzers that have the same
    /// property.
    fn supports_parallel_execution(&self) -> bool {
        false
    }

    /// Get the priority of this analyzer within its dependency level.
    ///
    /// When multiple analyzers can run at the same time, those with higher
    /// priority will be scheduled first. Default priority is 0.
    fn priority(&self) -> i32 {
        0
    }
}

/// Trait for analyzing individual declarations.
///
/// This trait allows for fine-grained analysis of specific declaration types
/// (models, enums, etc.). Analyzers can implement this trait to focus on
/// particular aspects of declarations.
pub trait DeclarationAnalyzer<T>: Send + Sync {
    /// Analyze a specific declaration and return any diagnostics.
    fn analyze_declaration(
        &self,
        decl: &T,
        context: &AnalysisContext,
    ) -> Vec<SemanticDiagnostic>;

    /// Get the name of this declaration analyzer for debugging.
    fn analyzer_name(&self) -> &'static str;
}

/// Trait for analyzing relationships between declarations.
///
/// Relationship analyzers examine how different schema elements interact,
/// such as foreign key relationships, inheritance, or dependencies.
pub trait RelationshipAnalyzer: Send + Sync {
    /// Analyze relationships within the entire schema.
    fn analyze_relationships(
        &self,
        schema: &Schema,
        context: &AnalysisContext,
    ) -> Vec<SemanticDiagnostic>;

    /// Get the name of this relationship analyzer.
    fn analyzer_name(&self) -> &'static str;
}

/// Trait for analyzing attributes and their arguments.
///
/// Attribute analyzers validate that attributes are used correctly, have
/// valid arguments, and don't conflict with other attributes.
pub trait AttributeAnalyzer: Send + Sync {
    /// Analyze a specific attribute in context.
    fn analyze_attribute(
        &self,
        attr: &FieldAttribute,
        context: &AttributeContext,
    ) -> Vec<SemanticDiagnostic>;

    /// Get the set of attribute names this analyzer handles.
    fn supported_attributes(&self) -> &[&'static str];

    /// Get the name of this attribute analyzer.
    fn analyzer_name(&self) -> &'static str;
}

/// Context for attribute analysis.
///
/// Provides additional context about where an attribute appears and what
/// element it's attached to.
#[derive(Debug, Clone)]
pub struct AttributeContext<'a> {
    /// The schema element this attribute is attached to
    pub element_type: AttributeElementType,

    /// The name of the parent element (model name, field name, etc.)
    pub element_name: &'a str,

    /// Reference to the main analysis context
    pub analysis_context: &'a AnalysisContext,
}

/// Types of schema elements that can have attributes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttributeElementType {
    Model,
    Field,
    Enum,
    EnumValue,
    Datasource,
    Generator,
}

/// Trait for custom validation rules.
///
/// This trait allows users to implement custom business logic and validation
/// rules that are specific to their use case.
pub trait CustomRule: Send + Sync {
    /// Apply the custom rule to the schema.
    fn apply_rule(
        &self,
        schema: &Schema,
        context: &AnalysisContext,
    ) -> Vec<SemanticDiagnostic>;

    /// Get the name of this custom rule.
    fn rule_name(&self) -> &'static str;

    /// Get the priority of this rule (higher priority rules run first).
    fn priority(&self) -> i32 {
        0
    }
}

/// Trait for composable analyzer components.
///
/// This trait allows analyzers to be composed together into larger analysis
/// units while maintaining introspection capabilities for debugging and testing.
pub trait CompositeAnalyzer {
    /// Get the name of this analyzer component.
    fn component_name(&self) -> &'static str;

    /// Get child analyzer components if this is a composite.
    fn child_components(&self) -> Vec<&dyn CompositeAnalyzer> {
        Vec::new()
    }

    /// Get a hierarchical description of this analyzer's structure.
    fn structure_description(&self) -> String {
        let mut desc = self.component_name().to_string();
        let children = self.child_components();
        if !children.is_empty() {
            desc.push_str(" { ");
            for (i, child) in children.iter().enumerate() {
                if i > 0 {
                    desc.push_str(", ");
                }
                desc.push_str(&child.structure_description());
            }
            desc.push_str(" }");
        }
        desc
    }
}

/// Trait for analyzers that can provide progress information.
///
/// This trait enables progress monitoring and timeout detection for long-running
/// analysis operations.
pub trait ProgressReporting {
    /// Get the current progress as a percentage (0.0 to 1.0).
    fn progress(&self) -> f32;

    /// Get a description of what the analyzer is currently doing.
    fn current_activity(&self) -> Option<&str>;

    /// Check if the analyzer is still making progress.
    fn is_making_progress(&self) -> bool;

    /// Get the time when this analyzer last made progress.
    fn last_progress_time(&self) -> std::time::Instant;
}

/// Trait for analyzers that support cancellation.
///
/// Analyzers implementing this trait can be interrupted and stopped gracefully
/// when timeouts occur or when the user requests cancellation.
pub trait Cancellable {
    /// Request that the analyzer cancel its current operation.
    fn request_cancellation(&mut self);

    /// Check if cancellation has been requested.
    fn is_cancelled(&self) -> bool;

    /// Reset the cancellation state.
    fn reset_cancellation(&mut self);
}
