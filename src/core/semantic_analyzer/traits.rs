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

#[cfg(test)]
use crate::core::semantic_analyzer::ConcurrencyMode;

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

#[cfg(test)]
mod tests {
    use super::*;

    // Mock implementations for testing
    struct MockPhaseAnalyzer {
        name: &'static str,
        deps: Vec<&'static str>,
    }

    impl MockPhaseAnalyzer {
        fn new(name: &'static str) -> Self {
            Self {
                name,
                deps: Vec::new(),
            }
        }

        fn with_dependencies(mut self, deps: Vec<&'static str>) -> Self {
            self.deps = deps;
            self
        }
    }

    impl PhaseAnalyzer for MockPhaseAnalyzer {
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
            &self.deps
        }
    }

    #[test]
    fn test_phase_analyzer_basic_properties() {
        let analyzer = MockPhaseAnalyzer::new("Test Phase");
        assert_eq!(analyzer.phase_name(), "Test Phase");
        assert_eq!(analyzer.dependencies().len(), 0);
        assert!(!analyzer.supports_parallel_execution());
        assert_eq!(analyzer.priority(), 0);
    }

    #[test]
    fn test_phase_analyzer_with_dependencies() {
        let analyzer = MockPhaseAnalyzer::new("Dependent Phase")
            .with_dependencies(vec!["Phase A", "Phase B"]);
        assert_eq!(analyzer.dependencies(), &["Phase A", "Phase B"]);
    }

    #[test]
    fn test_attribute_element_type_equality() {
        assert_eq!(AttributeElementType::Model, AttributeElementType::Model);
        assert_ne!(AttributeElementType::Model, AttributeElementType::Field);
    }

    #[test]
    fn test_all_attribute_element_types() {
        let types = [
            AttributeElementType::Model,
            AttributeElementType::Field,
            AttributeElementType::Enum,
            AttributeElementType::EnumValue,
            AttributeElementType::Datasource,
            AttributeElementType::Generator,
        ];

        // Test all variants are unique
        for (i, type1) in types.iter().enumerate() {
            for (j, type2) in types.iter().enumerate() {
                if i == j {
                    assert_eq!(type1, type2);
                } else {
                    assert_ne!(type1, type2);
                }
            }
        }

        // Test Debug implementation
        assert_eq!(format!("{:?}", AttributeElementType::Model), "Model");
        assert_eq!(format!("{:?}", AttributeElementType::Field), "Field");
        assert_eq!(format!("{:?}", AttributeElementType::Enum), "Enum");
        assert_eq!(
            format!("{:?}", AttributeElementType::EnumValue),
            "EnumValue"
        );
        assert_eq!(
            format!("{:?}", AttributeElementType::Datasource),
            "Datasource"
        );
        assert_eq!(
            format!("{:?}", AttributeElementType::Generator),
            "Generator"
        );

        // Test Copy trait
        let original = AttributeElementType::Model;
        let copied = original;
        assert_eq!(original, copied);
    }

    #[test]
    fn test_attribute_context_creation() {
        use crate::core::semantic_analyzer::{
            AnalyzerOptions, DatabaseProvider, FeatureOptions, ValidationMode,
        };
        use std::time::Duration;

        let options = AnalyzerOptions {
            validation_mode: ValidationMode::Lenient,
            features: FeatureOptions {
                validate_experimental: true,
                performance_warnings: true,
                enable_parallelism: true,
            },
            concurrency: ConcurrencyMode::Concurrent {
                max_threads: 4,
                threshold: 2,
            },
            phase_timeout: Duration::from_secs(30),
            target_provider: Some(DatabaseProvider::PostgreSQL),
            max_diagnostics: 100,
        };

        let analysis_context = AnalysisContext::new_test(&options);

        let attr_context = AttributeContext {
            element_type: AttributeElementType::Field,
            element_name: "user_id",
            analysis_context: &analysis_context,
        };

        assert_eq!(attr_context.element_type, AttributeElementType::Field);
        assert_eq!(attr_context.element_name, "user_id");

        // Test cloning
        let cloned_context = attr_context.clone();
        assert_eq!(cloned_context.element_type, attr_context.element_type);
        assert_eq!(cloned_context.element_name, attr_context.element_name);

        // Test Debug
        let debug_str = format!("{attr_context:?}");
        assert!(debug_str.contains("Field"));
        assert!(debug_str.contains("user_id"));
    }

    // Mock implementations for testing other traits
    struct MockDeclarationAnalyzer {
        name: &'static str,
    }

    impl MockDeclarationAnalyzer {
        fn new(name: &'static str) -> Self {
            Self { name }
        }
    }

    impl DeclarationAnalyzer<String> for MockDeclarationAnalyzer {
        fn analyze_declaration(
            &self,
            _decl: &String,
            _context: &AnalysisContext,
        ) -> Vec<SemanticDiagnostic> {
            Vec::new()
        }

        fn analyzer_name(&self) -> &'static str {
            self.name
        }
    }

    struct MockRelationshipAnalyzer {
        name: &'static str,
    }

    impl MockRelationshipAnalyzer {
        fn new(name: &'static str) -> Self {
            Self { name }
        }
    }

    impl RelationshipAnalyzer for MockRelationshipAnalyzer {
        fn analyze_relationships(
            &self,
            _schema: &Schema,
            _context: &AnalysisContext,
        ) -> Vec<SemanticDiagnostic> {
            Vec::new()
        }

        fn analyzer_name(&self) -> &'static str {
            self.name
        }
    }

    struct MockAttributeAnalyzer {
        name: &'static str,
        supported_attrs: Vec<&'static str>,
    }

    impl MockAttributeAnalyzer {
        fn new(name: &'static str, supported: Vec<&'static str>) -> Self {
            Self {
                name,
                supported_attrs: supported,
            }
        }
    }

    impl AttributeAnalyzer for MockAttributeAnalyzer {
        fn analyze_attribute(
            &self,
            _attr: &FieldAttribute,
            _context: &AttributeContext,
        ) -> Vec<SemanticDiagnostic> {
            Vec::new()
        }

        fn supported_attributes(&self) -> &[&'static str] {
            &self.supported_attrs
        }

        fn analyzer_name(&self) -> &'static str {
            self.name
        }
    }

    struct MockCustomRule {
        name: &'static str,
        rule_priority: i32,
    }

    impl MockCustomRule {
        fn new(name: &'static str) -> Self {
            Self {
                name,
                rule_priority: 0,
            }
        }

        fn with_priority(mut self, priority: i32) -> Self {
            self.rule_priority = priority;
            self
        }
    }

    impl CustomRule for MockCustomRule {
        fn apply_rule(
            &self,
            _schema: &Schema,
            _context: &AnalysisContext,
        ) -> Vec<SemanticDiagnostic> {
            Vec::new()
        }

        fn rule_name(&self) -> &'static str {
            self.name
        }

        fn priority(&self) -> i32 {
            self.rule_priority
        }
    }

    struct MockCompositeAnalyzer {
        name: &'static str,
        children: Vec<Box<dyn CompositeAnalyzer>>,
    }

    impl MockCompositeAnalyzer {
        fn new(name: &'static str) -> Self {
            Self {
                name,
                children: Vec::new(),
            }
        }

        fn with_child(mut self, child: Box<dyn CompositeAnalyzer>) -> Self {
            self.children.push(child);
            self
        }
    }

    impl CompositeAnalyzer for MockCompositeAnalyzer {
        fn component_name(&self) -> &'static str {
            self.name
        }

        fn child_components(&self) -> Vec<&dyn CompositeAnalyzer> {
            self.children
                .iter()
                .map(std::convert::AsRef::as_ref)
                .collect()
        }
    }

    #[test]
    fn test_declaration_analyzer() {
        use crate::core::semantic_analyzer::AnalyzerOptions;

        let analyzer = MockDeclarationAnalyzer::new("TestDeclarationAnalyzer");
        assert_eq!(analyzer.analyzer_name(), "TestDeclarationAnalyzer");

        // Create a mock context for testing
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let test_declaration = String::from("test_model");
        let diagnostics =
            analyzer.analyze_declaration(&test_declaration, &context);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_relationship_analyzer() {
        use crate::core::parser::ast::{Declaration, Schema};
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
        use crate::core::semantic_analyzer::AnalyzerOptions;

        let analyzer =
            MockRelationshipAnalyzer::new("TestRelationshipAnalyzer");
        assert_eq!(analyzer.analyzer_name(), "TestRelationshipAnalyzer");

        let schema = Schema {
            declarations: Vec::<Declaration>::new(),
            span: SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            },
        };
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let diagnostics = analyzer.analyze_relationships(&schema, &context);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_attribute_analyzer() {
        use crate::core::parser::ast::{FieldAttribute, Ident, QualifiedIdent};
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
        use crate::core::semantic_analyzer::AnalyzerOptions;

        let analyzer = MockAttributeAnalyzer::new(
            "TestAttributeAnalyzer",
            vec!["id", "default", "unique"],
        );

        assert_eq!(analyzer.analyzer_name(), "TestAttributeAnalyzer");
        assert_eq!(
            analyzer.supported_attributes(),
            &["id", "default", "unique"]
        );

        // Create mock attribute and context
        let span = SymbolSpan {
            start: SymbolLocation { line: 1, column: 1 },
            end: SymbolLocation { line: 1, column: 5 },
        };

        let attr = FieldAttribute {
            name: QualifiedIdent {
                parts: vec![Ident {
                    text: "id".to_string(),
                    span: span.clone(),
                }],
                span: span.clone(),
            },
            args: None,
            docs: None,
            span: span.clone(),
        };

        let options = AnalyzerOptions::default();
        let analysis_context = AnalysisContext::new_test(&options);
        let attr_context = AttributeContext {
            element_type: AttributeElementType::Field,
            element_name: "user_id",
            analysis_context: &analysis_context,
        };

        let diagnostics = analyzer.analyze_attribute(&attr, &attr_context);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_custom_rule() {
        use crate::core::parser::ast::{Declaration, Schema};
        use crate::core::scanner::tokens::{SymbolLocation, SymbolSpan};
        use crate::core::semantic_analyzer::AnalyzerOptions;

        let rule = MockCustomRule::new("TestCustomRule");
        assert_eq!(rule.rule_name(), "TestCustomRule");
        assert_eq!(rule.priority(), 0); // Default priority

        let high_priority_rule =
            MockCustomRule::new("HighPriorityRule").with_priority(100);
        assert_eq!(high_priority_rule.rule_name(), "HighPriorityRule");
        assert_eq!(high_priority_rule.priority(), 100);

        let schema = Schema {
            declarations: Vec::<Declaration>::new(),
            span: SymbolSpan {
                start: SymbolLocation { line: 1, column: 1 },
                end: SymbolLocation { line: 1, column: 1 },
            },
        };
        let options = AnalyzerOptions::default();
        let context = AnalysisContext::new_test(&options);

        let diagnostics = rule.apply_rule(&schema, &context);
        assert!(diagnostics.is_empty());

        let high_priority_diagnostics =
            high_priority_rule.apply_rule(&schema, &context);
        assert!(high_priority_diagnostics.is_empty());
    }

    #[test]
    fn test_composite_analyzer_simple() {
        let analyzer = MockCompositeAnalyzer::new("SimpleAnalyzer");
        assert_eq!(analyzer.component_name(), "SimpleAnalyzer");
        assert!(analyzer.child_components().is_empty());
        assert_eq!(analyzer.structure_description(), "SimpleAnalyzer");
    }

    #[test]
    fn test_composite_analyzer_with_children() {
        let child1 = Box::new(MockCompositeAnalyzer::new("Child1"));
        let child2 = Box::new(MockCompositeAnalyzer::new("Child2"));

        let parent = MockCompositeAnalyzer::new("Parent")
            .with_child(child1)
            .with_child(child2);

        assert_eq!(parent.component_name(), "Parent");
        assert_eq!(parent.child_components().len(), 2);
        assert_eq!(parent.child_components()[0].component_name(), "Child1");
        assert_eq!(parent.child_components()[1].component_name(), "Child2");

        let structure = parent.structure_description();
        assert_eq!(structure, "Parent { Child1, Child2 }");
    }

    #[test]
    fn test_composite_analyzer_nested() {
        let grandchild = Box::new(MockCompositeAnalyzer::new("GrandChild"));
        let child = Box::new(
            MockCompositeAnalyzer::new("Child").with_child(grandchild),
        );
        let parent = MockCompositeAnalyzer::new("Parent").with_child(child);

        let structure = parent.structure_description();
        assert_eq!(structure, "Parent { Child { GrandChild } }");
    }

    #[test]
    fn test_phase_analyzer_parallel_and_priority() {
        struct ParallelAnalyzer {
            name: &'static str,
            priority: i32,
        }

        impl ParallelAnalyzer {
            fn new(name: &'static str, priority: i32) -> Self {
                Self { name, priority }
            }
        }

        impl PhaseAnalyzer for ParallelAnalyzer {
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

            fn supports_parallel_execution(&self) -> bool {
                true
            }

            fn priority(&self) -> i32 {
                self.priority
            }
        }

        let analyzer = ParallelAnalyzer::new("ParallelPhase", 50);
        assert_eq!(analyzer.phase_name(), "ParallelPhase");
        assert!(analyzer.supports_parallel_execution());
        assert_eq!(analyzer.priority(), 50);
        assert_eq!(analyzer.dependencies().len(), 0);
    }
}
