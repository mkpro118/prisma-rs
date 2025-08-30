# Prisma Types Generator – Implementation Plan (Source of Truth)

> A compiler-style binary (implemented in Rust) that ingests a Prisma schema
> and emits type definitions for one or more target languages via a pluggable
> codegen API. This document defines scope, architecture, contracts, and
> milestones. It intentionally avoids code-level details; API suggestions below
> are conceptual contracts, not implementation.

---

## Objectives

- **Primary:** Convert a Prisma schema into a verified, language-agnostic
  intermediate representation (IR) and generate type definition artifacts for
  target languages (e.g., TypeScript, Python, Go, Rust, etc.) via plugins.
- **Secondary:** Provide a clean, compiler-like UX: scanning -> parsing
  -> semantic analysis -> type checking -> IR -> pluggable codegen.
- **Developer Experience:** Stable, well-documented plugin API;
  helpful diagnostics with precise source locations; predictable CLI and config.

**Success criteria**

- Given a valid Prisma schema, output correct, idiomatic type definitions for
  at least one target language.
- Clear, stable contracts between stages and plugins (versioned IR + plugin API).
- Deterministic output with snapshot/golden tests.
- Structured diagnostics (human-readable and machine-readable).

---

## Non-Goals (for v1)

- Runtime client generation or ORM code; **types only**.
- Database introspection or schema migration.
- Full Prisma feature parity on day one; we will prioritize core
  model/enum/scalar features and iterate.

---

## High-Level Architecture

```
Input Prisma Schema
   |
   v
[Scanner] -> TokenStream
   |
   v
[Parser] -> AST + Symbols
   |
   v
[Semantic Analysis & Type Checking] -> TypeGraph + Diagnostics
   |
   v
[IR Builder] -> Language-Agnostic IR (stable, versioned)
   │
   ▼
[Codegen Plugins] -> Artifacts (files/strings) per target language
```

Each stage consumes the previous stage's output and produces the next stage's
input, plus diagnostics.

---

## Core Data Models (Conceptual)

- **Token**: kind, lexeme, span.
- **TokenStream**: ordered iterable of Token with lookahead support.
- **AST**: nodes for datasource, generator, model, enum, field, attribute
  (decorator), relation, default, map, etc.; all nodes carry spans.
- **SymbolTable**: scoped bindings for models, enums, scalars, attributes.
- **TypeGraph**: resolved types, relations, cardinalities, nullability,
  constraints.
- **Diagnostic**: severity (error/warn/info), message, primary span, secondary
  notes/hints, code.
- **IR (v1)**: normalized, language-agnostic schema: scalars, enums, models
  (fields, relations, indexes, unique constraints, docs/annotations), naming
  metadata, nullability, default values, attribute projections.
- **Artifact**: one or more named outputs (e.g., files): name, relative\_path,
  content (string or bytes), suggested formatter.

> Guideline: prefer **specific** return types in interfaces
> (e.g., `TokenStream`, `TypeGraph`, `ArtifactBundle`) rather than generic
> containers.

---

## Compiler Pipeline & Contracts

### 5.1 Scanner / Lexical Analysis

**Purpose:** Convert schema text into tokens with spans.
**Input:** Raw schema text, file path (for spans).
**Output:** `TokenStream`, `Diagnostic[]`.
**Responsibilities:**

- Tokenize identifiers, keywords, punctuation, string/number literals,
  comments, block delimiters.
- Preserve whitespace/comments in spans for better diagnostics.
- Recover from minor lexical errors to continue parsing when possible.

**Suggested contract (conceptual):**

* `scan(schema_text: Text, source_id: SourceId) -> TokenStream + Diagnostic[]`

### 5.2 Parser (+ Light Semantic Shaping)

**Purpose:** Build AST from tokens; record symbol declarations; attach spans.
**Input:** `TokenStream`.
**Output:** `AST`, `SymbolTable`, `Diagnostic[]`.
**Responsibilities:**

- Parse datasource/generator blocks, model/enum declarations, fields,
  attributes, defaults, relation directives.
- Minimal validation needed to form a well-shaped AST (e.g., structural sanity).
- Error recovery: synchronize at block boundaries to keep parsing after an error.

**Optional pluggability:** Allow replacing the parser (see §8) while keeping
the same AST/IR contracts.

**Suggested contract:**

- `parse(tokens: TokenStream) -> AST + SymbolTable + Diagnostic[]`

### 5.3 Semantic Analysis & Type Checking

**Purpose:** Validate declarations and resolve types/relations.
**Input:** `AST`, `SymbolTable`.
**Output:** `TypeGraph`, `Diagnostic[]`.
**Checks (illustrative, not exhaustive):**

- Undefined types, duplicate names, shadowing rules.
- Field type resolution: scalar vs enum vs model reference.
- Nullability, defaults, relation cardinalities, referential integrity.
- Attribute semantics (e.g., `@id`, `@unique`, `@map`, documentation comments)
  projected into TypeGraph.
- Cross-model constraints (indexes, compound keys) captured for IR if needed
  by generators.

**Suggested contract:**

* `type_check(ast: AST, symbols: SymbolTable) -> TypeGraph + Diagnostic[]`

### 5.4 IR Builder (Language-Agnostic)

**Purpose:** Convert `TypeGraph` into a stable, versioned IR suitable for all
code generators.
**Input:** `TypeGraph`.
**Output:** `IR(vN)`, `Diagnostic[]` (e.g., deprecation or normalization notes).
**Responsibilities:**

- Normalize naming (canonical names + friendly aliases), map attributes to
  neutral concepts.
- Capture documentation strings, comments, and custom annotations.
- Mark feature flags/capabilities required by the schema (e.g., compound indexes)
  so plugins can declare support.

**Suggested contract:**

* `build_ir(type_graph: TypeGraph, options: IRBuildOptions) -> IR + Diagnostic[]`

### 5.5 Pluggable Code Generation

**Purpose:** Transform IR into target-language type artifacts.
**Input:** `IR`, generator config, environment context (e.g., output dir,
  project name).
**Output:** `ArtifactBundle` (one or more artifacts), `Diagnostic[]`.
**Responsibilities:**

- Map IR scalars/enums/models to idiomatic types in the target language.
- Apply naming/style conventions (e.g., PascalCase types, snake\_case fields,
  etc.) configurable per plugin.
- Emit artifacts (files/strings) and optional post-processing hints
  (formatters, import sorters).

**Suggested contract (plugin side):**

- `initialize(context: GeneratorContext) -> GeneratorSession`
- `supports(ir_capabilities: CapabilitySet) -> SupportMatrix`
- `generate(ir: IR, config: GeneratorConfig) -> ArtifactBundle + Diagnostic[]`

---

## Plugin System Design

**Goals:**

- Safe, discoverable, versioned.
- Minimal friction to author a new plugin.

**Discovery & Registration:**

- Plugins expose a **Manifest** with: name, version, target\_language,
  supported IR versions, capabilities, config schema (keys, types, defaults).
- Resolution order: explicit CLI/config selection -> environment overrides
  -> default plugin if only one matches.

**Versioning & Compatibility:**

- IR is versioned (e.g., `ir_version: 1`).
- Plugins declare supported IR versions and feature capabilities; the host
  negotiates and warns/fails on mismatch.

**Configuration Flow (host -> plugin):**

- Inputs: target language id, formatting preferences, file layout strategy,
  naming strategy, nullability strategy, optional custom scalar mappings,
  include/exclude lists.
- Plugin returns a `SupportMatrix` describing which IR capabilities are fully
  supported, partially supported (with warnings), or unsupported (hard error).

**Security & Isolation:**

- Default: execute plugins in-process for performance.
- Option: isolated execution mode (subprocess or sandbox) for untrusted plugins;
  host restricts filesystem/network access.

**Diagnostics:**

- All plugin warnings/errors returned as structured `Diagnostic` objects with
  optional references back to IR entities (which map to schema spans).

**Artifacts:**

- `ArtifactBundle` contains: artifacts\[], suggested\_writers (e.g., write to
  single index file vs multiple files), post\_processing (e.g., "run formatter X").

---

## Optional Pluggable Parser

**When would this be useful?**

- Alternative inputs (e.g., JSON-form IR exported from another tool).
- Experimental or faster parsers.

**Contract (mirror of built-in parser):**

- `parse(input) -> AST + SymbolTable + Diagnostic[]`
- Must populate spans or provide a mapping layer so diagnostics can reference
  source locations.

**Default:** The project ships with a first-party Prisma schema parser;
pluggable parsers are an **extension point**, not a requirement.

---

## CLI, Config, and Host UX

**CLI goals:** clear, scriptable, friendly for CI.

**Primary command behaviors:**

- **Build:** read schema, run full pipeline, emit artifacts.
- **Check:** run through type checking and IR build only; no artifacts.
- **List-plugins:** enumerate available generators and their support matrices.

**Common options (descriptive, not exhaustive):**

- `--schema`: path(s) to Prisma schema(s).
- `--target`: plugin/language id.
- `--out`: output directory or stdout.
- `--config`: path to tool config (host-level) and `--plugin-config` overrides.
- `--format`: apply formatter after write if plugin suggests.
- `--emit-json`: emit IR/diagnostics as JSON (for toolchains/AI use).
- `--strict`: treat warnings as errors.

**Configuration keys (host-level):**

- default\_target, include/exclude patterns, naming conventions,
scalar mappings, formatter options, parallelism, cache directory.

**Exit codes:**

- 0 success, 1 diagnostics with errors, 2 internal/IO failures.

---

## Diagnostics & Developer Experience

- Rich messages with spans and labeled notes/hints.
- Colorized human output; JSON diagnostics for machines.
- Show related schema snippets on error.
- Suggest quick fixes (e.g., "Did you mean '@id'?") when unambiguous.
- Deterministic ordering of messages.

---

## Testing & Quality Strategy

**Test layers:**

- **Lex/Parse snapshots:** token streams and AST shapes for representative
  schemas.
- **TypeCheck suites:** valid/invalid cases for resolution, relations,
  defaults, attributes.
- **IR stability tests:** golden IR for known schemas; backwards-compat checks
  across versions.
- **Generator conformance:** for each plugin, feed canonical IR cases;
  assert artifacts and support matrices.
- **End-to-end (golden files):** schema -> artifacts; diff snapshots per target
  language.
- **Performance & memory benchmarks:** large schemas;
  measure scan/parse/typecheck/generate.

**Sample corpora:**

- Minimal, typical, and large/edge-case Prisma schemas.
- Feature toggles (compound indexes, maps, relation modes) isolated in focused
  cases.

---

## Performance, Caching, Incrementality

- **Parallelism:** run independent file parses and plugin generation in parallel.
- **Content hashing:** cache by `(schema_hash, ir_version, plugin_version,
  config_hash)`.
- **Incremental rebuilds:** reuse previous TypeGraph/IR when unaffected.
- **Streaming:** surface diagnostics early while later stages execute.

---

## Compatibility & Mapping Guidelines (for plugins)

- **Scalar mapping:** IR scalar -> target-language primitive or custom type
  (override via config).
- **Enum mapping:** preserve names with configurable casing strategies.
- **Model mapping:** model -> interface/type/class per plugin conventions.
- **Nullability:** explicit strategy per language (e.g., union with null,
  optional fields, Option types).
- **Relations:** represent foreign keys/relations as references or identifiers
  depending on plugin capability; document guarantees.
- **Docs/annotations:** propagate schema docs/comments into generated docstrings
  when feasible.

---

## Versioning Policy

- **IR:** semantic versioning; breaking IR changes bump major, additive changes
  bump minor.
- **Plugin API:** semantic versioned; host negotiates and warns/fails on
  incompatible versions.
- **Host tool:** follows semver; publishes compatibility matrix.

---

## Security & Trust

- **Sandbox mode:** optional isolated execution for third-party plugins.
- **Allowlist FS writes:** plugins can only write via host-provided writers.
- **No network access:** There is no case where we need network access.

## Glossary

- **AST:** Abstract Syntax Tree produced by the parser.
- **TypeGraph:** Typed view with resolved references and constraints.
- **IR:** Stable, language-agnostic structure consumed by code generators.
- **Artifact:** A generated output unit (e.g., a file's content plus metadata).
- **Diagnostic:** Structured message describing errors/warnings tied to source
  spans.

---

## Appendices (Guidelines for API Shapes)

The following are **suggested contracts** to guide implementation and plugin
authors. They are not code and avoid implementation specifics:

- **Scanner:** `tokenize(schema_text) -> TokenStream + Diagnostic[]`
- **Parser:** `parse(tokens) -> AST + SymbolTable + Diagnostic[]`
- **Type Checking:** `type_check(ast, symbols) -> TypeGraph + Diagnostic[]`
- **IR Build:** `build_ir(type_graph, options) -> IR + Diagnostic[]`
- **Plugin Lifecycle:** `initialize(context)`, `supports(ir_capabilities)
  -> SupportMatrix`, `generate(ir, config) -> ArtifactBundle + Diagnostic[]`
- **Artifacts:** `ArtifactBundle` contains `artifacts[]` where each artifact
  has `(name, relative_path, content, formatter_hint)`.
