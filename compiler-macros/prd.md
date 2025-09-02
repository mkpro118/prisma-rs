# Simple Builder Proc-Macro PRD

## 1. Objective

To provide a simple and ergonomic solution for creating builder patterns in Rust. This proc-macro will automate the generation of a basic builder, reducing boilerplate code for simple use cases.

## 2. Background

The builder pattern is a useful way to construct complex objects. However, writing the builder struct and its methods can be tedious. This proc-macro automates the creation of a simple builder.

## 3. User Persona

This tool is for Rust developers who want a quick and easy way to create a builder for their structs without the complexity of a full type-state implementation.

## 4. API Definition

The public API will consist of a single derive macro:

```rust
use simple_builder::SimpleBuilder;

#[derive(SimpleBuilder, Default)]
#[builder_name = "MyCustomBuilderName"] // Optional: to rename the builder struct
pub struct MyStruct {
    // ... fields
}
```

-   `#[derive(SimpleBuilder)]`: The main entry point. It will trigger the builder generation.
-   `#[builder_name = "..."]` (optional attribute): Allows the user to specify a custom name for the generated builder struct. If not provided, it will default to `[StructName]Builder`.

### Constraints

-   The target struct **must** implement the `Default` trait.

## 5. Requirements & Features

### 5.1. "With Defaults" Builder Logic

The builder will follow a "with defaults" strategy. This means:

-   The `build()` method can be called at any time.
-   If a field has been set using its `with_...` method, the builder will use that value.
-   If a field has not been set, the builder will use the value from the struct's `Default` implementation.

### 5.2. Generated Code

The macro will generate:

1.  A public `...Builder` struct with `Option` fields.
2.  A `new()` method to create an empty builder.
3.  A `with_<field_name>()` method for each field in the target struct.
4.  A `build()` method that constructs the target struct, intelligently combining user-provided values with default values.

## 6. Acceptance Criteria

To consider this feature complete and correct, the following criteria must be met:

1.  **Compilation:** A struct decorated with `#[derive(SimpleBuilder, Default)]` must compile successfully.
2.  **Builder Generation:** The corresponding `...Builder` struct must be generated and be publicly accessible.
3.  **`new()` Method:** The `...Builder::new()` method must exist and return a new builder instance.
4.  **`with_...` Methods:** Each field in the target struct must have a corresponding `with_<field_name>()` method on the builder.
5.  **`build()` Method:** The `build()` method must be callable on the builder at any time.
6.  **Correctness (Set Fields):** When a field is set via its `with_...` method, the `build()` method must produce a struct with that exact value for that field.
7.  **Correctness (Unset Fields):** When a field is not set, the `build()` method must produce a struct where that field has the value from the `Default` implementation.

## 7. Out of Scope (Future Work)

-   **Type-State Builder:** A more advanced builder that uses the type-state pattern to enforce compile-time correctness.
-   **Generic Structs:** Support for structs with generic parameters.
-   **Required Fields:** An attribute to mark certain fields as required.
-   **Validation:** Adding validation logic to the `build()` method.
