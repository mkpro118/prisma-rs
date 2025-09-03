use proc_macro::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields, parse_macro_input};

/// Derive macro for implementing `AstNode` as a leaf node (non-container).
///
/// This automatically implements `HasSpan`, `HasNodeType`, and `AstNode` with
/// `is_container() = false`.
///
/// Requires a `span` field of type `SymbolSpan`.
///
/// # Example
///
/// ```rust
/// #[derive(AstLeafNode)]
/// struct StringLit {
///     pub value: String,
///     pub span: SymbolSpan,
/// }
/// ```
#[proc_macro_derive(AstLeafNode)]
pub fn derive_ast_leaf_node(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let generics = input.generics.clone();
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    // Verify the struct has a `span` field
    let has_span_field = match &input.data {
        Data::Struct(data_struct) => match &data_struct.fields {
            Fields::Named(fields) => fields.named.iter().any(|field| {
                field.ident.as_ref().is_some_and(|ident| ident == "span")
            }),
            _ => false,
        },
        _ => false,
    };

    if !has_span_field {
        return syn::Error::new_spanned(
            &input,
            "AstLeafNode can only be derived for structs with a `span: SymbolSpan` field"
        ).to_compile_error().into();
    }

    let type_name = name.to_string();

    let expanded = quote! {
        impl #impl_generics HasSpan for #name #ty_generics #where_clause {
            fn span(&self) -> &SymbolSpan {
                &self.span
            }
        }

        impl #impl_generics HasNodeType for #name #ty_generics #where_clause {
            fn node_type(&self) -> &'static str {
                #type_name
            }
        }

        impl #impl_generics AstNode for #name #ty_generics #where_clause {}

        impl #impl_generics AstVisitable for #name #ty_generics #where_clause {}
    };

    TokenStream::from(expanded)
}

/// Derive macro for implementing `AstNode` as a container node.
///
/// This automatically implements `HasSpan`, `HasNodeType`, and `AstNode` with
/// `is_container() = true`.
///
/// Requires a `span` field of type `SymbolSpan`.
/// The `accept` method should be implemented manually for visiting children.
///
/// # Example
///
/// ```rust
/// #[derive(AstContainerNode)]
/// struct ModelDecl {
///     pub name: Ident,
///     pub members: Vec<ModelMember>,
///     pub span: SymbolSpan,
/// }
/// ```
#[proc_macro_derive(AstContainerNode)]
pub fn derive_ast_container_node(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let generics = input.generics.clone();
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    // Verify the struct has a `span` field
    let has_span_field = match &input.data {
        Data::Struct(data_struct) => match &data_struct.fields {
            Fields::Named(fields) => fields.named.iter().any(|field| {
                field.ident.as_ref().is_some_and(|ident| ident == "span")
            }),
            _ => false,
        },
        _ => false,
    };

    if !has_span_field {
        return syn::Error::new_spanned(
            &input,
            "AstContainerNode can only be derived for structs with a `span: SymbolSpan` field"
        ).to_compile_error().into();
    }

    let type_name = name.to_string();

    let expanded = quote! {
        impl #impl_generics HasSpan for #name #ty_generics #where_clause {
            fn span(&self) -> &SymbolSpan {
                &self.span
            }
        }

        impl #impl_generics HasNodeType for #name #ty_generics #where_clause {
            fn node_type(&self) -> &'static str {
                #type_name
            }
        }

        impl #impl_generics AstNode for #name #ty_generics #where_clause {
            fn is_container(&self) -> bool {
                true
            }
        }

        impl #impl_generics AstVisitable for #name #ty_generics #where_clause {}
    };

    TokenStream::from(expanded)
}

/// Derive an inherent `name()` method for an enum that returns the variant name.
///
/// For unit variants, the match arm uses `Type::Variant`.
/// For tuple variants, it uses `Type::Variant(..)`.
/// For struct variants, it uses `Type::Variant { .. }`.
///
/// # Example
///
/// ```rust
/// #[derive(EnumKindName)]
/// enum K { Unit, Tuple(u8), Struct { x: u8 } }
/// # impl K { /* name() generated */ }
/// ```
#[proc_macro_derive(EnumKindName)]
pub fn derive_enum_kind_name(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let Data::Enum(data_enum) = &input.data else {
        return syn::Error::new_spanned(
            &input,
            "EnumKindName can only be derived for enums",
        )
        .to_compile_error()
        .into();
    };

    let arms = data_enum.variants.iter().map(|v| {
        let v_ident = &v.ident;
        let v_name = v_ident.to_string();
        match &v.fields {
            Fields::Unit => quote! { #name::#v_ident => #v_name },
            Fields::Unnamed(_) => quote! { #name::#v_ident(..) => #v_name },
            Fields::Named(_) => quote! { #name::#v_ident { .. } => #v_name },
        }
    });

    let expanded = quote! {
        impl #name {
            /// Return the enum variant name.
            pub fn name(&self) -> &'static str {
                match self {
                    #( #arms, )*
                }
            }
        }
    };

    TokenStream::from(expanded)
}
