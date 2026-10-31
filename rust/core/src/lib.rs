//! Shared policy artifacts and Host operation/authority identities.
mod artifact;
mod source_identity;
pub use artifact::{CompiledPolicyJson, SchemaSourceJson, TemplateSourceJson};
pub use source_identity::JsonSourceIdentity;
pub mod authority_consumption;
pub mod handoff;
pub mod operation_identity;

#[cfg(test)]
asp_rust::asp_rust_cargo_test_gate!(mode = deny, config = asp_rust::default_asp_rust_config());
