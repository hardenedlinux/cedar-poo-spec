//! Shared policy artifacts and Host operation/authority identities.
mod artifact;
pub use artifact::{CompiledPolicyJson, TemplateSourceJson};
pub mod authority_consumption;
pub mod handoff;
pub mod operation_identity;

#[cfg(test)]
asp_rust::asp_rust_cargo_test_gate!(mode = deny, config = asp_rust::default_asp_rust_config());
