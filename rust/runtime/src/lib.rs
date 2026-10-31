//! Official Cedar validation, policy export and receipt replay.
mod bridge;
mod canonical;
mod entities;
mod input;
mod observation;
mod policy_codec;
mod preparation;
mod replay;
mod revision;
mod syntax;
pub use observation::ReplayMetrics;
mod schema;
mod schema_preparation;
pub use bridge::check_direct_sources;
use cedar_poo_core::{CompiledPolicyJson, TemplateSourceJson};
pub use input::{Case, Manifest, ReplayReceipt, RequestInput};
pub use policy_codec::{
    check_template_source, load_policy_set, load_template_source, render_artifacts,
    render_identified_policy_sources, render_loaded_policy_set, render_policy_source,
};
pub use replay::{
    check_manifest, replay_manifest, replay_manifest_measured, verify_replay_receipts,
};
pub use schema::{
    SchemaBoundReceipt, SchemaEvolutionBundle, SchemaOnlyRevisionReceipt, ValidatedManifest,
    render_validated_policy_sources, replay_schema_only_revision, replay_validated_manifest,
    replay_validated_manifest_measured, verify_schema_only_revision,
    verify_validated_replay_receipts,
};
pub use schema_preparation::SchemaPreparation;

#[cfg(test)]
asp_rust::asp_rust_cargo_test_gate!(mode = deny, config = asp_rust::default_asp_rust_config());
