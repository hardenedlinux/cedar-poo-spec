//! Official Cedar validation, policy export and receipt replay.
mod bridge;
mod observation;
mod replay;
pub use observation::ReplayMetrics;
mod schema;
pub use bridge::{
    Case, Manifest, ReplayReceipt, RequestInput, check_direct_sources, check_template_source,
    load_policy_set, load_template_source, render_artifacts, render_identified_policy_sources,
    render_loaded_policy_set, render_policy_source,
};
use cedar_poo_core::{CompiledPolicyJson, TemplateSourceJson};
pub use replay::{
    check_manifest, replay_manifest, replay_manifest_measured, verify_replay_receipts,
};
pub use schema::{
    SchemaBoundReceipt, SchemaEvolutionBundle, SchemaOnlyRevisionReceipt, ValidatedManifest,
    render_validated_policy_sources, replay_schema_only_revision, replay_validated_manifest,
    replay_validated_manifest_measured, verify_schema_only_revision,
    verify_validated_replay_receipts,
};

#[cfg(test)]
asp_rust::asp_rust_cargo_test_gate!(mode = deny, config = asp_rust::default_asp_rust_config());
