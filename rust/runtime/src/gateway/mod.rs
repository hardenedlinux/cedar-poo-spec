//! Shared evidence/effect protocol, with explicit in-memory simulation.
//! Public source and audit verification require independently configured keys.
//! No production persistence, network sandbox or signer custody is provided.
mod audit;
#[cfg(unix)]
mod checkpoint_store;
mod lineage;
pub mod oauth;
pub mod oauth_code;
pub mod oauth_par;
pub mod oauth_refresh;
mod provider;
mod review;
mod simulation;
mod sources;
mod wire;
mod witness;
pub use audit::{
    AuditAuthority, IntentAuditTrust, ProviderAuditTrust, Reconciliation, reconcile,
    reconcile_intent, reconcile_provider_outcomes,
};
#[cfg(unix)]
pub use checkpoint_store::CheckpointStore;
pub use lineage::{Lineage, LineageBatch, LineageEdge, LineageState};
pub use provider::{ProviderAction, ProviderJournal, ProviderOutcome, Receipt};
pub use simulation::{
    EffectIo, Fault, LifecycleView, Outcome, PreparedEffect, PublicationTicket, RecoveryEvidence,
    ReviewSubmission, Simulator,
};
pub use sources::{FactAuthority, FactStatement};
pub use wire::{
    EffectIdentity, Envelope, FactBinding, Origin, ReviewBinding, Signed, Version, public_key,
    verify,
};
pub use witness::{Checkpoint, Commit, LogSnapshot, Witness, WitnessFrontier, verify_log};

pub use review::{
    AnalysisKind, GainApproval, PreparedPublications, PublicationDelivery, PublicationRecord,
    PublicationView, ReleaseIdentity, ReviewAuthority, ReviewRecord, ReviewTrust,
    publication_matches, verify_publications,
};
