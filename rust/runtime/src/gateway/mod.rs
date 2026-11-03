//! Shared evidence/effect protocol, with explicit in-memory simulation.
//! Public source and audit verification require independently configured keys.
//! No production persistence, network sandbox or signer custody is provided.
mod audit;
mod lineage;
mod provider;
mod simulation;
mod sources;
mod wire;
mod witness;
pub use audit::{AuditAuthority, Reconciliation, reconcile};
pub use lineage::{Lineage, LineageBatch, LineageEdge, LineageState};
pub use provider::{ProviderAction, ProviderJournal, Receipt};
pub use simulation::{EffectIo, Fault, Outcome, PreparedEffect, RecoveryEvidence, Simulator};
pub use sources::FactAuthority;
pub use wire::{
    EffectIdentity, Envelope, FactBinding, Origin, ReviewBinding, Signed, Version, public_key,
    verify,
};
pub use witness::{Checkpoint, Commit, LogSnapshot, Witness, verify_log};
