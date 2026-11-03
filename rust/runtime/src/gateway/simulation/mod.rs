//! Simulated current state, source binding, execution and recovery.
mod construction;
mod state;
use state::{Current, field_inventory};
pub use state::{EffectIo, Fault, Outcome, PreparedEffect, RecoveryEvidence, Simulator};
