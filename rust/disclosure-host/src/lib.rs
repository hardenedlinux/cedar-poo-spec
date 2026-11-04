//! In-memory Host reference for a tool-using language-model disclosure effect.
//! Authenticated inputs and durable storage remain the deploying Host's duty.

#[cfg(unix)]
mod dispatch;
#[cfg(unix)]
pub use dispatch::{DisclosureOutcome, DisclosureReceiver, DispatchBinding, ReceiverCut};
mod host;
#[cfg(unix)]
pub use host::persistent::PersistentDisclosureHost;
pub use host::{
    CommitReceipt, DispatchOutcome, Effect, Evidence, Grant, InMemoryDisclosureHost,
    RecipientGrant, Ticket, ValidatedDisclosurePolicy,
};

#[cfg(test)]
asp_rust::asp_rust_cargo_test_gate!(mode = deny, config = asp_rust::default_asp_rust_config());
