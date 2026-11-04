//! Durable OAuth final mediation on the shared trusted Unix checkpoint store.
use super::oauth_refresh::{RefreshDigest, RefreshEnrollment, RefreshExchange, State};
use crate::gateway::checkpoint_store::LockedCheckpoint;
use crate::gateway::oauth::{CurrentUse, Grant, ProofReservation};
use crate::gateway::oauth_par::VerifiedClient;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Arc;

/// Portable replica image. Trust comes from equality with the independent
/// live checkpoint, never from deserializing this value.
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DurableRevocationCheckpoint {
    version: u32,
    authority: String,
    ledger: State,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Image {
    checkpoint: DurableRevocationCheckpoint,
    reserved: BTreeSet<ProofReservation>,
}

/// Actual final-use observations and the checkpoint retained at precheck.
pub struct DurableFinalUse<'a> {
    pub checked: &'a DurableRevocationCheckpoint,
    pub replica: &'a DurableRevocationCheckpoint,
    pub current: &'a CurrentUse,
    pub base_allowed: bool,
}

/// Trusted independent directory for one OAuth authority. Every worker and
/// writer must use the same directory and retain the lock inode across recovery.
pub struct DurableRefreshLedger<'a> {
    directory: &'a Path,
    authority: &'a str,
}

impl<'a> DurableRefreshLedger<'a> {
    /// Select the independent store and authority from trusted configuration.
    pub fn new(directory: &'a Path, authority: &'a str) -> Self {
        Self {
            directory,
            authority,
        }
    }

    /// Explicit empty bootstrap. Recovery never bootstraps from replica data.
    pub fn initialize(&self) -> Result<(), String> {
        if self.authority.is_empty() {
            return Err("missing OAuth checkpoint authority".into());
        }
        LockedCheckpoint::open(self.directory)?.initialize(&Image {
            checkpoint: DurableRevocationCheckpoint {
                version: 1,
                authority: self.authority.into(),
                ledger: State::default(),
            },
            reserved: BTreeSet::new(),
        })
    }

    fn read(&self, file: &LockedCheckpoint<'_>) -> Result<Image, String> {
        let image: Image = file.read()?;
        if self.authority.is_empty()
            || image.checkpoint.authority != self.authority
            || image.checkpoint.version != 1
        {
            return Err("wrong OAuth checkpoint authority or version".into());
        }
        file.sync_directory()?;
        Ok(image)
    }

    fn update<T>(
        &self,
        step: impl FnOnce(&mut Arc<State>) -> Result<T, String>,
    ) -> Result<T, String> {
        let file = LockedCheckpoint::open(self.directory)?;
        let mut image = self.read(&file)?;
        let position = image.checkpoint.ledger.position;
        let mut ledger = Arc::new(image.checkpoint.ledger);
        let result = step(&mut ledger)?;
        if ledger.position != position {
            image.checkpoint.ledger = Arc::unwrap_or_clone(ledger);
            file.persist(&image)?;
        }
        Ok(result)
    }

    /// Enroll a fresh refresh family under the independent writer lock.
    pub fn enroll(&self, input: RefreshEnrollment) -> Result<bool, String> {
        self.update(|ledger| State::enroll(ledger, input))
    }

    /// Refresh against current persisted state and acknowledge after sync.
    pub fn refresh(&self, input: RefreshExchange) -> Result<Option<Grant>, String> {
        self.update(|ledger| State::refresh(ledger, input))
    }

    /// Revoke the family and acknowledge only after the updated image is durable.
    pub fn revoke(&self, verified: VerifiedClient<RefreshDigest>) -> Result<bool, String> {
        self.update(|ledger| State::revoke(ledger, verified))
    }

    /// Read the independently retained committed checkpoint.
    pub fn checkpoint(&self) -> Result<DurableRevocationCheckpoint, String> {
        let file = LockedCheckpoint::open(self.directory)?;
        Ok(self.read(&file)?.checkpoint)
    }

    /// Verify recovery against the independently retained image.
    pub fn recover(&self, replica: &DurableRevocationCheckpoint) -> Result<bool, String> {
        Ok(self.checkpoint()? == *replica)
    }

    /// Re-read the current frontier, persist any proof reservation and observe
    /// the effect under the same lock as revocation. The observer is synchronous
    /// and must never re-enter this store.
    pub fn execute_final(
        &self,
        input: DurableFinalUse<'_>,
        observe_effect: impl FnOnce(),
    ) -> Result<bool, String> {
        let file = LockedCheckpoint::open(self.directory)?;
        let mut image = self.read(&file)?;
        if input.checked != &image.checkpoint
            || input.replica != &image.checkpoint
            || !image.checkpoint.ledger.contains_active(input.current)
        {
            return Ok(false);
        }
        let prior = image.reserved.len();
        if !input
            .current
            .admit_with(input.base_allowed, |key| Ok(image.reserved.insert(key)))?
        {
            return Ok(false);
        }
        if image.reserved.len() != prior {
            file.persist(&image)?;
        }
        observe_effect();
        Ok(true)
    }
}
