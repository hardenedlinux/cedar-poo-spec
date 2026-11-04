//! One authoritative sender image per trusted, non-rollback directory.
use super::{
    CommitReceipt, DispatchOutcome, Effect, Evidence, InMemoryDisclosureHost, Inner, Ticket,
    ValidatedDisclosurePolicy, commit_admitted, ticket_current,
};
use crate::dispatch::{DispatchBinding, ReceiverCut, atomic_write, lock, read, verify_outcome};
use cedar_poo_core::authority_consumption::{AuthorityId, AuthorityLedger};
use cedar_poo_core::operation_identity::{OperationId, OperationLedger};
use cedar_poo_runtime::gateway::Signed;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Image {
    policy: String,
    evidence: Evidence,
    authority: AuthorityLedger<Effect>,
    operations: OperationLedger<Effect>,
    audit: Vec<CommitReceipt>,
    dispatches: BTreeMap<String, DispatchBinding>,
    #[serde(default)]
    settlements: BTreeMap<String, Signed>,
}

struct DispatchHistory {
    dispatches: BTreeMap<String, DispatchBinding>,
    settlements: BTreeMap<String, Signed>,
}

/// Process-reopenable sender. File locking coordinates distinct Host handles.
/// Provision the directory and authenticate all bootstrap inputs independently.
pub struct PersistentDisclosureHost {
    directory: PathBuf,
    policy: ValidatedDisclosurePolicy,
    scope: Arc<()>,
}

impl PersistentDisclosureHost {
    pub fn open(directory: &Path, policy: &ValidatedDisclosurePolicy) -> Result<Self, String> {
        let host = Self {
            directory: directory.into(),
            policy: policy.clone(),
            scope: Arc::new(()),
        };
        let _guard = lock(directory, "sender")?;
        host.load()?;
        Ok(host)
    }

    /// Only explicit provisioning may create an image. Recovery never does.
    pub fn initialize(
        directory: &Path,
        policy: &ValidatedDisclosurePolicy,
        evidence: Evidence,
        authority: AuthorityLedger<Effect>,
    ) -> Result<(), String> {
        let _guard = lock(directory, "sender")?;
        match std::fs::symlink_metadata(directory.join("sender.json")) {
            Ok(_) => return Err("sender already initialized".into()),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error.to_string()),
        }
        atomic_write(
            directory,
            "sender",
            &Image {
                policy: policy.0.identity.clone(),
                evidence,
                authority,
                operations: OperationLedger::default(),
                audit: Vec::new(),
                dispatches: BTreeMap::new(),
                settlements: BTreeMap::new(),
            },
        )
    }

    fn load(&self) -> Result<Image, String> {
        let image: Image = read(&self.directory, "sender")?;
        if image.policy != self.policy.0.identity {
            return Err("persisted disclosure policy differs".into());
        }
        Ok(image)
    }

    fn unpack(&self, image: Image) -> (Inner, DispatchHistory) {
        let inner = Inner {
            policies: Arc::clone(&self.policy.0),
            evidence: image.evidence,
            authority: image.authority,
            operations: image.operations,
            audit: image.audit,
        };
        (
            inner,
            DispatchHistory {
                dispatches: image.dispatches,
                settlements: image.settlements,
            },
        )
    }

    pub fn prepare(&self, approval: AuthorityId, effect: Effect) -> Result<Option<Ticket>, String> {
        let _guard = lock(&self.directory, "sender")?;
        let (inner, _) = self.unpack(self.load()?);
        InMemoryDisclosureHost {
            scope: Arc::clone(&self.scope),
            inner: Mutex::new(inner),
        }
        .prepare(approval, effect)
    }

    /// A successful disk commit precedes dispatch. On an ambiguous disk error
    /// the caller must reopen the image; this method never sends on that error.
    pub fn commit_and_dispatch(
        &self,
        ticket: Ticket,
        actual: &Effect,
        cut: ReceiverCut,
        send: impl FnOnce(&DispatchBinding, &Effect) -> Result<(), String>,
    ) -> Result<Option<DispatchOutcome>, String> {
        let binding = DispatchBinding::new(actual, cut)?;
        let receipt = {
            let _guard = lock(&self.directory, "sender")?;
            let (mut inner, mut history) = self.unpack(self.load()?);
            if !Arc::ptr_eq(&self.scope, &ticket.scope)
                || history.dispatches.contains_key(&actual.operation_id.0)
                || !ticket_current(&inner, &ticket, actual)?
            {
                return Ok(None);
            }
            let receipt = commit_admitted(&mut inner, &ticket, actual)?;
            history
                .dispatches
                .insert(actual.operation_id.0.clone(), binding.clone());
            atomic_write(
                &self.directory,
                "sender",
                &Image {
                    policy: self.policy.0.identity.clone(),
                    evidence: inner.evidence,
                    authority: inner.authority,
                    operations: inner.operations,
                    audit: inner.audit,
                    dispatches: history.dispatches,
                    settlements: history.settlements,
                },
            )?;
            receipt
        };
        Ok(Some(match send(&binding, actual) {
            Ok(()) => DispatchOutcome::Confirmed(receipt),
            Err(_) => DispatchOutcome::Unknown(receipt),
        }))
    }

    pub fn audit(&self) -> Result<Vec<CommitReceipt>, String> {
        let _guard = lock(&self.directory, "sender")?;
        Ok(self.load()?.audit)
    }

    pub fn approval_used(&self, id: &AuthorityId) -> Result<Option<u64>, String> {
        let _guard = lock(&self.directory, "sender")?;
        Ok(self.load()?.authority.used(id).ok())
    }

    pub fn reconcile(
        &self,
        id: &OperationId,
        signed: &Signed,
        provider_key: &[u8],
    ) -> Result<bool, String> {
        let _guard = lock(&self.directory, "sender")?;
        let mut image = self.load()?;
        let binding = image
            .dispatches
            .get(&id.0)
            .ok_or("missing retained dispatch")?;
        let delivered = verify_outcome(binding, signed, provider_key)?;
        if let Some(retained) = image.settlements.get(&id.0) {
            if verify_outcome(binding, retained, provider_key)? != delivered {
                return Err("conflicting authenticated provider settlement".into());
            }
            // Reconfirm directory durability if a prior rename reported
            // an ambiguous synchronization error.
            crate::dispatch::sync_directory(&self.directory)?;
            return Ok(delivered);
        }
        image.settlements.insert(id.0.clone(), signed.clone());
        atomic_write(&self.directory, "sender", &image)?;
        Ok(delivered)
    }
}
