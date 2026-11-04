//! Trusted local persistence and a simulated final receiver for disclosure.
use super::Effect;
use cedar_poo_core::operation_identity::OperationId;
use cedar_poo_runtime::gateway::{Signed, public_key, verify};
use cedar_poo_runtime::gateway_source_sha256;
use serde::{Deserialize, Serialize};
use std::fs::{File, OpenOptions};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

/// Authority identity and generation obtained through the trusted control plane.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverCut {
    pub scope: String,
    pub generation: u64,
}

/// Exact admitted operation, transmitted by an authenticated Host adapter.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DispatchBinding {
    operation: String,
    effect: String,
    cut: ReceiverCut,
}

impl DispatchBinding {
    pub(crate) fn new(effect: &Effect, cut: ReceiverCut) -> Result<Self, String> {
        if effect.operation_id.0.is_empty() || cut.scope.is_empty() {
            return Err("missing operation identity or receiver scope".into());
        }
        let selection = effect
            .selection_delta
            .as_ref()
            .map(|d| (&d.before, &d.after));
        let digest = gateway_source_sha256(&(
            "cedar-poo/disclosure-effect/v1",
            &effect.operation_id.0,
            &effect.sources,
            &effect.destination,
            &effect.purpose,
            &effect.channel,
            &effect.recipients,
            &effect.payload_digest,
            &effect.candidate_ids,
            selection,
        ))?;
        Ok(Self {
            operation: effect.operation_id.0.clone(),
            effect: digest,
            cut,
        })
    }
}

/// Trusted sender journal and independently obtained receiver cut.
pub struct RecoverableDispatch<'a> {
    pub journal: &'a DispatchJournal<'a>,
    pub receiver_cut: ReceiverCut,
}

/// Provider evidence uses a dedicated signing root and an exact dispatch binding.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DisclosureOutcome {
    pub domain: String,
    pub binding: DispatchBinding,
    pub delivered: bool,
}

impl DisclosureOutcome {
    pub const DOMAIN: &str = "cedar-poo/disclosure-outcome/v1";
}

/// One trusted, non-rollback directory per workflow authority. Records are
/// immutable. A torn or unreadable reservation cannot authorize another send.
pub struct DispatchJournal<'a> {
    directory: &'a Path,
}

impl<'a> DispatchJournal<'a> {
    pub fn new(directory: &'a Path) -> Self {
        Self { directory }
    }

    fn path(&self, operation: &str) -> Result<PathBuf, String> {
        Ok(self.directory.join(gateway_source_sha256(&operation)?))
    }

    pub(crate) fn reserve(&self, binding: &DispatchBinding) -> Result<bool, String> {
        let path = self.path(&binding.operation)?;
        let mut file = match OpenOptions::new().write(true).create_new(true).open(path) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => return Ok(false),
            Err(error) => return Err(error.to_string()),
        };
        serde_json::to_writer(&mut file, binding).map_err(|e| e.to_string())?;
        file.sync_all().map_err(|e| e.to_string())?;
        File::open(self.directory)
            .and_then(|dir| dir.sync_all())
            .map_err(|e| e.to_string())?;
        Ok(true)
    }

    /// Read independent signed evidence without reopening dispatch eligibility.
    pub fn reconcile(
        &self,
        operation: &OperationId,
        signed: &Signed,
        configured_provider_key: &[u8],
    ) -> Result<bool, String> {
        let file = File::open(self.path(&operation.0)?).map_err(|e| e.to_string())?;
        let reserved: DispatchBinding = serde_json::from_reader(file).map_err(|e| e.to_string())?;
        let outcome: DisclosureOutcome = verify(signed, &public_key(configured_provider_key)?)?;
        if reserved.operation != operation.0
            || outcome.domain != DisclosureOutcome::DOMAIN
            || outcome.binding != reserved
        {
            return Err("provider outcome does not match the retained dispatch".into());
        }
        Ok(outcome.delivered)
    }
}

/// Receiver control writers and actual application share the deciding lock.
/// Real transports must authenticate the Host before calling this boundary.
pub struct DisclosureReceiver {
    current: Mutex<ReceiverCut>,
}

impl DisclosureReceiver {
    pub fn new(current: ReceiverCut) -> Self {
        Self {
            current: Mutex::new(current),
        }
    }

    pub fn advance(&self, next: ReceiverCut) -> Result<(), String> {
        let mut current = self.current.lock().map_err(|_| "receiver lock poisoned")?;
        if current.scope != next.scope || next.generation <= current.generation {
            return Err("receiver cut regressed or changed scope".into());
        }
        *current = next;
        Ok(())
    }

    pub fn receive<T>(
        &self,
        journal: &DispatchJournal<'_>,
        request: &DispatchBinding,
        actual: &Effect,
        apply: impl FnOnce(&Effect) -> Result<T, String>,
    ) -> Result<Option<T>, String> {
        let current = self.current.lock().map_err(|_| "receiver lock poisoned")?;
        if request.cut != *current
            || DispatchBinding::new(actual, current.clone())? != *request
            || !journal.reserve(request)?
        {
            return Ok(None);
        }
        apply(actual).map(Some)
    }
}
