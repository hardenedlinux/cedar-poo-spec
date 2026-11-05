//! Durable OAuth final mediation on the shared trusted Unix checkpoint store.
use super::oauth_refresh::{RefreshDigest, RefreshEnrollment, RefreshExchange, State};
use crate::gateway::audit::reconcile_recovery;
use crate::gateway::checkpoint_store::{CheckpointStage, LockedCheckpoint};
use crate::gateway::oauth::{CurrentUse, Grant, ProofReservation};
use crate::gateway::oauth_par::VerifiedClient;
use crate::gateway::witness::{VerifiedLog, verify_view};
use crate::gateway::{
    AuditAuthority, EffectIdentity, LogSnapshot, ProviderAuditTrust, ProviderJournal, Signed,
    WitnessFrontier,
};
use cedar_poo_core::operation_identity::OperationId;
use p256::ecdsa::VerifyingKey;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Portable replica image. Trust comes from equality with the independent
/// live checkpoint, never from deserializing this value.
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DurableRevocationCheckpoint {
    version: u32,
    authority: String,
    #[serde(default)]
    writer: WriterCut,
    ledger: State,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Image {
    checkpoint: DurableRevocationCheckpoint,
    reserved: BTreeSet<ProofReservation>,
    #[serde(default)]
    effects: BTreeMap<String, RetainedEffect>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RetainedEffect {
    intent: Signed,
    anchor: Signed,
    provider_key: Vec<u8>,
    resolved: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    settled_outcome: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    recovery_origin: Option<RecoveryOrigin>,
}

/// Authority-assigned writer incarnation. Trusted configuration binds it
/// to the worker that received the handoff.
#[derive(Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct WriterCut(u64);

/// Actual final-use observations and the checkpoint retained at precheck.
pub struct DurableFinalUse<'a> {
    pub checked: &'a DurableRevocationCheckpoint,
    pub replica: &'a DurableRevocationCheckpoint,
    pub current: &'a CurrentUse,
    pub base_allowed: bool,
}

/// Actual effect and its exact independently witnessed intent.
pub struct DurableEffectUse<'a> {
    pub admission: DurableFinalUse<'a>,
    pub effect: &'a EffectIdentity,
    pub intent: &'a Signed,
    pub history: &'a LogSnapshot,
    pub trust: ProviderAuditTrust<'a>,
}

/// Durable OAuth view of an operation. Only independent evidence can
/// advance an unresolved reservation to reconciled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EffectStatus {
    Unreserved,
    Unresolved,
    Reconciled,
}

/// Detached provider evidence and the independently selected audit roots.
pub struct DurableEffectRecovery<'a> {
    pub effect: &'a EffectIdentity,
    pub journal: &'a ProviderJournal,
    pub outcomes: &'a [Signed],
    pub history: &'a LogSnapshot,
    pub trust: ProviderAuditTrust<'a>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReceiverBinding {
    pub(super) checkpoint: PathBuf,
    pub(super) scope: String,
}

#[derive(PartialEq, Eq, Serialize, Deserialize)]
enum RecoveryOrigin {
    Detached,
    Receiver(ReceiverBinding),
}

pub(super) enum RecoveryRequest {
    Detached,
    Receiver(ReceiverBinding),
    LegacyMigration(ReceiverBinding),
}

impl RetainedEffect {
    fn is_legacy_unresolved(&self) -> bool {
        self.recovery_origin.is_none() && !self.resolved && self.settled_outcome.is_none()
    }

    fn matches_origin(&self, request: &RecoveryRequest) -> bool {
        match (&self.recovery_origin, request) {
            (Some(RecoveryOrigin::Detached), RecoveryRequest::Detached) => true,
            (Some(RecoveryOrigin::Receiver(pinned)), RecoveryRequest::Receiver(binding)) => {
                pinned == binding
            }
            (Some(RecoveryOrigin::Receiver(pinned)), RecoveryRequest::LegacyMigration(binding)) => {
                self.resolved && pinned == binding
            }
            // Older settlements with an exact identity can only confirm that
            // outcome through the existing detached port.
            (None, RecoveryRequest::Detached) => self.resolved && self.settled_outcome.is_some(),
            (None, RecoveryRequest::LegacyMigration(_)) => self.is_legacy_unresolved(),
            _ => false,
        }
    }

    fn matches_recovery(
        &self,
        input: &DurableEffectRecovery<'_>,
        history: &VerifiedLog<'_>,
    ) -> Result<bool, String> {
        let prior = WitnessFrontier::from_checkpoint(&self.anchor, &input.trust.authority.log_key)?;
        history.check_frontier(&prior)?;
        Ok(
            self.provider_key == input.trust.provider_key.to_encoded_point(false).as_bytes()
                && history
                    .intent(&self.intent)
                    .is_some_and(|entry| &entry.effect == input.effect),
        )
    }
}

fn anchored_history<'a>(
    history: &'a LogSnapshot,
    authority: &AuditAuthority,
) -> Result<VerifiedLog<'a>, String> {
    let verified = verify_view(history.view(), &authority.log_key, authority.minimum_size)?;
    authority.check_history(&verified)?;
    if authority.independent_frontier.as_ref() != Some(&verified.frontier()) {
        return Err("OAuth effect lacks an exact independent witness frontier".into());
    }
    Ok(verified)
}

/// Receiver pin for the trusted OAuth checkpoint. Writer rotations retain it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReceiverAuthority {
    pub(super) directory: PathBuf,
    authority: String,
}

/// Short-lived permission constructed only inside final OAuth mediation.
pub(super) struct ReceiverAuthorization<'a> {
    authority: &'a ReceiverAuthority,
    intent: &'a Signed,
    provider_key: &'a VerifyingKey,
}

impl ReceiverAuthorization<'_> {
    pub(super) fn matches(
        &self,
        authority: Option<&ReceiverAuthority>,
        intent: &Signed,
        provider_key: &VerifyingKey,
    ) -> bool {
        authority == Some(self.authority)
            && intent == self.intent
            && provider_key == self.provider_key
    }
}

/// Trusted independent directory for one OAuth authority. Every worker and
/// writer must use the same directory and retain the lock inode across recovery.
pub struct DurableRefreshLedger<'a> {
    directory: &'a Path,
    authority: &'a str,
    writer: WriterCut,
}

impl<'a> DurableRefreshLedger<'a> {
    /// Select the independent store and authority from trusted configuration.
    pub fn new(directory: &'a Path, authority: &'a str) -> Self {
        Self {
            directory,
            authority,
            writer: WriterCut::default(),
        }
    }

    /// Reopen for the incarnation assigned by the trusted authority.
    pub fn for_writer(&self, writer: WriterCut) -> Self {
        Self { writer, ..*self }
    }

    /// Serialize an authority-approved handoff with every final effect and write.
    pub fn rotate_writer(&self) -> Result<WriterCut, String> {
        let file = LockedCheckpoint::open(self.directory)?;
        let mut image = self.read(&file)?;
        let next = WriterCut(
            self.writer
                .0
                .checked_add(1)
                .ok_or("OAuth writer cut exhausted")?,
        );
        image.checkpoint.writer = next;
        file.persist(&image)?;
        Ok(next)
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
                writer: self.writer,
                ledger: State::default(),
            },
            reserved: BTreeSet::new(),
            effects: BTreeMap::new(),
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
        if image.checkpoint.writer != self.writer {
            return Err("OAuth writer fenced".into());
        }
        file.sync_directory()?;
        Ok(image)
    }

    fn update<T>(
        &self,
        step: impl FnOnce(&mut Arc<State>) -> Result<T, String>,
    ) -> Result<T, String> {
        self.update_at(step, |_| Ok(()))
    }

    fn update_at<T>(
        &self,
        step: impl FnOnce(&mut Arc<State>) -> Result<T, String>,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<T, String> {
        let file = LockedCheckpoint::open(self.directory)?;
        let mut image = self.read(&file)?;
        let position = image.checkpoint.ledger.position;
        let mut ledger = Arc::new(image.checkpoint.ledger);
        let result = step(&mut ledger)?;
        if ledger.position != position {
            image.checkpoint.ledger = Arc::unwrap_or_clone(ledger);
            file.persist_at(&image, observe)?;
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

    #[cfg(test)]
    pub(super) fn revoke_with_crash(
        &self,
        verified: VerifiedClient<RefreshDigest>,
        crash_at: CheckpointStage,
    ) -> Result<bool, String> {
        self.revoke_observed(verified, |stage| {
            if stage == crash_at {
                Err("simulated checkpoint crash".into())
            } else {
                Ok(())
            }
        })
    }

    #[cfg(test)]
    pub(super) fn revoke_observed(
        &self,
        verified: VerifiedClient<RefreshDigest>,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<bool, String> {
        self.update_at(|ledger| State::revoke(ledger, verified), observe)
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

    fn reserve(image: &mut Image, input: DurableFinalUse<'_>) -> Result<bool, String> {
        if input.checked != &image.checkpoint
            || input.replica != &image.checkpoint
            || !image.checkpoint.ledger.contains_active(input.current)
        {
            return Ok(false);
        }
        input
            .current
            .admit_with(input.base_allowed, |key| Ok(image.reserved.insert(key)))
    }

    /// Persist the exact intent and proof reservation before the external
    /// observer. An observer error retains the intent and never permits resend.
    pub fn execute_effect(
        &self,
        input: DurableEffectUse<'_>,
        observe_effect: impl FnOnce(&EffectIdentity) -> Result<(), String>,
    ) -> Result<bool, String> {
        self.execute_effect_at(input, RecoveryOrigin::Detached, || Ok(()), observe_effect)
    }

    fn execute_effect_at(
        &self,
        input: DurableEffectUse<'_>,
        origin: RecoveryOrigin,
        after_reservation: impl FnOnce() -> Result<(), String>,
        observe_effect: impl FnOnce(&EffectIdentity) -> Result<(), String>,
    ) -> Result<bool, String> {
        let history = anchored_history(input.history, input.trust.authority)?;
        let commit = history
            .intent(input.intent)
            .ok_or("OAuth effect intent is not witnessed")?;
        let operation = &commit.effect.operation;
        if operation.is_empty()
            || &commit.effect != input.effect
            || commit.effect.audience != input.admission.current.target.audience
            || history
                .records()
                .iter()
                .filter(|entry| &entry.effect.operation == operation)
                .count()
                != 1
        {
            return Ok(false);
        }
        let file = LockedCheckpoint::open(self.directory)?;
        let mut image = self.read(&file)?;
        if image.effects.contains_key(operation) || !Self::reserve(&mut image, input.admission)? {
            return Ok(false);
        }
        image.effects.insert(
            operation.clone(),
            RetainedEffect {
                intent: input.intent.clone(),
                anchor: input.history.checkpoint.clone(),
                provider_key: input
                    .trust
                    .provider_key
                    .to_encoded_point(false)
                    .as_bytes()
                    .to_vec(),
                resolved: false,
                settled_outcome: None,
                recovery_origin: Some(origin),
            },
        );
        file.persist(&image)?;
        after_reservation()?;
        observe_effect(&commit.effect)?;
        Ok(true)
    }

    pub(super) fn receiver_authority(&self) -> Result<ReceiverAuthority, String> {
        let directory = self
            .directory
            .canonicalize()
            .map_err(|error| error.to_string())?;
        Ok(ReceiverAuthority {
            directory,
            authority: self.authority.into(),
        })
    }

    pub(super) fn bind_receiver_authority(
        &self,
        authority: &ReceiverAuthority,
        bind: impl FnOnce() -> Result<(), String>,
    ) -> Result<(), String> {
        let file = LockedCheckpoint::open(&authority.directory)?;
        self.read(&file)?;
        bind()
    }

    pub(super) fn authorize_receiver(
        &self,
        input: DurableEffectUse<'_>,
        authority: &ReceiverAuthority,
        binding: ReceiverBinding,
        after_reservation: impl FnOnce() -> Result<(), String>,
        receive: impl FnOnce(ReceiverAuthorization<'_>) -> Result<Option<Signed>, String>,
    ) -> Result<Option<Signed>, String> {
        let permission = ReceiverAuthorization {
            authority,
            intent: input.intent,
            provider_key: input.trust.provider_key,
        };
        let ledger = DurableRefreshLedger {
            directory: &authority.directory,
            authority: self.authority,
            writer: self.writer,
        };
        let mut outcome = None;
        ledger.execute_effect_at(
            input,
            RecoveryOrigin::Receiver(binding),
            after_reservation,
            |_| {
                outcome = receive(permission)?;
                Ok(())
            },
        )?;
        Ok(outcome)
    }

    /// Read status from the current writer's durable store. An unresolved
    /// operation remains reserved, including when the receiver has no receipt.
    pub fn effect_status(&self, operation: &OperationId) -> Result<EffectStatus, String> {
        let file = LockedCheckpoint::open(self.directory)?;
        let image = self.read(&file)?;
        Ok(match image.effects.get(&operation.0) {
            None => EffectStatus::Unreserved,
            Some(effect) if effect.resolved => EffectStatus::Reconciled,
            Some(_) => EffectStatus::Unresolved,
        })
    }

    /// List legacy unresolved operation IDs for evidence collection. This
    /// read does not bind a receiver or authorize a new send.
    pub fn legacy_unresolved_operations(&self) -> Result<Vec<OperationId>, String> {
        let file = LockedCheckpoint::open(self.directory)?;
        let image = self.read(&file)?;
        Ok(image
            .effects
            .into_iter()
            .filter_map(|(operation, effect)| {
                effect
                    .is_legacy_unresolved()
                    .then_some(OperationId(operation))
            })
            .collect())
    }

    /// Settle an explicitly detached effect. Managed deliveries require the
    /// independently acknowledged receiver image through its reconciliation port.
    pub fn reconcile_effect(&self, input: DurableEffectRecovery<'_>) -> Result<bool, String> {
        self.reconcile_effect_at(
            input,
            RecoveryRequest::Detached,
            |_, _| Ok(Some(())),
            |_| Ok(()),
        )
    }

    pub(super) fn reconcile_receiver_effect<G>(
        &self,
        input: DurableEffectRecovery<'_>,
        authority: &ReceiverAuthority,
        request: RecoveryRequest,
        committed: impl FnOnce(&Signed, &Signed) -> Result<Option<G>, String>,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<bool, String> {
        let ledger = DurableRefreshLedger {
            directory: &authority.directory,
            authority: self.authority,
            writer: self.writer,
        };
        ledger.reconcile_effect_at(input, request, committed, observe)
    }

    fn reconcile_effect_at<G>(
        &self,
        input: DurableEffectRecovery<'_>,
        request: RecoveryRequest,
        committed: impl FnOnce(&Signed, &Signed) -> Result<Option<G>, String>,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<bool, String> {
        let history = anchored_history(input.history, input.trust.authority)?;
        let file = LockedCheckpoint::open(self.directory)?;
        let mut image = self.read(&file)?;
        let Some(effect) = image.effects.get_mut(&input.effect.operation) else {
            return Ok(false);
        };
        if !effect.matches_origin(&request) || !effect.matches_recovery(&input, &history)? {
            return Ok(false);
        }
        let (_, outcome) = reconcile_recovery(
            input.journal,
            input.outcomes,
            &history,
            input.trust.authority,
            Some(input.trust.provider_key),
            Some(&effect.intent),
        );
        let Some(outcome) = outcome else {
            return Ok(false);
        };
        // Keep the independently verified receiver cut locked until the
        // OAuth checkpoint commits or the attempt returns.
        let Some(_receiver_guard) = committed(&effect.intent, outcome)? else {
            return Ok(false);
        };
        let identity = outcome.source_sha256()?;
        if effect.resolved {
            return Ok(effect.settled_outcome.as_ref() == Some(&identity));
        }
        if let RecoveryRequest::LegacyMigration(binding) = request {
            effect.recovery_origin = Some(RecoveryOrigin::Receiver(binding));
        }
        effect.resolved = true;
        effect.settled_outcome = Some(identity);
        file.persist_at(&image, observe)?;
        Ok(true)
    }

    /// For a synchronous observer with no recoverable external outcome,
    /// re-read the current frontier, persist any proof reservation and observe
    /// the effect under the same lock as revocation. The observer is synchronous
    /// and must never re-enter this store.
    pub fn execute_final(
        &self,
        input: DurableFinalUse<'_>,
        observe_effect: impl FnOnce(),
    ) -> Result<bool, String> {
        let file = LockedCheckpoint::open(self.directory)?;
        let mut image = self.read(&file)?;
        let prior = image.reserved.len();
        if !Self::reserve(&mut image, input)? {
            return Ok(false);
        }
        if image.reserved.len() != prior {
            file.persist(&image)?;
        }
        observe_effect();
        Ok(true)
    }
}
