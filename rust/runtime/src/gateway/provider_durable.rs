//! Receiver-owned cut, operation reservation, and signed simulated effect.
use super::checkpoint_store::{CheckpointStage, LockedCheckpoint};
use super::oauth_refresh_durable::{
    DurableEffectRecovery, DurableEffectUse, DurableRefreshLedger, ReceiverAuthority,
    ReceiverAuthorization, RecoveryRequest,
};
use super::provider::ProviderRequest;
pub use super::receipt_identity::LegacyReceiverTrust;
use super::receipt_identity::ReceiptAuthority as ReceiverBinding;
use super::wire::sign;
use super::{
    EffectIdentity, FactBinding, ProviderAction, ProviderJournal, Signed, Version, verify,
};
pub use cedar_poo_core::operation_identity::ReceiverCut;
use cedar_poo_core::operation_identity::{OperationId, OperationLedger};
use p256::ecdsa::{SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

const VERSION: Version = Version { major: 1, minor: 0 };
const DISPATCH_DOMAIN: &str = "cedar-poo/provider-dispatch";

/// Exact witnessed intent authorized for a receiver cut and observed route.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverDispatch {
    version: Version,
    domain: String,
    cut: ReceiverCut,
    channel: String,
    intent: Signed,
}

impl ReceiverDispatch {
    /// Sign at the trusted dispatch boundary, after selecting the receiver cut.
    pub fn sign(
        cut: ReceiverCut,
        channel: &str,
        intent: &Signed,
        sender: &SigningKey,
    ) -> Result<Signed, String> {
        sign(
            &Self {
                version: VERSION,
                domain: DISPATCH_DOMAIN.into(),
                cut,
                channel: channel.into(),
                intent: intent.clone(),
            },
            sender,
        )
    }
}

/// The completed prefix of a migration attempt. Each confirmed item is
/// durable. A stopped item may have committed before its acknowledgment failed.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct LegacyMigrationReport {
    pub confirmed: Vec<OperationId>,
    pub pending: Vec<OperationId>,
    pub stopped: Option<LegacyMigrationStop>,
}

/// First operational failure. Resume from the durable OAuth image.
#[derive(Debug, PartialEq, Eq)]
pub struct LegacyMigrationStop {
    pub operation: OperationId,
    pub error: String,
}

/// Independently configured receiver scope and signing roots.
pub struct ReceiverTrust<'a> {
    pub scope: &'a str,
    pub sender: &'a VerifyingKey,
    pub witness: &'a VerifyingKey,
    pub provider: &'a SigningKey,
}

/// Actual receiver-side observation paired with the authenticated dispatch.
pub struct ReceiverDelivery<'a> {
    pub authorization: &'a Signed,
    pub channel: &'a str,
    pub effect: &'a EffectIdentity,
    pub bindings: &'a [FactBinding],
    pub facts: &'a [Signed],
    pub publications: &'a [Signed],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Delivered {
    authorization: Signed,
    action: ProviderAction,
    outcome: Signed,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Image {
    version: Version,
    cut: ReceiverCut,
    keys: [Vec<u8>; 3],
    #[serde(default)]
    managed: bool,
    operations: OperationLedger<Delivered>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Handoff {
    predecessor: String,
    cut: ReceiverCut,
}

/// Independently acknowledged placement and full receiver image identity.
/// A promotion compares this captured value with the live checkpoint.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverCheckpoint {
    active: PathBuf,
    cut: ReceiverCut,
    digest: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    handoff: Option<Handoff>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    oauth: Option<ReceiverAuthority>,
}

impl ReceiverCheckpoint {
    fn image_digest(image: &Image) -> Result<String, String> {
        crate::json_sha256(&("cedar-poo/receiver-failover/v1", image))
    }

    fn for_image(active: &Path, image: &Image) -> Result<Self, String> {
        Ok(Self {
            active: active.into(),
            cut: image.cut.clone(),
            digest: Self::image_digest(image)?,
            handoff: None,
            oauth: None,
        })
    }

    fn matches(&self, image: &Image) -> Result<bool, String> {
        Ok(self.cut == image.cut && self.digest == Self::image_digest(image)?)
    }

    fn identity(&self) -> Result<String, String> {
        crate::json_sha256(&("cedar-poo/receiver-checkpoint/v1", self))
    }
}

struct Placement {
    replica: PathBuf,
    checkpoint: PathBuf,
}

struct LockedReceiver<'a> {
    replica: LockedCheckpoint<'a>,
    checkpoint: Option<LockedCheckpoint<'a>>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ManagedDeliveryStage {
    OAuthReserved,
    Receiver(CheckpointStage),
}

/// Detached evidence read from the receiver without applying an effect.
pub struct ReceiverEvidence {
    pub journal: ProviderJournal,
    pub outcome: Signed,
}

/// Simulated provider whose operation and signed result are one committed
/// record. The trusted receiver directory stays outside replica rollback.
pub struct DurableReceiver<'a> {
    directory: &'a Path,
    trust: ReceiverTrust<'a>,
    placement: Option<Placement>,
}

impl<'a> DurableReceiver<'a> {
    /// Select the independent receiver directory and its configured roots.
    pub fn new(directory: &'a Path, trust: ReceiverTrust<'a>) -> Self {
        Self {
            directory,
            trust,
            placement: None,
        }
    }

    /// Configure a replica and a separate, independently trusted checkpoint.
    /// Every managed writer must use the same checkpoint directory.
    pub fn managed(
        directory: &'a Path,
        checkpoint: &Path,
        trust: ReceiverTrust<'a>,
    ) -> Result<Self, String> {
        let replica = directory
            .canonicalize()
            .map_err(|error| error.to_string())?;
        let checkpoint = checkpoint
            .canonicalize()
            .map_err(|error| error.to_string())?;
        if replica == checkpoint {
            return Err("receiver replica and independent checkpoint share a directory".into());
        }
        Ok(Self {
            directory,
            trust,
            placement: Some(Placement {
                replica,
                checkpoint,
            }),
        })
    }

    fn lock(&self) -> Result<LockedReceiver<'_>, String> {
        let checkpoint = self
            .placement
            .as_ref()
            .map(|placement| LockedCheckpoint::open(&placement.checkpoint))
            .transpose()?;
        let replica = self
            .placement
            .as_ref()
            .map_or(self.directory, |placement| placement.replica.as_path());
        Ok(LockedReceiver {
            replica: LockedCheckpoint::open(replica)?,
            checkpoint,
        })
    }

    fn keys(&self) -> [Vec<u8>; 3] {
        [
            self.trust.sender,
            self.trust.witness,
            self.trust.provider.verifying_key(),
        ]
        .map(|key| key.to_encoded_point(false).as_bytes().to_vec())
    }

    /// Explicit bootstrap. Reopening never replaces missing committed state.
    pub fn initialize(&self) -> Result<(), String> {
        if self.trust.scope.is_empty() {
            return Err("missing receiver scope".into());
        }
        let files = self.lock()?;
        let image = Image {
            version: VERSION,
            cut: ReceiverCut {
                scope: self.trust.scope.into(),
                generation: 0,
            },
            keys: self.keys(),
            managed: self.placement.is_some(),
            operations: OperationLedger::default(),
        };
        if let Some(checkpoint) = &files.checkpoint {
            checkpoint.ensure_uninitialized()?;
        }
        files.replica.initialize(&image)?;
        if let (Some(checkpoint), Some(placement)) = (&files.checkpoint, &self.placement) {
            checkpoint.initialize(&ReceiverCheckpoint::for_image(&placement.replica, &image)?)?;
        }
        Ok(())
    }

    fn read(&self, files: &LockedReceiver<'_>) -> Result<Image, String> {
        let image: Image = files.replica.read()?;
        if self.trust.scope.is_empty()
            || image.version != VERSION
            || image.cut.scope != self.trust.scope
            || image.keys != self.keys()
            || image.managed != self.placement.is_some()
        {
            return Err("receiver scope, version, roots or custody mode changed".into());
        }
        files.replica.sync_directory()?;
        Ok(image)
    }

    fn qualified(
        &self,
        files: &LockedReceiver<'_>,
    ) -> Result<(Image, Option<ReceiverCheckpoint>), String> {
        let image = self.read(files)?;
        let checkpoint = files
            .checkpoint
            .as_ref()
            .map(|file| {
                let checkpoint: ReceiverCheckpoint = file.read()?;
                if !checkpoint.matches(&image)? {
                    return Err("receiver replica differs from the independent checkpoint".into());
                }
                file.sync_directory()?;
                Ok::<_, String>(checkpoint)
            })
            .transpose()?;
        Ok((image, checkpoint))
    }

    fn current(
        &self,
        files: &LockedReceiver<'_>,
    ) -> Result<(Image, Option<ReceiverCheckpoint>), String> {
        let (image, checkpoint) = self.qualified(files)?;
        if let (Some(checkpoint), Some(placement)) = (&checkpoint, &self.placement)
            && checkpoint.active != placement.replica
        {
            return Err("receiver replica has not been promoted".into());
        }
        Ok((image, checkpoint))
    }

    fn persist(
        &self,
        files: &LockedReceiver<'_>,
        image: &Image,
        checkpoint: Option<ReceiverCheckpoint>,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<(), String> {
        if let Some(file) = &files.checkpoint {
            let mut next = checkpoint.ok_or("missing independent receiver checkpoint")?;
            next.cut = image.cut.clone();
            next.digest = ReceiverCheckpoint::image_digest(image)?;
            files.replica.persist(image)?;
            file.persist_at(&next, observe)
        } else {
            files.replica.persist_at(image, observe)
        }
    }

    fn receiver_binding(&self, directory: &Path) -> Result<ReceiverBinding, String> {
        let placement = self
            .placement
            .as_ref()
            .ok_or("OAuth delivery requires a managed receiver")?;
        if directory == placement.replica || directory == placement.checkpoint {
            return Err("OAuth and receiver checkpoints must use separate directories".into());
        }
        Ok(ReceiverBinding {
            checkpoint: placement.checkpoint.clone(),
            scope: self.trust.scope.into(),
        })
    }

    fn bind_authority(&self, authority: &ReceiverAuthority) -> Result<(), String> {
        let files = self.lock()?;
        let (_, checkpoint) = self.current(&files)?;
        let file = files
            .checkpoint
            .as_ref()
            .ok_or("receiver has no independent checkpoint")?;
        let mut checkpoint = checkpoint.ok_or("missing independent receiver checkpoint")?;
        match &checkpoint.oauth {
            Some(bound) if bound == authority => Ok(()),
            Some(_) => Err("receiver already binds a different OAuth authority".into()),
            None => {
                checkpoint.oauth = Some(authority.clone());
                file.persist(&checkpoint)
            }
        }
    }

    /// Read the independent authority without relying on the primary replica.
    /// Promotion still requires a candidate with the exact acknowledged image.
    pub fn acknowledged_checkpoint(&self) -> Result<ReceiverCheckpoint, String> {
        let placement = self
            .placement
            .as_ref()
            .ok_or("receiver has no independent checkpoint")?;
        let file = LockedCheckpoint::open(&placement.checkpoint)?;
        let checkpoint: ReceiverCheckpoint = file.read()?;
        if self.trust.scope.is_empty() || checkpoint.cut.scope != self.trust.scope {
            return Err("receiver checkpoint scope changed".into());
        }
        file.sync_directory()?;
        Ok(checkpoint)
    }

    /// Compare and advance the expected checkpoint while holding the shared
    /// lock. A candidate cannot silently rebase a stale promotion request.
    pub fn promote(&self, expected: &ReceiverCheckpoint) -> Result<ReceiverCut, String> {
        self.promote_at(expected, |_| Ok(()))
    }

    fn promote_at(
        &self,
        expected: &ReceiverCheckpoint,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<ReceiverCut, String> {
        let placement = self
            .placement
            .as_ref()
            .ok_or("receiver has no independent checkpoint")?;
        let files = self.lock()?;
        let (mut image, checkpoint) = self.qualified(&files)?;
        let mut checkpoint = checkpoint.ok_or("missing independent receiver checkpoint")?;
        if &checkpoint != expected {
            return Err("receiver promotion checkpoint changed".into());
        }
        if checkpoint.active == placement.replica {
            return Err("receiver replica is already active".into());
        }
        image.cut.generation = image
            .cut
            .generation
            .checked_add(1)
            .ok_or("receiver cut exhausted")?;
        checkpoint.active = placement.replica.clone();
        checkpoint.handoff = Some(Handoff {
            predecessor: expected.identity()?,
            cut: image.cut.clone(),
        });
        self.persist(&files, &image, Some(checkpoint), observe)?;
        Ok(image.cut)
    }

    /// Recover the active placement's committed handoff without advancing or
    /// emitting again. Ordinary writes retain it until another promotion wins.
    pub fn recover_promotion(
        &self,
        expected: &ReceiverCheckpoint,
    ) -> Result<Option<ReceiverCut>, String> {
        let (_, checkpoint) = self.current(&self.lock()?)?;
        let predecessor = expected.identity()?;
        Ok(checkpoint
            .and_then(|pin| pin.handoff)
            .filter(|handoff| handoff.predecessor == predecessor)
            .map(|handoff| handoff.cut))
    }

    /// Read the current independent receiver cut, including after restart.
    pub fn cut(&self) -> Result<ReceiverCut, String> {
        Ok(self.current(&self.lock()?)?.0.cut)
    }

    /// Advance only the expected cut under the same lock as delivery.
    pub fn advance(&self, expected: &ReceiverCut) -> Result<ReceiverCut, String> {
        self.advance_at(expected, |_| Ok(()))
    }

    fn advance_at(
        &self,
        expected: &ReceiverCut,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<ReceiverCut, String> {
        let files = self.lock()?;
        let (mut image, checkpoint) = self.current(&files)?;
        if &image.cut != expected {
            return Err("stale receiver cut".into());
        }
        image.cut.generation = image
            .cut
            .generation
            .checked_add(1)
            .ok_or("receiver cut exhausted")?;
        self.persist(&files, &image, checkpoint, observe)?;
        Ok(image.cut)
    }

    /// Bind an active receiver to its independent OAuth authority. Existing
    /// pins must be bound explicitly before the first managed delivery.
    pub fn bind_oauth(&self, oauth: &DurableRefreshLedger<'_>) -> Result<(), String> {
        let authority = oauth.receiver_authority()?;
        self.receiver_binding(&authority.directory)?;
        oauth.bind_receiver_authority(&authority, || self.bind_authority(&authority))
    }

    /// Commit a managed simulated effect with current OAuth and receiver state.
    /// Lock order is OAuth authority, receiver authority, then receiver replica.
    pub fn receive_oauth(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        input: DurableEffectUse<'_>,
        delivery: ReceiverDelivery<'_>,
    ) -> Result<Option<Signed>, String> {
        self.receive_oauth_at(oauth, input, delivery, |_| Ok(()))
    }

    fn receive_oauth_at(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        input: DurableEffectUse<'_>,
        delivery: ReceiverDelivery<'_>,
        observe: impl Fn(ManagedDeliveryStage) -> Result<(), String>,
    ) -> Result<Option<Signed>, String> {
        if input.effect != delivery.effect {
            return Ok(None);
        }
        let authority = oauth.receiver_authority()?;
        let binding = self.receiver_binding(&authority.directory)?;
        oauth.authorize_receiver(
            input,
            &authority,
            binding,
            || observe(ManagedDeliveryStage::OAuthReserved),
            |permission| {
                self.receive_at(delivery, Some(permission), |stage| {
                    observe(ManagedDeliveryStage::Receiver(stage))
                })
            },
        )
    }

    /// Apply the simulated effect and persist its signed outcome atomically.
    pub fn receive(&self, input: ReceiverDelivery<'_>) -> Result<Option<Signed>, String> {
        self.receive_at(input, None, |_| Ok(()))
    }

    fn receive_at(
        &self,
        input: ReceiverDelivery<'_>,
        permission: Option<ReceiverAuthorization<'_>>,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<Option<Signed>, String> {
        let files = self.lock()?;
        let (mut image, checkpoint) = self.current(&files)?;
        let dispatch: ReceiverDispatch = verify(input.authorization, self.trust.sender)?;
        if let Some(pin) = &checkpoint {
            let permission =
                permission.ok_or("managed receiver requires current OAuth authorization")?;
            if !permission.matches(
                pin.oauth.as_ref(),
                &dispatch.intent,
                self.trust.provider.verifying_key(),
            ) {
                return Ok(None);
            }
        }
        let id = OperationId(input.effect.operation.clone());
        if dispatch.version != VERSION
            || dispatch.domain != DISPATCH_DOMAIN
            || dispatch.cut != image.cut
            || dispatch.channel.is_empty()
            || dispatch.channel != input.channel
            || id.0.is_empty()
            || image.operations.admitted(&id).is_some()
        {
            return Ok(None);
        }
        let request = ProviderRequest {
            effect: input.effect,
            commit: &dispatch.intent,
            log_key: self.trust.witness,
            bindings: input.bindings,
            facts: input.facts,
            publications: input.publications,
        };
        request.validate()?;
        let action = ProviderAction {
            effect: input.effect.clone(),
            result: format!("provider-{}", id.0),
        };
        let outcome = request.sign_outcome(action.clone(), self.trust.provider)?;
        image
            .operations
            .admit(
                &id,
                &Delivered {
                    authorization: input.authorization.clone(),
                    action,
                    outcome: outcome.clone(),
                },
            )
            .map_err(|_| "receiver operation already reserved")?;
        self.persist(&files, &image, checkpoint, observe)?;
        Ok(Some(outcome))
    }

    /// Reconcile a managed effect against the independently acknowledged
    /// receiver image and the OAuth reservation's pinned receiver authority.
    pub fn reconcile_oauth(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        input: DurableEffectRecovery<'_>,
    ) -> Result<bool, String> {
        self.reconcile_oauth_at(oauth, input, None, |_| Ok(()))
    }

    /// Bind and settle an originless unresolved operation in one OAuth write.
    /// The original receiver authority must come from trusted configuration.
    /// A retry of the exact committed receipt is a read-only confirmation.
    pub fn migrate_legacy_oauth(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        input: DurableEffectRecovery<'_>,
        trusted: &LegacyReceiverTrust,
    ) -> Result<bool, String> {
        self.reconcile_oauth_at(oauth, input, Some(trusted), |_| Ok(()))
    }

    /// Attempt a batch under one trusted receiver configuration. Each item
    /// uses the single-operation commit. Resubmit the original inputs after
    /// interruption to confirm the committed prefix and continue safely.
    pub fn migrate_legacy_oauth_batch<'e>(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        inputs: impl IntoIterator<Item = DurableEffectRecovery<'e>>,
        trusted: &LegacyReceiverTrust,
    ) -> LegacyMigrationReport {
        self.migrate_legacy_oauth_batch_at(oauth, inputs, trusted, |_, _| Ok(()))
    }

    pub(super) fn migrate_legacy_oauth_batch_at<'e>(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        inputs: impl IntoIterator<Item = DurableEffectRecovery<'e>>,
        trusted: &LegacyReceiverTrust,
        observe: impl FnMut(&OperationId, CheckpointStage) -> Result<(), String>,
    ) -> LegacyMigrationReport {
        self.migrate_oauth_batch_at(oauth, inputs, trusted, false, observe)
    }

    /// Explicitly backfill settled legacy records using the current independent
    /// receiver, original intent, retained outcome digest and pinned audit roots.
    pub fn migrate_settled_oauth_mappings<'e>(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        inputs: impl IntoIterator<Item = DurableEffectRecovery<'e>>,
        trusted: &LegacyReceiverTrust,
    ) -> LegacyMigrationReport {
        self.migrate_settled_oauth_mappings_at(oauth, inputs, trusted, |_, _| Ok(()))
    }

    pub(super) fn migrate_settled_oauth_mappings_at<'e>(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        inputs: impl IntoIterator<Item = DurableEffectRecovery<'e>>,
        trusted: &LegacyReceiverTrust,
        observe: impl FnMut(&OperationId, CheckpointStage) -> Result<(), String>,
    ) -> LegacyMigrationReport {
        self.migrate_oauth_batch_at(oauth, inputs, trusted, true, observe)
    }

    fn migrate_oauth_batch_at<'e>(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        inputs: impl IntoIterator<Item = DurableEffectRecovery<'e>>,
        trusted: &LegacyReceiverTrust,
        settled: bool,
        mut observe: impl FnMut(&OperationId, CheckpointStage) -> Result<(), String>,
    ) -> LegacyMigrationReport {
        let mut report = LegacyMigrationReport::default();
        for input in inputs {
            let operation = OperationId(input.effect.operation.clone());
            match self.reconcile_oauth_mode_at(oauth, input, Some(trusted), settled, |stage| {
                observe(&operation, stage)
            }) {
                Ok(true) => report.confirmed.push(operation),
                Ok(false) => report.pending.push(operation),
                Err(error) => {
                    report.stopped = Some(LegacyMigrationStop { operation, error });
                    break;
                }
            }
        }
        report
    }

    pub(super) fn reconcile_oauth_at(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        input: DurableEffectRecovery<'_>,
        legacy: Option<&LegacyReceiverTrust>,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<bool, String> {
        self.reconcile_oauth_mode_at(oauth, input, legacy, false, observe)
    }

    fn reconcile_oauth_mode_at(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        input: DurableEffectRecovery<'_>,
        legacy: Option<&LegacyReceiverTrust>,
        settled: bool,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<bool, String> {
        let authority = oauth.receiver_authority()?;
        let binding = self.receiver_binding(&authority.directory)?;
        let request = match legacy {
            Some(trusted) if trusted.0 == binding => {
                if settled {
                    RecoveryRequest::SettledMappingMigration(binding)
                } else {
                    RecoveryRequest::LegacyMigration(binding)
                }
            }
            Some(_) => return Ok(false),
            None => RecoveryRequest::Receiver(binding),
        };
        let operation = OperationId(input.effect.operation.clone());
        oauth.reconcile_receiver_effect(
            input,
            &authority,
            request,
            || {
                let files = self.lock()?;
                let (image, checkpoint) = self.current(&files)?;
                let bound = checkpoint.and_then(|pin| pin.oauth).as_ref() == Some(&authority);
                Ok(bound.then_some((files, image)))
            },
            |(_, image), intent, outcome| {
                self.committed_receipt(image, &operation, intent, outcome, legacy.is_some())
            },
            observe,
        )
    }

    fn committed_receipt(
        &self,
        image: &Image,
        operation: &OperationId,
        intent: &Signed,
        outcome: &Signed,
        migration: bool,
    ) -> Result<bool, String> {
        let Some(delivery) = image.operations.admitted(operation) else {
            return Ok(false);
        };
        if &delivery.outcome != outcome {
            return Ok(false);
        }
        if !migration {
            return Ok(true);
        }
        let dispatch: ReceiverDispatch = verify(&delivery.authorization, self.trust.sender)?;
        Ok(dispatch.version == VERSION
            && dispatch.domain == DISPATCH_DOMAIN
            && &dispatch.intent == intent
            && dispatch.cut.scope == image.cut.scope
            && dispatch.cut.generation <= image.cut.generation)
    }

    /// Recover the original signed receipt and action without executing again.
    pub fn evidence(&self, operation: &OperationId) -> Result<Option<ReceiverEvidence>, String> {
        let files = self.lock()?;
        let (image, _) = self.current(&files)?;
        Ok(image
            .operations
            .admitted(operation)
            .map(|delivered| ReceiverEvidence {
                journal: ProviderJournal::observation(delivered.action.clone()),
                outcome: delivered.outcome.clone(),
            }))
    }

    #[cfg(test)]
    pub(super) fn crash_receive_oauth(
        &self,
        oauth: &DurableRefreshLedger<'_>,
        input: DurableEffectUse<'_>,
        delivery: ReceiverDelivery<'_>,
        crash: ManagedDeliveryStage,
    ) -> Result<Option<Signed>, String> {
        self.receive_oauth_at(oauth, input, delivery, |stage| {
            if stage == crash {
                Err("simulated managed delivery crash".into())
            } else {
                Ok(())
            }
        })
    }

    #[cfg(test)]
    pub(super) fn crash_promote(
        &self,
        expected: &ReceiverCheckpoint,
        crash: CheckpointStage,
    ) -> Result<ReceiverCut, String> {
        self.promote_at(expected, |stage| crash_at(stage, crash))
    }

    #[cfg(test)]
    pub(super) fn crash_advance(
        &self,
        expected: &ReceiverCut,
        crash: CheckpointStage,
    ) -> Result<ReceiverCut, String> {
        self.advance_at(expected, |stage| crash_at(stage, crash))
    }

    #[cfg(test)]
    pub(super) fn crash_receive(
        &self,
        input: ReceiverDelivery<'_>,
        crash: CheckpointStage,
    ) -> Result<Option<Signed>, String> {
        self.receive_at(input, None, |stage| crash_at(stage, crash))
    }
}

#[cfg(test)]
fn crash_at(stage: CheckpointStage, crash: CheckpointStage) -> Result<(), String> {
    if stage == crash {
        Err("simulated receiver crash".into())
    } else {
        Ok(())
    }
}
