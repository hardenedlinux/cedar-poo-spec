//! Receiver-owned cut, operation reservation, and signed simulated effect.
use super::checkpoint_store::{CheckpointStage, LockedCheckpoint};
use super::provider::ProviderRequest;
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

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ReceiverCheckpoint {
    active: PathBuf,
    cut: ReceiverCut,
    digest: String,
}

impl ReceiverCheckpoint {
    fn for_image(active: &Path, image: &Image) -> Result<Self, String> {
        Ok(Self {
            active: active.into(),
            cut: image.cut.clone(),
            digest: crate::json_sha256(&("cedar-poo/receiver-failover/v1", image))?,
        })
    }

    fn matches(&self, image: &Image) -> Result<bool, String> {
        Ok(self.cut == image.cut && self.digest == Self::for_image(&self.active, image)?.digest)
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

    fn current(&self, files: &LockedReceiver<'_>) -> Result<Image, String> {
        let (image, checkpoint) = self.qualified(files)?;
        if let (Some(checkpoint), Some(placement)) = (checkpoint, &self.placement)
            && checkpoint.active != placement.replica
        {
            return Err("receiver replica has not been promoted".into());
        }
        Ok(image)
    }

    fn persist(
        &self,
        files: &LockedReceiver<'_>,
        image: &Image,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<(), String> {
        if let (Some(checkpoint), Some(placement)) = (&files.checkpoint, &self.placement) {
            let next = ReceiverCheckpoint::for_image(&placement.replica, image)?;
            files.replica.persist(image)?;
            checkpoint.persist_at(&next, observe)
        } else {
            files.replica.persist_at(image, observe)
        }
    }

    /// Activate only an exact copy of the independently acknowledged image.
    /// The shared checkpoint switches placement and advances the cut together.
    pub fn promote(&self) -> Result<ReceiverCut, String> {
        self.promote_at(|_| Ok(()))
    }

    fn promote_at(
        &self,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<ReceiverCut, String> {
        let placement = self
            .placement
            .as_ref()
            .ok_or("receiver has no independent checkpoint")?;
        let files = self.lock()?;
        let (mut image, checkpoint) = self.qualified(&files)?;
        let checkpoint = checkpoint.ok_or("missing independent receiver checkpoint")?;
        if checkpoint.active == placement.replica {
            return Err("receiver replica is already active".into());
        }
        image.cut.generation = image
            .cut
            .generation
            .checked_add(1)
            .ok_or("receiver cut exhausted")?;
        self.persist(&files, &image, observe)?;
        Ok(image.cut)
    }

    /// Read the current independent receiver cut, including after restart.
    pub fn cut(&self) -> Result<ReceiverCut, String> {
        Ok(self.current(&self.lock()?)?.cut)
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
        let mut image = self.current(&files)?;
        if &image.cut != expected {
            return Err("stale receiver cut".into());
        }
        image.cut.generation = image
            .cut
            .generation
            .checked_add(1)
            .ok_or("receiver cut exhausted")?;
        self.persist(&files, &image, observe)?;
        Ok(image.cut)
    }

    /// Apply the simulated effect and persist its signed outcome atomically.
    pub fn receive(&self, input: ReceiverDelivery<'_>) -> Result<Option<Signed>, String> {
        self.receive_at(input, |_| Ok(()))
    }

    fn receive_at(
        &self,
        input: ReceiverDelivery<'_>,
        observe: impl FnMut(CheckpointStage) -> Result<(), String>,
    ) -> Result<Option<Signed>, String> {
        let files = self.lock()?;
        let mut image = self.current(&files)?;
        let dispatch: ReceiverDispatch = verify(input.authorization, self.trust.sender)?;
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
        self.persist(&files, &image, observe)?;
        Ok(Some(outcome))
    }

    /// Recover the original signed receipt and action without executing again.
    pub fn evidence(&self, operation: &OperationId) -> Result<Option<ReceiverEvidence>, String> {
        let files = self.lock()?;
        let image = self.current(&files)?;
        Ok(image
            .operations
            .admitted(operation)
            .map(|delivered| ReceiverEvidence {
                journal: ProviderJournal::observation(delivered.action.clone()),
                outcome: delivered.outcome.clone(),
            }))
    }

    #[cfg(test)]
    pub(super) fn crash_promote(&self, crash: CheckpointStage) -> Result<ReceiverCut, String> {
        self.promote_at(|stage| crash_at(stage, crash))
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
        self.receive_at(input, |stage| crash_at(stage, crash))
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
