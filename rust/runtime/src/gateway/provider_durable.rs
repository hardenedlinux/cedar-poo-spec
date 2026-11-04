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
use std::path::Path;

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
    operations: OperationLedger<Delivered>,
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
}

impl<'a> DurableReceiver<'a> {
    /// Select the independent receiver directory and its configured roots.
    pub fn new(directory: &'a Path, trust: ReceiverTrust<'a>) -> Self {
        Self { directory, trust }
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
        LockedCheckpoint::open(self.directory)?.initialize(&Image {
            version: VERSION,
            cut: ReceiverCut {
                scope: self.trust.scope.into(),
                generation: 0,
            },
            keys: self.keys(),
            operations: OperationLedger::default(),
        })
    }

    fn read(&self, file: &LockedCheckpoint<'_>) -> Result<Image, String> {
        let image: Image = file.read()?;
        if self.trust.scope.is_empty()
            || image.version != VERSION
            || image.cut.scope != self.trust.scope
            || image.keys != self.keys()
        {
            return Err("receiver scope, version or roots changed".into());
        }
        file.sync_directory()?;
        Ok(image)
    }

    /// Read the current independent receiver cut, including after restart.
    pub fn cut(&self) -> Result<ReceiverCut, String> {
        Ok(self.read(&LockedCheckpoint::open(self.directory)?)?.cut)
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
        let file = LockedCheckpoint::open(self.directory)?;
        let mut image = self.read(&file)?;
        if &image.cut != expected {
            return Err("stale receiver cut".into());
        }
        image.cut.generation = image
            .cut
            .generation
            .checked_add(1)
            .ok_or("receiver cut exhausted")?;
        file.persist_at(&image, observe)?;
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
        let file = LockedCheckpoint::open(self.directory)?;
        let mut image = self.read(&file)?;
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
        file.persist_at(&image, observe)?;
        Ok(Some(outcome))
    }

    /// Recover the original signed receipt and action without executing again.
    pub fn evidence(&self, operation: &OperationId) -> Result<Option<ReceiverEvidence>, String> {
        let file = LockedCheckpoint::open(self.directory)?;
        let image = self.read(&file)?;
        Ok(image
            .operations
            .admitted(operation)
            .map(|delivered| ReceiverEvidence {
                journal: ProviderJournal::observation(delivered.action.clone()),
                outcome: delivered.outcome.clone(),
            }))
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
