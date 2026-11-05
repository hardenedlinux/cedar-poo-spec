//! Exact source mapping selected from configured authority and independent evidence.
use super::provider::PROVIDER_OUTCOME_DOMAIN;
use super::{Commit, EffectIdentity, ProviderOutcome, Signed, Version, verify};
use cedar_poo_core::operation_identity::OperationId;
use p256::ecdsa::VerifyingKey;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

/// Receiver checkpoint and scope selected by trusted configuration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiptAuthority {
    pub checkpoint: PathBuf,
    pub scope: String,
}

/// Receiver authority selected independently by the host for a legacy
/// migration. Construct it from trusted deployment configuration.
pub struct LegacyReceiverTrust(pub(super) ReceiptAuthority);

impl LegacyReceiverTrust {
    /// Project the configured receiver identity for a source-bound receipt mapping.
    pub fn receipt_authority(&self) -> ReceiptAuthority {
        ReceiptAuthority {
            checkpoint: self.0.checkpoint.clone(),
            scope: self.0.scope.clone(),
        }
    }

    /// Resolve the checkpoint from trusted deployment configuration.
    pub fn from_config(checkpoint: &Path, scope: &str) -> Result<Self, String> {
        if scope.is_empty() {
            return Err("missing legacy receiver scope".into());
        }
        let checkpoint = checkpoint
            .canonicalize()
            .map_err(|error| error.to_string())?;
        Ok(Self(ReceiptAuthority {
            checkpoint,
            scope: scope.into(),
        }))
    }
}

/// Versioned operation and authority identity of the exact signed sources.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiptIdentityBinding {
    pub version: Version,
    pub authority: ReceiptAuthority,
    pub provider_key: Vec<u8>,
    pub witness_key: Vec<u8>,
    pub operation: OperationId,
    pub intent_sha256: String,
    pub outcome_sha256: String,
}

/// Untrusted mapping proposal, including source bytes as well as their digests.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiptIdentityCandidate {
    pub identity: ReceiptIdentityBinding,
    pub intent: Signed,
    pub outcome: Signed,
}

/// Durable source binding; the retained effect already owns the signed intent.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct StoredReceiptIdentity {
    pub(super) identity: ReceiptIdentityBinding,
    outcome: Signed,
}

impl StoredReceiptIdentity {
    /// Called only after the shared audit and locked independent receiver check.
    pub(super) fn from_audited(
        authority: ReceiptAuthority,
        provider_key: &VerifyingKey,
        witness_key: &VerifyingKey,
        operation: OperationId,
        intent: &Signed,
        outcome: &Signed,
    ) -> Result<Self, String> {
        Ok(Self {
            identity: ReceiptIdentityBinding {
                version: Version { major: 1, minor: 0 },
                authority,
                provider_key: provider_key.to_encoded_point(false).as_bytes().to_vec(),
                witness_key: witness_key.to_encoded_point(false).as_bytes().to_vec(),
                operation,
                intent_sha256: intent.source_sha256()?,
                outcome_sha256: outcome.source_sha256()?,
            },
            outcome: outcome.clone(),
        })
    }

    pub(super) fn candidate(&self, intent: &Signed) -> ReceiptIdentityCandidate {
        ReceiptIdentityCandidate {
            identity: self.identity.clone(),
            intent: intent.clone(),
            outcome: self.outcome.clone(),
        }
    }
}

/// Context comes from trusted configuration, the retained intent and the
/// independently selected receiver outcome. Mapping is a read-only operation.
#[derive(Clone, Copy)]
pub struct ReceiptIdentityContext<'a> {
    pub receiver: &'a LegacyReceiverTrust,
    pub provider_key: &'a VerifyingKey,
    pub witness_key: &'a VerifyingKey,
    pub effect: &'a EffectIdentity,
    pub intent: &'a Signed,
    pub outcome: &'a Signed,
}

/// Immutable mapping prepared from authenticated, independently selected sources.
pub struct VerifiedReceiptIdentity {
    original: ReceiptIdentityCandidate,
}

impl VerifiedReceiptIdentity {
    /// Return the source-bound candidate for transport or subsequent comparisons.
    pub fn candidate(&self) -> ReceiptIdentityCandidate {
        self.original.clone()
    }

    /// Accept only the complete original binding and exact signed source bytes.
    pub fn check(&self, candidate: &ReceiptIdentityCandidate) -> Option<ReceiptIdentityBinding> {
        (candidate == &self.original).then(|| self.original.identity.clone())
    }
}

impl ReceiptIdentityContext<'_> {
    /// Authenticate sources and bind them to the configured operation and authorities.
    pub fn prepare(&self) -> Result<VerifiedReceiptIdentity, String> {
        let intent: Commit = verify(self.intent, self.witness_key)?;
        let outcome: ProviderOutcome = verify(self.outcome, self.provider_key)?;
        let version = Version { major: 1, minor: 0 };
        if intent.version != version
            || outcome.version != version
            || outcome.outcome.version != version
            || outcome.domain != PROVIDER_OUTCOME_DOMAIN
            || intent.effect != *self.effect
            || outcome.outcome.action.effect != *self.effect
            || outcome.outcome.commit != *self.intent
            || outcome.log_key != self.witness_key.to_encoded_point(false).as_bytes()
        {
            return Err("receipt identity context differs from the verified sources".into());
        }
        Ok(VerifiedReceiptIdentity {
            original: StoredReceiptIdentity::from_audited(
                self.receiver.receipt_authority(),
                self.provider_key,
                self.witness_key,
                OperationId(self.effect.operation.clone()),
                self.intent,
                self.outcome,
            )?
            .candidate(self.intent),
        })
    }
}
