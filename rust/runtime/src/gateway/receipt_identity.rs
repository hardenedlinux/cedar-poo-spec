//! Exact source mapping selected from configured authority and independent evidence.
use super::provider::PROVIDER_OUTCOME_DOMAIN;
use super::provider_durable::LegacyReceiverTrust;
use super::{Commit, EffectIdentity, ProviderOutcome, Signed, Version, verify};
use cedar_poo_core::operation_identity::OperationId;
use p256::ecdsa::VerifyingKey;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

/// Receiver checkpoint and scope selected by trusted configuration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiptAuthority {
    pub checkpoint: PathBuf,
    pub scope: String,
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
            original: ReceiptIdentityCandidate {
                identity: ReceiptIdentityBinding {
                    version,
                    authority: self.receiver.receipt_authority(),
                    provider_key: self
                        .provider_key
                        .to_encoded_point(false)
                        .as_bytes()
                        .to_vec(),
                    witness_key: self.witness_key.to_encoded_point(false).as_bytes().to_vec(),
                    operation: OperationId(self.effect.operation.clone()),
                    intent_sha256: self.intent.source_sha256()?,
                    outcome_sha256: self.outcome.source_sha256()?,
                },
                intent: self.intent.clone(),
                outcome: self.outcome.clone(),
            },
        })
    }
}
