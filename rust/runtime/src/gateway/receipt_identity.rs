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

/// Decoded model receipt and its complete independently selected authority frame.
/// It is an untrusted proposal until a verified source context accepts it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiptSymbol {
    pub receipt: ProviderOutcome,
    pub provider_signature: Vec<u8>,
    pub version: Version,
    pub authority: ReceiptAuthority,
    pub provider_key: Vec<u8>,
    pub witness_key: Vec<u8>,
    pub operation: OperationId,
}

impl ReceiptSymbol {
    fn matches(&self, binding: &ReceiptIdentityBinding) -> bool {
        self.version == binding.version
            && self.authority == binding.authority
            && self.provider_key == binding.provider_key
            && self.witness_key == binding.witness_key
            && self.operation == binding.operation
    }
}

/// Transport proposal: a symbolic receipt and the complete native signed-source binding.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiptRealizationCandidate {
    pub symbol: ReceiptSymbol,
    pub native: ReceiptIdentityCandidate,
}

/// A checked association borrows both immutable inputs; construction grants no authorization.
pub struct VerifiedReceiptRealization<'a> {
    symbol: &'a ReceiptSymbol,
    native: &'a VerifiedReceiptIdentity,
}

impl VerifiedReceiptRealization<'_> {
    /// Explicit transport materialization; ordinary checks borrow the prepared sources.
    pub fn candidate(&self) -> ReceiptRealizationCandidate {
        ReceiptRealizationCandidate {
            symbol: self.symbol.clone(),
            native: self.native.candidate(),
        }
    }

    /// The model scope, decoded receipt, digests and raw signed sources must all agree.
    pub fn check(&self, candidate: &ReceiptRealizationCandidate) -> Option<ReceiptIdentityBinding> {
        (candidate.symbol == *self.symbol).then_some(())?;
        self.native.check(&candidate.native)
    }
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
    /// Decode the symbolic receipt and scope from already authenticated sources.
    pub fn symbol(&self) -> Result<ReceiptSymbol, String> {
        let identity = &self.original.identity;
        Ok(ReceiptSymbol {
            receipt: serde_json::from_slice(&self.original.outcome.payload)
                .map_err(|error| error.to_string())?,
            provider_signature: self.original.outcome.signature.clone(),
            version: identity.version.clone(),
            authority: identity.authority.clone(),
            provider_key: identity.provider_key.clone(),
            witness_key: identity.witness_key.clone(),
            operation: identity.operation.clone(),
        })
    }

    /// Bind a full symbolic receipt only inside this authenticated source context.
    /// The body is decoded from already verified bytes; signatures are not verified again.
    pub fn realize<'a>(
        &'a self,
        symbol: &'a ReceiptSymbol,
    ) -> Result<VerifiedReceiptRealization<'a>, String> {
        if !symbol.matches(&self.original.identity) {
            return Err("symbolic receipt scope differs from verified identity".into());
        }
        let decoded: ProviderOutcome = serde_json::from_slice(&self.original.outcome.payload)
            .map_err(|error| error.to_string())?;
        if symbol.receipt != decoded || symbol.provider_signature != self.original.outcome.signature
        {
            return Err("symbolic receipt differs from verified outcome".into());
        }
        Ok(VerifiedReceiptRealization {
            symbol,
            native: self,
        })
    }

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
