//! Strict protocol representation and signature verification.
use p256::ecdsa::{
    Signature, SigningKey, VerifyingKey,
    signature::{Signer, Verifier},
};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
/// Exact supported wire protocol version; unknown versions refuse.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Version {
    pub major: u64,
    pub minor: u64,
}
/// Issuer statement category; claimed input is never trusted evidence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Origin {
    Claimed,
    Observed,
    Attested,
}
/// One issuer-bound field with exact meaning, scope, generation and lease.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FactBinding {
    pub issuer: String,
    pub subject: String,
    pub audience: String,
    pub source: String,
    pub field: String,
    pub value: String,
    pub generation: u64,
    pub origin: Origin,
    pub not_before: u64,
    pub expires_at: u64,
}
/// Exact effect object and operation identity across admission and execution.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, PartialOrd, Ord)]
#[serde(deny_unknown_fields)]
pub struct EffectIdentity {
    pub operation: String,
    pub object: String,
    pub generation: u64,
    pub payload: String,
    pub action_schema: String,
    pub audience: String,
}
/// Independently registered policy, schema, source and frontier identity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewBinding {
    pub before: String,
    pub after: String,
    pub schema: String,
    pub source: String,
    pub epoch: u64,
    pub report: String,
}
/// Sign exact serialized payload bytes, with a trusted key selected outside it.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Signed {
    #[serde(with = "base64url")]
    pub payload: Vec<u8>,
    #[serde(with = "base64url")]
    pub signature: Vec<u8>,
}
#[path = "base64url.rs"]
mod base64url;
/// Decode an independently configured SEC1 P-256 verification key.
pub fn public_key(bytes: &[u8]) -> Result<VerifyingKey, String> {
    VerifyingKey::from_sec1_bytes(bytes).map_err(|e| e.to_string())
}
pub(super) const MAX_SIGNED_PAYLOAD: usize = 1_048_576;

pub(super) fn sign(value: &impl Serialize, key: &SigningKey) -> Result<Signed, String> {
    let payload = serde_json::to_vec(value).map_err(|e| e.to_string())?;
    if payload.len() > MAX_SIGNED_PAYLOAD {
        return Err("oversized signed payload".into());
    }
    let signature: Signature = key.sign(&payload);
    Ok(Signed {
        payload,
        signature: signature.to_bytes().to_vec(),
    })
}
/// Verify original payload bytes with a trusted key before typed decoding.
pub fn verify<T: DeserializeOwned>(value: &Signed, key: &VerifyingKey) -> Result<T, String> {
    verify_signature(value, key)?;
    serde_json::from_slice(&value.payload).map_err(|e| e.to_string())
}

pub(super) fn verify_signature(value: &Signed, key: &VerifyingKey) -> Result<(), String> {
    if value.payload.len() > MAX_SIGNED_PAYLOAD {
        return Err("oversized signed payload".into());
    }
    let signature = Signature::from_slice(&value.signature).map_err(|e| e.to_string())?;
    key.verify(&value.payload, &signature)
        .map_err(|_| "unverified evidence".into())
}
/// Untrusted versioned candidate carrying signed field evidence.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Envelope {
    pub current_world: String,
    pub version: Version,
    pub effect: EffectIdentity,
    pub review: ReviewBinding,
    pub facts: Vec<Signed>,
}

pub(super) fn simulation_key(byte: u8) -> SigningKey {
    static KEYS: std::sync::LazyLock<[SigningKey; 7]> = std::sync::LazyLock::new(|| {
        std::array::from_fn(|index| {
            SigningKey::from_slice(&[index as u8 + 1; 32]).expect("fixed simulation scalar")
        })
    });
    match byte
        .checked_sub(1)
        .and_then(|index| KEYS.get(usize::from(index)))
    {
        Some(key) => key.clone(),
        None => SigningKey::from_slice(&[byte; 32]).expect("fixed simulation scalar"),
    }
}

#[cfg(test)]
#[path = "../../tests/unit/gateway_wire.rs"]
mod tests;
