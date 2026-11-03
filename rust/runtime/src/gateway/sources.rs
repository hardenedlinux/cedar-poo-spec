//! Independent field inventory and verified immutable source preparation.
use super::wire::{MAX_SIGNED_PAYLOAD, verify_signature};
use super::{FactBinding, Origin, Signed, Version};
use p256::ecdsa::VerifyingKey;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
/// One issuer signs the complete ordered statement. Every field retains its
/// own scope, value, generation and lease; independently trusted issuers never mix.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FactStatement {
    pub version: Version,
    pub facts: Vec<FactBinding>,
}
#[derive(Deserialize)]
#[serde(untagged)]
enum SourcePayload {
    Field(FactBinding),
    Statement(FactStatement),
}
impl SourcePayload {
    fn decode(signed: &Signed) -> Result<Vec<FactBinding>, String> {
        if signed.payload.len() > MAX_SIGNED_PAYLOAD {
            return Err("oversized source statement".into());
        }
        match serde_json::from_slice(&signed.payload).map_err(|e| e.to_string())? {
            Self::Field(fact) if signed.payload.len() <= 65_536 => Ok(vec![fact]),
            Self::Statement(statement)
                if statement.version == (Version { major: 1, minor: 0 })
                    && !statement.facts.is_empty() =>
            {
                for fact in &statement.facts {
                    if serde_json::to_vec(fact).map_err(|e| e.to_string())?.len() > 65_536 {
                        return Err("oversized fact".into());
                    }
                }
                Ok(statement.facts)
            }
            _ => Err("invalid or oversized source payload".into()),
        }
    }
}
/// A current field inventory and independently selected verifying key.
/// Incoming provenance strings alone grant no authority.
#[derive(Clone)]
pub struct FactAuthority {
    expected: Arc<BTreeMap<String, FactBinding>>,
    keys: Arc<BTreeMap<String, VerifyingKey>>,
    pub(super) now: u64,
    prepared: Arc<Vec<(Signed, Vec<FactBinding>)>>,
}
impl FactAuthority {
    pub fn new(
        expected: Vec<FactBinding>,
        keys: BTreeMap<String, VerifyingKey>,
        now: u64,
    ) -> Result<Self, String> {
        let count = expected.len();
        let expected: BTreeMap<_, _> = expected.into_iter().map(|f| (f.field.clone(), f)).collect();
        if count == 0 || expected.len() != count {
            return Err("invalid fact inventory".into());
        }
        if expected
            .values()
            .any(|fact| !keys.contains_key(&fact.issuer))
        {
            return Err("missing trusted issuer key".into());
        }
        Ok(Self {
            expected: Arc::new(expected),
            keys: Arc::new(keys),
            now,
            prepared: Arc::new(Vec::new()),
        })
    }
    /// Retain verified immutable source material, never a current-use decision.
    pub fn prepare_sources(mut self, evidence: &[Signed]) -> Result<Self, String> {
        let groups = self.validate(evidence)?;
        self.prepared = Arc::new(evidence.iter().cloned().zip(groups).collect());
        Ok(self)
    }
    pub fn at_time(&self, now: u64) -> Result<Self, String> {
        if now < self.now {
            return Err("source clock moved backwards".into());
        }
        Ok(Self {
            now,
            ..self.clone()
        })
    }
    pub fn public_material(&self) -> (Vec<FactBinding>, BTreeMap<String, Vec<u8>>, u64) {
        (
            self.expected.values().cloned().collect(),
            self.keys
                .iter()
                .map(|(issuer, key)| {
                    (
                        issuer.clone(),
                        key.to_encoded_point(false).as_bytes().to_vec(),
                    )
                })
                .collect(),
            self.now,
        )
    }
    pub fn accepts(&self, evidence: &[Signed]) -> Result<Vec<FactBinding>, String> {
        if evidence.len() == self.prepared.len()
            && !evidence.is_empty()
            && evidence
                .iter()
                .zip(self.prepared.iter())
                .all(|(actual, (known, _))| {
                    actual.payload == known.payload && actual.signature == known.signature
                })
        {
            return self
                .prepared
                .iter()
                .flat_map(|(_, facts)| facts)
                .map(|fact| {
                    self.check_current(fact)?;
                    Ok(fact.clone())
                })
                .collect();
        }
        Ok(self.validate(evidence)?.into_iter().flatten().collect())
    }
    fn validate(&self, evidence: &[Signed]) -> Result<Vec<Vec<FactBinding>>, String> {
        if evidence.is_empty() || evidence.len() > self.expected.len() {
            return Err("fact inventory mismatch".into());
        }
        let mut seen = BTreeSet::new();
        let groups = evidence
            .iter()
            .map(|signed| self.verify_group(signed, &mut seen))
            .collect::<Result<Vec<_>, _>>()?;
        if seen.len() != self.expected.len() {
            return Err("incomplete fact inventory".into());
        }
        Ok(groups)
    }
    fn verify_group(
        &self,
        signed: &Signed,
        seen: &mut BTreeSet<String>,
    ) -> Result<Vec<FactBinding>, String> {
        let facts = SourcePayload::decode(signed)?;
        let first = facts.first().ok_or("empty source statement")?;
        let issuer = &self
            .expected
            .get(&first.field)
            .ok_or("unknown fact field")?
            .issuer;
        for fact in &facts {
            if !seen.insert(fact.field.clone()) {
                return Err("duplicate fact field".into());
            }
            self.check_current(fact)?;
            if &fact.issuer != issuer {
                return Err("mixed source issuers".into());
            }
        }
        // The key comes from the independently retained expected inventory.
        verify_signature(signed, &self.keys[issuer])?;
        Ok(facts)
    }
    fn check_current(&self, fact: &FactBinding) -> Result<(), String> {
        if self.expected.get(&fact.field) != Some(fact)
            || fact.origin == Origin::Claimed
            || self.now < fact.not_before
            || self.now >= fact.expires_at
        {
            return Err("fact source, authority, value or validity changed".into());
        }
        Ok(())
    }
}
