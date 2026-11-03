//! Independent field inventory and verified immutable source preparation.
use super::{FactBinding, Origin, Signed, verify};
use p256::ecdsa::VerifyingKey;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
/// A current field inventory and independently selected verifying key.
/// Incoming provenance strings alone grant no authority.
#[derive(Clone)]
pub struct FactAuthority {
    expected: Arc<BTreeMap<String, FactBinding>>,
    keys: Arc<BTreeMap<String, VerifyingKey>>,
    pub(super) now: u64,
    prepared: Arc<BTreeMap<String, (Signed, FactBinding)>>,
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
            prepared: Arc::new(BTreeMap::new()),
        })
    }
    /// Retain verified immutable source material, never a current-use decision.
    /// Every use still checks exact inventory, binding, generation and time.
    pub fn prepare_sources(mut self, evidence: &[Signed]) -> Result<Self, String> {
        let facts = self.accepts(evidence)?;
        self.prepared = Arc::new(
            evidence
                .iter()
                .cloned()
                .zip(facts)
                .map(|(signed, fact)| (fact.field.clone(), (signed, fact)))
                .collect(),
        );
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
        if evidence.len() != self.expected.len() {
            return Err("fact inventory mismatch".into());
        }
        let mut seen = BTreeSet::new();
        let mut facts = Vec::with_capacity(evidence.len());
        for signed in evidence {
            if signed.payload.len() > 65_536 {
                return Err("oversized fact".into());
            }
            let fact: FactBinding =
                serde_json::from_slice(&signed.payload).map_err(|e| e.to_string())?;
            if !seen.insert(fact.field.clone())
                || self.expected.get(&fact.field) != Some(&fact)
                || fact.origin == Origin::Claimed
                || self.now < fact.not_before
                || self.now >= fact.expires_at
            {
                return Err("fact source, authority, value or validity changed".into());
            }
            let expected = &self.expected[&fact.field];
            let verified = match self.prepared.get(&fact.field) {
                Some((prepared, value))
                    if prepared.payload == signed.payload
                        && prepared.signature == signed.signature =>
                {
                    value.clone()
                }
                _ => verify(signed, &self.keys[&expected.issuer])?,
            };
            facts.push(verified);
        }
        Ok(facts)
    }
}
