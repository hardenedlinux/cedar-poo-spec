//! Serialized current-effect admission, owner-bound handles and recovery simulation.
use crate::gateway::wire::sign;
use crate::gateway::{
    AuditAuthority, Commit, EffectIdentity, Envelope, FactAuthority, FactBinding, ProviderJournal,
    Reconciliation, ReviewBinding, Signed, Version, Witness, reconcile, verify,
};
use crate::gateway::{Origin, Receipt};
use crate::{Case, ReplayReceipt};
use crate::{json_sha256, value_sha256};
use cedar_poo_core::SchemaSourceJson;
use cedar_poo_core::authority_consumption::AuthorityLedger;
use p256::ecdsa::{SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
/// Witness, outcomes and independent provider evidence supplied for recovery.
pub struct RecoveryEvidence<'a> {
    pub witness: &'a Witness,
    pub receipts: &'a [Signed],
    pub provider: &'a ProviderJournal,
}
/// Borrowed effect channels and the explicit post-send crash control.
pub struct EffectIo<'a> {
    pub witness: &'a mut Witness,
    pub provider: &'a mut ProviderJournal,
    pub crash_after_send: bool,
}
/// Declared negative controls shared with the Lean Production oracle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Fault {
    None,
    Version,
    Issuer,
    Subject,
    Audience,
    Source,
    Value,
    FactGeneration,
    Claimed,
    Unverified,
    Expired,
    MissingFact,
    DuplicateFact,
    ExtraFact,
    Review,
    Policy,
    Schema,
    SourceRevision,
    Epoch,
    Resource,
    ResourceGeneration,
    Payload,
    ActionSchema,
    EffectAudience,
    Observing,
    Unmapped,
    Revoked,
    Unregistered,
    Unconsumed,
    Unknown,
    LogFailure,
    CrashAfterSend,
}
/// Complete simulated admission, precommit, send and outcome state.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Outcome {
    pub admitted: bool,
    pub precommitted: bool,
    pub sent: bool,
    pub receipted: bool,
    pub unknown: bool,
}
impl Outcome {
    fn refused() -> Self {
        Self {
            admitted: false,
            precommitted: false,
            sent: false,
            receipted: false,
            unknown: false,
        }
    }
}
#[derive(Clone)]
pub(super) struct Current {
    pub(super) generation: u64,
    pub(super) effect: EffectIdentity,
    pub(super) review: ReviewBinding,
    pub(super) authority: FactAuthority,
    pub(super) enforcing: bool,
    pub(super) mapped: bool,
    pub(super) revoked: bool,
    pub(super) registered: bool,
    pub(super) original: AuthorityLedger<EffectIdentity>,
    pub(super) unknown: bool,
    pub(super) spent: bool,
}
/// The token is private, owner-bound and consumed by value at final use.
pub struct PreparedEffect {
    owner: Arc<()>,
    generation: u64,
    identity: EffectIdentity,
}
/// Explicit simulator of one already-consumed original operation. It has no
/// disk backend. All model writers and the actual send share the deciding lock.
pub struct Simulator {
    pub(super) owner: Arc<()>,
    pub(super) current: Mutex<Current>,
    pub(super) source_keys: Arc<BTreeMap<String, SigningKey>>,
    pub(super) receipt_key: SigningKey,
    pub(super) cedar: ReplayReceipt,
    pub(super) initial: Envelope,
}
pub(super) fn field_inventory(case: &Case) -> Result<BTreeMap<String, String>, String> {
    let mut values = BTreeMap::new();
    values.insert("principal".into(), json_sha256(&case.request.principal)?);
    values.insert("action".into(), json_sha256(&case.request.action)?);
    values.insert("resource".into(), json_sha256(&case.request.resource)?);
    let context = case
        .request
        .context
        .as_object()
        .ok_or("context must be an object")?;
    for (field, value) in context {
        values.insert(format!("context/{field}"), value_sha256(value)?);
    }
    // Each entity and its attributes retain separate meaning/source bindings.
    for (index, entity) in case
        .entities
        .as_array()
        .ok_or("entities must be an array")?
        .iter()
        .enumerate()
    {
        values.insert(format!("entity/{index}"), value_sha256(entity)?);
        if let Some(attrs) = entity.get("attrs").and_then(serde_json::Value::as_object) {
            for (name, value) in attrs {
                values.insert(
                    format!("entity/{index}/attribute/{name}"),
                    value_sha256(value)?,
                );
            }
        }
    }
    Ok(values)
}
impl Simulator {
    /// Restore from the independently retained witness and outcome records.
    /// Any precommit retains the burn; absence of a verified outcome retains
    /// unknown exposure. This models recovery, not physical anti-rollback.
    pub fn recover(
        case: &Case,
        schema: Option<&SchemaSourceJson>,
        evidence: RecoveryEvidence<'_>,
    ) -> Result<Self, String> {
        let RecoveryEvidence {
            witness,
            receipts,
            provider,
        } = evidence;
        witness.verify_history()?;
        let recovered = Self::new(case, schema)?;
        let operation = recovered.initial.effect.operation.clone();
        let mut committed = false;
        for entry in &witness.entries {
            let commit: Commit = verify(entry, &witness.verifying_key())?;
            if commit.effect.operation == operation {
                committed = true;
            }
        }
        if committed {
            let report = reconcile(
                provider,
                receipts,
                &witness.snapshot(),
                &recovered.audit_authority(witness),
            );
            let independently_matched = report == Reconciliation::default()
                && provider
                    .actions
                    .iter()
                    .any(|action| action.effect == recovered.initial.effect);
            let complete = independently_matched
                && receipts.iter().any(|signed| {
                    let Ok(receipt) = verify::<Receipt>(signed, &recovered.verifying_key()) else {
                        return false;
                    };
                    receipt.action.effect == recovered.initial.effect
                        && witness.entries.iter().any(|entry| {
                            entry.payload == receipt.commit.payload
                                && entry.signature == receipt.commit.signature
                        })
                });
            let mut current = recovered.current.lock().map_err(|_| "poisoned authority")?;
            current.spent = true;
            current.unknown = !complete;
        }
        Ok(recovered)
    }
    /// A resource writer invalidates mediation until fresh source preparation.
    pub fn replace_resource(&self, object: String, generation: u64) -> Result<(), String> {
        let mut current = self.current.lock().map_err(|_| "poisoned authority")?;
        let next = current
            .generation
            .checked_add(1)
            .ok_or("generation exhausted")?;
        current.effect.object = object;
        current.effect.generation = generation;
        current.mapped = false;
        current.generation = next;
        Ok(())
    }
    /// New, disjoint simulation world; never a live rollback/recovery API.
    pub fn fork_simulation(&self) -> Result<Self, String> {
        Ok(Self {
            owner: Arc::new(()),
            current: Mutex::new(
                self.current
                    .lock()
                    .map_err(|_| "poisoned authority")?
                    .clone(),
            ),
            source_keys: Arc::clone(&self.source_keys),
            receipt_key: self.receipt_key.clone(),
            cedar: self.cedar.clone(),
            initial: self.initial.clone(),
        })
    }
    pub fn envelope(&self) -> Envelope {
        self.initial.clone()
    }
    pub fn fact_authority(&self) -> FactAuthority {
        self.current
            .lock()
            .expect("simulation authority")
            .authority
            .clone()
    }
    /// Select public audit material from independent simulation state.
    pub fn audit_authority(&self, witness: &Witness) -> AuditAuthority {
        AuditAuthority {
            gateway_key: self.verifying_key(),
            log_key: witness.verifying_key(),
            facts: self.fact_authority(),
            minimum_size: witness.minimum_size(),
        }
    }
    pub fn verifying_key(&self) -> VerifyingKey {
        *self.receipt_key.verifying_key()
    }
    pub fn prepare(&self, envelope: &Envelope) -> Result<PreparedEffect, String> {
        let current = self.current.lock().map_err(|_| "poisoned authority")?;
        self.check(&current, envelope)?;
        Ok(PreparedEffect {
            owner: Arc::clone(&self.owner),
            generation: current.generation,
            identity: envelope.effect.clone(),
        })
    }
    fn check(&self, current: &Current, envelope: &Envelope) -> Result<Vec<FactBinding>, String> {
        if envelope.version != (Version { major: 1, minor: 0 })
            || envelope.effect != current.effect
            || envelope.review != current.review
            || !current.enforcing
            || !current.mapped
            || current.revoked
            || !current.registered
            || !matches!(current.original.grants.as_slice(), [grant]
                if grant.id.0 == current.effect.operation && grant.effect == current.effect
                    && grant.max_uses == 1 && grant.used == 1)
            || current.unknown
            || current.spent
            || !self.cedar.error_free_allow
        {
            return Err("current effect admission refused".into());
        }
        current.authority.accepts(&envelope.facts)
    }
    pub fn execute(
        &self,
        handle: PreparedEffect,
        envelope: &Envelope,
        io: EffectIo<'_>,
    ) -> Result<(Outcome, Option<Signed>), String> {
        if !Arc::ptr_eq(&handle.owner, &self.owner) {
            return Err("foreign handle".into());
        }
        let mut current = self.current.lock().map_err(|_| "poisoned authority")?;
        if handle.generation != current.generation || handle.identity != current.effect {
            return Err("stale effect handle".into());
        }
        let facts = self.check(&current, envelope)?;
        let next = current
            .generation
            .checked_add(1)
            .ok_or("generation exhausted")?;
        self.execute_locked(&mut current, envelope, facts, next, io)
    }
    fn execute_locked(
        &self,
        current: &mut Current,
        envelope: &Envelope,
        facts: Vec<FactBinding>,
        next: u64,
        io: EffectIo<'_>,
    ) -> Result<(Outcome, Option<Signed>), String> {
        let EffectIo {
            witness,
            provider,
            crash_after_send,
        } = io;
        let mut outcome = Outcome {
            admitted: true,
            precommitted: false,
            sent: false,
            receipted: false,
            unknown: false,
        };
        let Ok(commit) = witness.append(&current.effect, &current.review, &facts) else {
            return Ok((outcome, None));
        };
        current.generation = next;
        current.spent = true;
        current.unknown = true;
        outcome.precommitted = true;
        outcome.sent = true;
        let action = match provider.send(&current.effect) {
            Ok(action) => action,
            Err(_) => {
                outcome.unknown = true;
                return Ok((outcome, None));
            }
        };
        if crash_after_send {
            outcome.unknown = true;
            return Ok((outcome, None));
        }
        let receipt = sign(
            &Receipt {
                version: Version { major: 1, minor: 0 },
                commit,
                action,
                facts: envelope.facts.clone(),
            },
            &self.receipt_key,
        )?;
        current.unknown = false;
        outcome.receipted = true;
        Ok((outcome, Some(receipt)))
    }
    pub fn mutate(&self, fault: Fault, envelope: &mut Envelope) -> Result<(), String> {
        let mut current = self.current.lock().map_err(|_| "poisoned authority")?;
        let next = current
            .generation
            .checked_add(1)
            .ok_or("generation exhausted")?;
        match fault {
            Fault::None | Fault::LogFailure | Fault::CrashAfterSend => (),
            Fault::Version => envelope.version.major = 2,
            Fault::MissingFact => {
                envelope.facts.pop();
            }
            Fault::DuplicateFact => envelope.facts.push(envelope.facts[0].clone()),
            Fault::ExtraFact => {
                let mut fact: FactBinding = serde_json::from_slice(&envelope.facts[0].payload)
                    .map_err(|e| e.to_string())?;
                fact.field = "extra".into();
                envelope
                    .facts
                    .push(sign(&fact, &self.source_keys[&fact.issuer])?);
            }
            Fault::Unverified => envelope.facts[0].signature[0] ^= 1,
            Fault::Expired => current.authority.now = 100,
            Fault::Issuer
            | Fault::Subject
            | Fault::Audience
            | Fault::Source
            | Fault::Value
            | Fault::FactGeneration
            | Fault::Claimed => {
                let mut fact: FactBinding = serde_json::from_slice(&envelope.facts[0].payload)
                    .map_err(|e| e.to_string())?;
                let issuer_key = &self.source_keys[&fact.issuer];
                match fault {
                    Fault::Issuer => fact.issuer = "other".into(),
                    Fault::Subject => fact.subject = "other".into(),
                    Fault::Audience => fact.audience = "other".into(),
                    Fault::Source => fact.source = "other".into(),
                    Fault::Value => fact.value = "other".into(),
                    Fault::FactGeneration => fact.generation += 1,
                    Fault::Claimed => fact.origin = Origin::Claimed,
                    _ => unreachable!(),
                }
                envelope.facts[0] = sign(&fact, issuer_key)?;
            }
            Fault::Review => envelope.review.report = "other".into(),
            Fault::Policy => envelope.review.after = "other".into(),
            Fault::Schema => envelope.review.schema = "other".into(),
            Fault::SourceRevision => envelope.review.source = "other".into(),
            Fault::Epoch => envelope.review.epoch += 1,
            Fault::Resource => envelope.effect.object = "other".into(),
            Fault::ResourceGeneration => envelope.effect.generation += 1,
            Fault::Payload => envelope.effect.payload = "other".into(),
            Fault::ActionSchema => envelope.effect.action_schema = "other".into(),
            Fault::EffectAudience => envelope.effect.audience = "other".into(),
            Fault::Observing => current.enforcing = false,
            Fault::Unmapped => current.mapped = false,
            Fault::Revoked => current.revoked = true,
            Fault::Unregistered => current.registered = false,
            Fault::Unconsumed => current.original.grants[0].used = 0,
            Fault::Unknown => current.unknown = true,
        }
        // Every writer invalidates existing handles, including equal-value ABA.
        current.generation = next;
        Ok(())
    }
    pub fn run(&self, fault: Fault) -> Result<(Outcome, Reconciliation), String> {
        let mut envelope = self.envelope();
        self.mutate(fault, &mut envelope)?;
        let mut witness = Witness::simulation();
        witness.available = fault != Fault::LogFailure;
        let mut provider = ProviderJournal::default();
        let (outcome, receipt) = match self.prepare(&envelope) {
            Ok(handle) => self.execute(
                handle,
                &envelope,
                EffectIo {
                    witness: &mut witness,
                    provider: &mut provider,
                    crash_after_send: fault == Fault::CrashAfterSend,
                },
            )?,
            Err(_) => (Outcome::refused(), None),
        };
        let report = reconcile(
            &provider,
            &receipt.into_iter().collect::<Vec<_>>(),
            &witness.snapshot(),
            &self.audit_authority(&witness),
        );
        Ok((outcome, report))
    }
}
