//! Serialized current-effect admission, owner-bound handles and recovery simulation.
use super::RegisteredReview;
use crate::gateway::ReviewTrust;
use crate::gateway::wire::sign;
use crate::gateway::witness::PrecommitInput;
use crate::gateway::{
    AuditAuthority, EffectIdentity, Envelope, FactAuthority, FactBinding, FactStatement,
    ProviderJournal, Reconciliation, ReviewBinding, Signed, Version, Witness, reconcile,
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
    pub publications: &'a [Signed],
    pub audit: &'a AuditAuthority,
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
    pub(super) active_owner: Arc<()>,
    pub(super) fact_generation: u64,
    pub(super) sources_current: bool,
    pub(super) facts: Vec<Signed>,
    pub(super) world: String,
    pub(super) case: Case,
    pub(super) schema: Option<SchemaSourceJson>,
    pub(super) cedar: ReplayReceipt,
    pub(super) release_root: String,
    pub(super) model_source: String,
    pub(super) pending_review: Option<RegisteredReview>,
    pub(super) publications: Vec<Signed>,
    pub(super) publication_unknown: bool,
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
    pub(super) current: Arc<Mutex<Current>>,
    pub(super) source_keys: Arc<BTreeMap<String, SigningKey>>,
    pub(super) receipt_key: SigningKey,
    pub(super) review_trust: ReviewTrust,
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
pub(super) fn original_consumed(current: &Current) -> bool {
    matches!(current.original.grants.as_slice(), [grant]
        if grant.id.0 == current.effect.operation && grant.effect == current.effect
            && grant.max_uses == 1 && grant.used == 1)
}
impl Simulator {
    /// A resource writer invalidates mediation until fresh source preparation.
    pub fn replace_resource(&self, object: String, generation: u64) -> Result<(), String> {
        let mut current = self.current.lock().map_err(|_| "poisoned authority")?;
        self.check_owner(&current)?;
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
        let mut snapshot = self
            .current
            .lock()
            .map_err(|_| "poisoned authority")?
            .clone();
        self.check_owner(&snapshot)?;
        let owner = Arc::new(());
        snapshot.active_owner = Arc::clone(&owner);
        Ok(Self {
            owner,
            current: Arc::new(Mutex::new(snapshot)),
            source_keys: Arc::clone(&self.source_keys),
            receipt_key: self.receipt_key.clone(),
            review_trust: self.review_trust.clone(),
            initial: self.initial.clone(),
        })
    }
    pub fn envelope(&self) -> Envelope {
        let current = self.current.lock().expect("poisoned simulation authority");
        Envelope {
            current_world: current.world.clone(),
            version: self.initial.version.clone(),
            effect: current.effect.clone(),
            review: current.review.clone(),
            facts: current.facts.clone(),
        }
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
            review_trust: Some(self.review_trust.clone()),
            prepared_publications: None,
        }
    }
    /// Public trust material for independent review and approval verification.
    pub fn review_trust(&self) -> ReviewTrust {
        self.review_trust.clone()
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
        self.check_owner(current)?;
        if envelope.version != (Version { major: 1, minor: 0 })
            || envelope.effect != current.effect
            || envelope.review != current.review
            || envelope.current_world != current.world
            || !current.enforcing
            || !current.mapped
            || current.revoked
            || !current.registered
            || !original_consumed(current)
            || !current.sources_current
            || current.unknown
            || current.spent
            || current.publication_unknown
            || !current.cedar.error_free_allow
        {
            return Err("current effect admission refused".into());
        }
        let facts = current.authority.accepts(&envelope.facts)?;
        if facts.iter().any(|fact| fact.source != current.world) {
            return Err("fact world differs from the current SDK preparation".into());
        }
        Ok(facts)
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
        self.check_owner(&current)?;
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
        let Ok(commit) = witness.append(PrecommitInput {
            current_world: &current.world,
            effect: &current.effect,
            review: &current.review,
            facts: &facts,
            publications: &current.publications,
        }) else {
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
        let receipt = match sign(
            &Receipt {
                version: Version { major: 1, minor: 0 },
                commit,
                action,
                facts: envelope.facts.clone(),
                publications: current.publications.clone(),
            },
            &self.receipt_key,
        ) {
            Ok(receipt) => receipt,
            Err(_) => {
                outcome.unknown = true;
                return Ok((outcome, None));
            }
        };
        current.unknown = false;
        outcome.receipted = true;
        Ok((outcome, Some(receipt)))
    }
    pub fn mutate(&self, fault: Fault, envelope: &mut Envelope) -> Result<(), String> {
        let mut current = self.current.lock().map_err(|_| "poisoned authority")?;
        self.check_owner(&current)?;
        let next = current
            .generation
            .checked_add(1)
            .ok_or("generation exhausted")?;
        self.apply_fault(&mut current, fault, envelope)?;
        current.generation = next;
        Ok(())
    }
    fn apply_fault(
        &self,
        current: &mut Current,
        fault: Fault,
        envelope: &mut Envelope,
    ) -> Result<(), String> {
        match fault {
            Fault::None | Fault::LogFailure | Fault::CrashAfterSend => (),
            Fault::Version => envelope.version.major = 2,
            Fault::MissingFact => {
                envelope.facts.pop();
            }
            Fault::DuplicateFact => {
                let fact = envelope.facts.first().ok_or("missing source fact")?.clone();
                envelope.facts.push(fact);
            }
            Fault::ExtraFact => {
                let mut statement: FactStatement = serde_json::from_slice(
                    &envelope.facts.first().ok_or("missing source fact")?.payload,
                )
                .map_err(|e| e.to_string())?;
                let fact = statement
                    .facts
                    .first_mut()
                    .ok_or("empty source statement")?;
                fact.field = "extra".into();
                envelope.facts.push(sign(
                    &fact,
                    self.source_keys
                        .get(&fact.issuer)
                        .ok_or("unknown source issuer")?,
                )?);
            }
            Fault::Unverified => {
                let fact = envelope.facts.first_mut().ok_or("missing source fact")?;
                let byte = fact
                    .signature
                    .first_mut()
                    .ok_or("missing source signature")?;
                *byte ^= 1;
            }
            Fault::Expired => {
                let expiry = current
                    .authority
                    .public_material()
                    .0
                    .into_iter()
                    .map(|fact| fact.expires_at)
                    .max()
                    .ok_or("missing source lease")?;
                current.authority = current
                    .authority
                    .at_time(current.authority.now.max(expiry))?;
            }
            Fault::Issuer
            | Fault::Subject
            | Fault::Audience
            | Fault::Source
            | Fault::Value
            | Fault::FactGeneration
            | Fault::Claimed => {
                let mut statement: FactStatement = serde_json::from_slice(
                    &envelope.facts.first().ok_or("missing source fact")?.payload,
                )
                .map_err(|e| e.to_string())?;
                let fact = statement
                    .facts
                    .first_mut()
                    .ok_or("empty source statement")?;
                let issuer_key = self
                    .source_keys
                    .get(&fact.issuer)
                    .ok_or("unknown source issuer")?;
                match fault {
                    Fault::Issuer => fact.issuer = "other".into(),
                    Fault::Subject => fact.subject = "other".into(),
                    Fault::Audience => fact.audience = "other".into(),
                    Fault::Source => fact.source = "other".into(),
                    Fault::Value => fact.value = "other".into(),
                    Fault::FactGeneration => {
                        fact.generation = fact
                            .generation
                            .checked_add(1)
                            .ok_or("fact generation exhausted")?
                    }
                    Fault::Claimed => fact.origin = Origin::Claimed,
                    _ => unreachable!(),
                }
                envelope.facts[0] = sign(&statement, issuer_key)?;
            }
            Fault::Review => envelope.review.report = "other".into(),
            Fault::Policy => envelope.review.after = "other".into(),
            Fault::Schema => envelope.review.schema = "other".into(),
            Fault::SourceRevision => envelope.review.source = "other".into(),
            Fault::Epoch => {
                envelope.review.epoch = envelope
                    .review
                    .epoch
                    .checked_add(1)
                    .ok_or("review epoch exhausted")?
            }
            Fault::Resource => envelope.effect.object = "other".into(),
            Fault::ResourceGeneration => {
                envelope.effect.generation = envelope
                    .effect
                    .generation
                    .checked_add(1)
                    .ok_or("object generation exhausted")?
            }
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
