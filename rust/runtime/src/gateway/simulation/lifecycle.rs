//! Trusted simulated fact writers and sticky revocation share the deciding lock.
use super::{Current, Simulator, field_inventory};
use crate::gateway::wire::sign;
use crate::gateway::{FactAuthority, FactBinding, FactStatement, Origin, Signed, Version};
use crate::{Case, ReplayReceipt, ValidatedProgram, json_sha256};
use cedar_poo_core::JsonSourceIdentity;
use p256::ecdsa::SigningKey;
use serde::Serialize;
use std::{collections::BTreeMap, sync::Arc};

/// Read-only observation; neither a checkpoint nor an execution capability.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LifecycleView {
    pub generation: u64,
    pub fact_generation: u64,
    pub sources_current: bool,
    pub now: u64,
    pub revoked: bool,
    pub spent: bool,
    pub unknown: bool,
    pub publication_unknown: bool,
    pub policy_epoch: u64,
    pub cedar_allowed: bool,
    pub world: String,
    pub mediator_current: bool,
}
pub(super) struct SourceWindow {
    pub generation: u64,
    pub now: u64,
    pub expires_at: u64,
}
struct RefreshSnapshot {
    generation: u64,
    fact_generation: u64,
    program: Option<ValidatedProgram>,
    now: u64,
    payload: String,
}
pub(super) struct Sources {
    pub generation: u64,
    pub authority: FactAuthority,
    pub facts: Vec<Signed>,
    pub world: String,
}
pub(super) fn prepare_facts(
    case: &Case,
    keys: &BTreeMap<String, SigningKey>,
    window: SourceWindow,
) -> Result<Sources, String> {
    if window.expires_at <= window.now {
        return Err("source lease is not current".into());
    }
    let world = json_sha256(&(&case.request, &*case.entities))?;
    let facts: Vec<_> = field_inventory(case)?
        .into_iter()
        .map(|(field, value)| FactBinding {
            issuer: if field.starts_with("context/") {
                "context-authority"
            } else if field.starts_with("entity/") {
                "entity-authority"
            } else {
                "binding-authority"
            }
            .into(),
            subject: case.request.principal.clone(),
            audience: "gateway".into(),
            source: world.clone(),
            field,
            value,
            generation: window.generation,
            origin: Origin::Attested,
            not_before: window.now,
            expires_at: window.expires_at,
        })
        .collect();
    let mut statements: BTreeMap<&str, Vec<FactBinding>> = BTreeMap::new();
    for fact in &facts {
        statements
            .entry(&fact.issuer)
            .or_default()
            .push(fact.clone());
    }
    let signed = statements
        .into_iter()
        .map(|(issuer, facts)| {
            sign(
                &FactStatement {
                    version: Version { major: 1, minor: 0 },
                    facts,
                },
                &keys[issuer],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let authority = FactAuthority::new(
        facts,
        keys.iter()
            .map(|(issuer, key)| (issuer.clone(), *key.verifying_key()))
            .collect(),
        window.now,
    )?
    .prepare_sources(&signed)?;
    Ok(Sources {
        generation: window.generation,
        authority,
        facts: signed,
        world,
    })
}
impl Simulator {
    pub(super) fn check_owner(&self, current: &Current) -> Result<(), String> {
        if !Arc::ptr_eq(&self.owner, &current.active_owner) {
            return Err("retired mediation owner".into());
        }
        Ok(())
    }
    /// Observe authoritative state without granting any capability to the caller.
    pub fn lifecycle_view(&self) -> Result<LifecycleView, String> {
        let current = self.current.lock().map_err(|_| "poisoned authority")?;
        Ok(LifecycleView {
            generation: current.generation,
            fact_generation: current.fact_generation,
            sources_current: current.sources_current,
            now: current.authority.now,
            revoked: current.revoked,
            spent: current.spent,
            unknown: current.unknown,
            publication_unknown: current.publication_unknown,
            policy_epoch: current.review.epoch,
            cedar_allowed: current.cedar.error_free_allow,
            world: current.world.clone(),
            mediator_current: Arc::ptr_eq(&self.owner, &current.active_owner),
        })
    }
    /// A trusted clock writer invalidates prepared handles and refuses rollback.
    pub fn advance_time(&self, now: u64) -> Result<(), String> {
        let mut current = self.current.lock().map_err(|_| "poisoned authority")?;
        self.check_owner(&current)?;
        let next = current
            .generation
            .checked_add(1)
            .ok_or("generation exhausted")?;
        let authority = current.authority.at_time(now)?;
        current.authority = authority;
        current.generation = next;
        Ok(())
    }
    /// Terminal for this original operation; no refresh, publication or recovery clears it.
    pub fn revoke(&self) -> Result<(), String> {
        let mut current = self.current.lock().map_err(|_| "poisoned authority")?;
        self.check_owner(&current)?;
        let next = current
            .generation
            .checked_add(1)
            .ok_or("generation exhausted")?;
        current.revoked = true;
        current.pending_review = None;
        current.generation = next;
        Ok(())
    }
    /// Trusted source-adapter input, never an MCP argument. Preserve exact original
    /// request/policies and re-run the SDK for the current entity world and lease.
    pub fn refresh_facts(&self, candidate: &Case, expires_at: u64) -> Result<(), String> {
        let (generation, cedar, sources) = self.prepare_refresh(candidate, expires_at)?;
        self.install_refresh(generation, candidate, cedar, sources)
    }
    fn prepare_refresh(
        &self,
        candidate: &Case,
        expires_at: u64,
    ) -> Result<(u64, ReplayReceipt, Sources), String> {
        let snapshot = self.begin_refresh(candidate)?;
        let cedar = snapshot
            .program
            .as_ref()
            .ok_or("unqualified source refresh")?
            .replay(candidate)?
            .replay;
        if cedar.request_sha256 != snapshot.payload {
            return Err("source refresh changed the original effect".into());
        }
        let generation = snapshot
            .fact_generation
            .checked_add(1)
            .ok_or("fact generation exhausted")?;
        let sources = prepare_facts(
            candidate,
            &self.source_keys,
            SourceWindow {
                generation,
                now: snapshot.now,
                expires_at,
            },
        )?;
        Ok((snapshot.generation, cedar, sources))
    }
    fn begin_refresh(&self, candidate: &Case) -> Result<RefreshSnapshot, String> {
        let mut snapshot = self.current.lock().map_err(|_| "poisoned authority")?;
        self.check_owner(&snapshot)?;
        if candidate.name != snapshot.case.name
            || candidate.revision != snapshot.case.revision
            || candidate.request.principal != snapshot.case.request.principal
            || candidate.request.action != snapshot.case.request.action
            || candidate.request.resource != snapshot.case.request.resource
            || !candidate
                .request
                .context
                .same_source(&snapshot.case.request.context)
            || !candidate.policies.same_source(&snapshot.case.policies)
        {
            return Err(
                "fact refresh cannot replace the original request or reviewed policies".into(),
            );
        }
        let next = snapshot
            .generation
            .checked_add(1)
            .ok_or("generation exhausted")?;
        snapshot.sources_current = false;
        snapshot.pending_review = None;
        snapshot.generation = next;
        Ok(RefreshSnapshot {
            generation: snapshot.generation,
            fact_generation: snapshot.fact_generation,
            program: snapshot.program.clone(),
            now: snapshot.authority.now,
            payload: snapshot.effect.payload.clone(),
        })
    }
    fn install_refresh(
        &self,
        captured: u64,
        candidate: &Case,
        cedar: ReplayReceipt,
        sources: Sources,
    ) -> Result<(), String> {
        let mut current = self.current.lock().map_err(|_| "poisoned authority")?;
        self.check_owner(&current)?;
        if current.generation != captured {
            return Err("source preparation became stale".into());
        }
        let next = current
            .generation
            .checked_add(1)
            .ok_or("generation exhausted")?;
        let mut review = current.review.clone();
        if current.publications.is_empty() {
            review.source = sources.world.clone();
            review.report.clear();
            review.report = json_sha256(&review)?;
        }
        current.review = review;
        current.world = sources.world;
        current.case = candidate.clone();
        current.cedar = cedar;
        current.authority = sources.authority;
        current.facts = sources.facts;
        current.sources_current = true;
        current.fact_generation = sources.generation;
        current.pending_review = None;
        current.generation = next;
        Ok(())
    }
}
