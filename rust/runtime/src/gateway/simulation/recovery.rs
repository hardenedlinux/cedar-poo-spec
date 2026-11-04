//! Recovery reads surviving trusted state; history cannot reconstruct live authority.
use super::{RecoveryEvidence, Simulator};
use crate::gateway::{AuditAuthority, Reconciliation, publication_matches};
use crate::value_sha256;
use std::sync::Arc;

struct RecoverySnapshot {
    generation: u64,
    review: crate::gateway::ReviewBinding,
    release_root: String,
    policies: crate::CompiledPolicyJson,
    operation: String,
    authority: crate::gateway::FactAuthority,
    retained_intent: Option<super::state::RetainedIntent>,
    witness_frontier: Option<crate::gateway::witness::WitnessFrontier>,
}

struct RecoveryStatus {
    generation: u64,
    committed: bool,
    complete: bool,
    frontier: crate::gateway::witness::WitnessFrontier,
}

impl Simulator {
    /// Recover a mediator against the surviving trusted simulation authority.
    /// Exact historical evidence can resolve an outcome, never reset live facts,
    /// revocation, mode, original consumption, publication exposure or policy epoch.
    pub fn recover(authority: &Self, evidence: RecoveryEvidence<'_>) -> Result<Self, String> {
        let checked = authority.check_recovery(evidence, None)?;
        authority.attach_recovered(checked)
    }
    /// Resolve a lost Gateway receipt from separately read, provider-signed outcomes.
    /// Original consumption and current controls survive; no effect is resent.
    pub fn recover_with_provider_outcomes(
        authority: &Self,
        evidence: RecoveryEvidence<'_>,
        outcomes: &[crate::gateway::Signed],
    ) -> Result<Self, String> {
        if !evidence.receipts.is_empty() {
            return Err("mixed Gateway and provider completion evidence".into());
        }
        let checked = authority.check_recovery(evidence, Some(outcomes))?;
        authority.attach_recovered(checked)
    }
    fn check_recovery(
        &self,
        evidence: RecoveryEvidence<'_>,
        outcomes: Option<&[crate::gateway::Signed]>,
    ) -> Result<RecoveryStatus, String> {
        let authority = self;
        let history = evidence.witness.view();
        let snapshot = {
            let current = authority.current.lock().map_err(|_| "poisoned authority")?;
            authority.check_owner(&current)?;
            // Exact ordered bytes are stronger than digest equality. Borrow the
            // retained prefix while locked instead of cloning and encoding it.
            if current.publications.len() != evidence.publications.len()
                || !current
                    .publications
                    .iter()
                    .zip(evidence.publications)
                    .all(|(a, b)| a.payload == b.payload && a.signature == b.signature)
            {
                return Err("recovery discarded or substituted current publication history".into());
            }
            RecoverySnapshot {
                generation: current.generation,
                review: current.review.clone(),
                release_root: current.release_root.clone(),
                policies: current.case.policies.clone(),
                operation: current.effect.operation.clone(),
                authority: current.authority.clone(),
                retained_intent: current.retained_intent.clone(),
                witness_frontier: current.witness_frontier.clone(),
            }
        };
        if !evidence.publications.is_empty() {
            let trust = evidence
                .audit
                .review_trust
                .as_ref()
                .ok_or("missing recovery review roots")?;
            if trust.review_key != self.review_trust.review_key
                || trust.approval_key != self.review_trust.approval_key
            {
                return Err("recovery review trust changed".into());
            }
        }
        if let Some(last) = evidence.audit.verify_publications(evidence.publications)? {
            publication_matches(&snapshot.review, &last)?;
            if last.0.after_root != snapshot.release_root
                || last.0.after != value_sha256(&snapshot.policies)?
            {
                return Err("recovery did not retain the actual installed policies".into());
            }
        }
        if evidence.audit.gateway_key != authority.verifying_key()
            || evidence.audit.log_key != evidence.witness.verifying_key()
        {
            return Err("recovery audit trust changed".into());
        }
        // The deciding writer retained the original source interpretation with
        // the exact intent. Current source renewal cannot rewrite historical
        // admission, and incoming audit configuration cannot select new roots.
        let facts = snapshot
            .retained_intent
            .as_ref()
            .map_or(&snapshot.authority, |retained| &retained.facts);
        if !facts.same_roots(&evidence.audit.facts) {
            return Err("recovery source issuer roots changed".into());
        }
        let audit = AuditAuthority {
            gateway_key: evidence.audit.gateway_key,
            log_key: evidence.audit.log_key,
            facts: facts.clone(),
            minimum_size: evidence
                .audit
                .minimum_size
                .max(evidence.witness.minimum_size()),
            independent_frontier: evidence.audit.independent_frontier.clone(),
            review_trust: evidence.audit.review_trust.clone(),
            prepared_publications: evidence.audit.prepared_publications.clone(),
        };
        let history =
            crate::gateway::witness::verify_view(history, &audit.log_key, audit.minimum_size)?;
        if let Some(frontier) = &snapshot.witness_frontier {
            history.check_frontier(frontier)?;
        }
        let retained_effect = match &snapshot.retained_intent {
            Some(retained) => {
                if retained.log_key != audit.log_key {
                    return Err("recovery witness key differs from retained intent".into());
                }
                Some(
                    &history
                        .intent(&retained.entry)
                        .ok_or("recovery omitted or substituted the retained intent")?
                        .effect,
                )
            }
            None => {
                if history
                    .records()
                    .iter()
                    .any(|commit| commit.effect.operation == snapshot.operation)
                {
                    return Err("recovery supplied an unrecorded operation intent".into());
                }
                None
            }
        };
        let report = crate::gateway::audit::reconcile_recovery(
            evidence.provider,
            outcomes.unwrap_or(evidence.receipts),
            &history,
            &audit,
            outcomes.map(|_| &self.provider_key),
            snapshot
                .retained_intent
                .as_ref()
                .map(|retained| retained.entry.as_ref()),
        );
        if report.invalid_log {
            return Err("recovery witness fails the independent history constraint".into());
        }
        let committed = retained_effect.is_some();
        let complete = retained_effect.is_some_and(|effect| {
            report == Reconciliation::default()
                && evidence
                    .provider
                    .actions
                    .iter()
                    .any(|action| &action.effect == effect)
        });
        Ok(RecoveryStatus {
            generation: snapshot.generation,
            committed,
            complete,
            frontier: history.frontier(),
        })
    }
    fn attach_recovered(&self, checked: RecoveryStatus) -> Result<Self, String> {
        let authority = self;
        let owner = Arc::new(());
        {
            let mut current = authority.current.lock().map_err(|_| "poisoned authority")?;
            authority.check_owner(&current)?;
            if current.generation != checked.generation {
                return Err("recovery observation became stale".into());
            }
            let next = current
                .generation
                .checked_add(1)
                .ok_or("generation exhausted")?;
            current.spent |= checked.committed;
            if current.spent || current.unknown {
                current.unknown = !checked.complete;
            }
            current.witness_frontier = Some(checked.frontier);
            current.pending_review = None;
            current.active_owner = Arc::clone(&owner);
            current.generation = next;
        }
        Ok(Self {
            owner,
            current: Arc::clone(&authority.current),
            source_keys: Arc::clone(&authority.source_keys),
            receipt_key: authority.receipt_key.clone(),
            provider_key: authority.provider_key,
            review_trust: authority.review_trust.clone(),
            initial: authority.initial.clone(),
        })
    }
}
