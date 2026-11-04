//! Recovery reads surviving trusted state; history cannot reconstruct live authority.
use super::{RecoveryEvidence, Simulator};
use crate::gateway::{Reconciliation, publication_matches, reconcile, verify_log};
use crate::{json_sha256, value_sha256};
use std::sync::Arc;

struct RecoveryStatus {
    generation: u64,
    committed: bool,
    complete: bool,
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
        let history = evidence.witness.snapshot();
        let records = verify_log(
            &history,
            &evidence.witness.verifying_key(),
            evidence.witness.minimum_size(),
        )?;
        let snapshot = authority
            .current
            .lock()
            .map_err(|_| "poisoned authority")?
            .clone();
        authority.check_owner(&snapshot)?;
        if json_sha256(&snapshot.publications)? != json_sha256(&evidence.publications)? {
            return Err("recovery discarded or substituted current publication history".into());
        }
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
                || last.0.after != value_sha256(&snapshot.case.policies)?
            {
                return Err("recovery did not retain the actual installed policies".into());
            }
        }
        if evidence.audit.gateway_key != authority.verifying_key()
            || evidence.audit.log_key != evidence.witness.verifying_key()
        {
            return Err("recovery audit trust changed".into());
        }
        let retained_effect = match &snapshot.retained_intent {
            Some(retained) => {
                if retained.log_key != evidence.audit.log_key {
                    return Err("recovery witness key differs from retained intent".into());
                }
                let index = history
                    .entries
                    .iter()
                    .position(|entry| {
                        entry.payload == retained.entry.payload
                            && entry.signature == retained.entry.signature
                    })
                    .ok_or("recovery omitted or substituted the retained intent")?;
                Some(
                    records
                        .get(index)
                        .ok_or("retained witness projection missing")?
                        .effect
                        .clone(),
                )
            }
            None => {
                if records
                    .iter()
                    .any(|commit| commit.effect.operation == snapshot.effect.operation)
                {
                    return Err("recovery supplied an unrecorded operation intent".into());
                }
                None
            }
        };
        drop(records);
        let report = match outcomes {
            None => reconcile(
                evidence.provider,
                evidence.receipts,
                &history,
                evidence.audit,
            ),
            Some(outcomes) => crate::gateway::reconcile_provider_outcomes(
                evidence.provider,
                outcomes,
                &history,
                crate::gateway::ProviderAuditTrust {
                    authority: evidence.audit,
                    provider_key: &self.provider_verifying_key(),
                },
            ),
        };
        if report.invalid_log {
            return Err("recovery witness is below the trusted floor".into());
        }
        let committed = retained_effect.is_some();
        let complete = retained_effect.is_some_and(|effect| {
            report == Reconciliation::default()
                && evidence
                    .provider
                    .actions
                    .iter()
                    .any(|action| action.effect == effect)
        });
        Ok(RecoveryStatus {
            generation: snapshot.generation,
            committed,
            complete,
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
