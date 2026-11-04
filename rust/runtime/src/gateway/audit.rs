//! Reconciliation from public log, source and gateway trust material.
use super::{
    Commit, FactAuthority, LogSnapshot, ProviderJournal, Receipt, Signed, Version, verify,
};
use crate::json_sha256;
use p256::ecdsa::VerifyingKey;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
/// Independent audit findings; empty lists alone do not validate an invalid log.
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct Reconciliation {
    pub unresolved_precommits: Vec<String>,
    pub missing_receipts: Vec<String>,
    pub missing_actions: Vec<String>,
    pub mismatched: Vec<String>,
    pub duplicates: Vec<String>,
    pub invalid_receipts: usize,
    pub invalid_log: bool,
}
/// Independently configured public verification material; no private key.
pub struct AuditAuthority {
    pub gateway_key: VerifyingKey,
    pub log_key: VerifyingKey,
    pub facts: FactAuthority,
    pub minimum_size: u64,
    pub review_trust: Option<super::ReviewTrust>,
    pub prepared_publications: Option<super::PreparedPublications>,
}
impl AuditAuthority {
    /// Verify an exact public prefix; prepared material never supplies an Allow.
    pub fn verify_publications(
        &self,
        records: &[Signed],
    ) -> Result<Option<(super::ReviewRecord, super::PublicationRecord)>, String> {
        if records.is_empty() {
            return Ok(None);
        }
        let trust = self
            .review_trust
            .as_ref()
            .ok_or("missing independent review trust")?;
        match &self.prepared_publications {
            Some(prepared) => prepared.verify(records, &self.gateway_key, trust),
            None => super::verify_publications(records, &self.gateway_key, trust),
        }
    }
}
struct VerifiedOutcome {
    action: super::ProviderAction,
    commit_index: usize,
}
#[derive(Clone, Copy)]
enum OutcomeSource<'a> {
    Gateway,
    Provider(&'a VerifyingKey),
}

fn verify_outcome(
    signed: &Signed,
    authority: &AuditAuthority,
    source: OutcomeSource<'_>,
) -> Result<Receipt, String> {
    match source {
        OutcomeSource::Gateway => verify(signed, &authority.gateway_key),
        OutcomeSource::Provider(key) => {
            let outcome: super::ProviderOutcome = verify(signed, key)?;
            if outcome.version != (Version { major: 1, minor: 0 })
                || outcome.domain != super::provider::PROVIDER_OUTCOME_DOMAIN
                || outcome.log_key != authority.log_key.to_encoded_point(false).as_bytes()
            {
                return Err("provider outcome domain, version or witness key differs".into());
            }
            Ok(outcome.outcome)
        }
    }
}

/// External auditor entrypoint: no private signer or gateway state is required.
pub fn reconcile(
    journal: &ProviderJournal,
    receipts: &[Signed],
    snapshot: &LogSnapshot,
    authority: &AuditAuthority,
) -> Reconciliation {
    reconcile_source(
        journal,
        receipts,
        snapshot,
        authority,
        OutcomeSource::Gateway,
        None,
    )
}

/// Independently configured provider root composed with the existing audit roots.
#[derive(Clone, Copy)]
pub struct ProviderAuditTrust<'a> {
    pub authority: &'a AuditAuthority,
    pub provider_key: &'a VerifyingKey,
}
/// Verify detached provider outcomes without any Gateway or provider private key.
/// Trust comes from the explicit provider root, not an incoming proof or journal.
pub fn reconcile_provider_outcomes(
    journal: &ProviderJournal,
    outcomes: &[Signed],
    snapshot: &LogSnapshot,
    trust: ProviderAuditTrust<'_>,
) -> Reconciliation {
    reconcile_source(
        journal,
        outcomes,
        snapshot,
        trust.authority,
        OutcomeSource::Provider(trust.provider_key),
        None,
    )
}

/// Explicit expected intent and completion channel from independently trusted setup.
pub struct IntentAuditTrust<'a> {
    pub authority: &'a AuditAuthority,
    pub intent: &'a Signed,
    pub provider_key: Option<&'a VerifyingKey>,
}
/// Audit one operation anchored to exact signed bytes in the full verified log.
/// All outcome envelopes are authenticated before excluding unrelated operations.
/// This result does not certify completion of the rest of the shared journal.
pub fn reconcile_intent(
    journal: &ProviderJournal,
    outcomes: &[Signed],
    snapshot: &LogSnapshot,
    trust: IntentAuditTrust<'_>,
) -> Reconciliation {
    reconcile_source(
        journal,
        outcomes,
        snapshot,
        trust.authority,
        trust
            .provider_key
            .map_or(OutcomeSource::Gateway, OutcomeSource::Provider),
        Some(trust.intent),
    )
}

fn reconcile_source(
    journal: &ProviderJournal,
    receipts: &[Signed],
    snapshot: &LogSnapshot,
    authority: &AuditAuthority,
    source: OutcomeSource<'_>,
    intent: Option<&Signed>,
) -> Reconciliation {
    let view = snapshot.view();
    let history = super::witness::verify_view(view, &authority.log_key, authority.minimum_size);
    reconcile_records(
        journal,
        receipts,
        view,
        authority,
        source,
        intent,
        history.as_ref().map_err(|_| ()),
    )
}

/// Recovery supplies one fully verified borrowed log; no second checkpoint,
/// signature/chain pass or detached log copy is introduced here.
pub(super) fn reconcile_recovery(
    journal: &ProviderJournal,
    receipts: &[Signed],
    history: &super::witness::VerifiedLog<'_>,
    authority: &AuditAuthority,
    provider_key: Option<&VerifyingKey>,
    intent: Option<&Signed>,
) -> Reconciliation {
    let verified = if history.key() == authority.log_key
        && history.records().len() as u64 >= authority.minimum_size
    {
        Ok(history)
    } else {
        Err(())
    };
    reconcile_records(
        journal,
        receipts,
        history.view(),
        authority,
        provider_key.map_or(OutcomeSource::Gateway, OutcomeSource::Provider),
        intent,
        verified,
    )
}

fn reconcile_records(
    journal: &ProviderJournal,
    receipts: &[Signed],
    snapshot: super::witness::LogView<'_>,
    authority: &AuditAuthority,
    source: OutcomeSource<'_>,
    intent: Option<&Signed>,
    history: Result<&super::witness::VerifiedLog<'_>, ()>,
) -> Reconciliation {
    let mut report = Reconciliation {
        invalid_log: history.is_err(),
        ..Reconciliation::default()
    };
    // Borrow complete identities; canonical positions avoid retaining another
    // signed payload per verified outcome. History validation remains mandatory.
    let anchors: BTreeMap<_, _> = snapshot
        .entries
        .iter()
        .enumerate()
        .map(|(index, entry)| {
            (
                (entry.payload.as_slice(), entry.signature.as_slice()),
                index,
            )
        })
        .collect();
    let operation = intent.and_then(|entry| {
        let index = anchors.get(&(entry.payload.as_slice(), entry.signature.as_slice()))?;
        history
            .as_ref()
            .ok()?
            .records()
            .get(*index)
            .map(|commit| commit.effect.operation.as_str())
    });
    if intent.is_some() && operation.is_none() {
        report.invalid_log = true;
    }
    let in_scope = |candidate: &str| operation.is_none_or(|expected| expected == candidate);
    let observed: BTreeSet<_> = journal
        .actions
        .iter()
        .filter(|action| in_scope(&action.effect.operation))
        .collect();
    let mut verified = BTreeMap::new();
    for signed in receipts {
        let checked = (|| {
            if report.invalid_log {
                return Err("invalid witness history".into());
            }
            let receipt = verify_outcome(signed, authority, source)?;
            let commit_index = *anchors
                .get(&(
                    receipt.commit.payload.as_slice(),
                    receipt.commit.signature.as_slice(),
                ))
                .ok_or("unanchored outcome")?;
            // The full prefix already authenticated this exact signed pair.
            // Reuse its typed metadata rather than reverify/reparse each receipt's
            // copy. Neither an operation label nor a digest is used as identity.
            let commit: &Commit = history
                .as_ref()
                .map_err(|_| "invalid witness history")?
                .records()
                .get(commit_index)
                .ok_or("missing verified commit projection")?;
            if receipt.version != (Version { major: 1, minor: 0 })
                || commit.version != receipt.version
                || commit.effect != receipt.action.effect
            {
                return Err("unanchored outcome".into());
            }
            if !in_scope(&receipt.action.effect.operation) {
                return Ok(None);
            }
            let facts = authority.facts.accepts(&receipt.facts)?;
            if facts.iter().any(|fact| fact.source != commit.current_world) {
                return Err("outcome facts do not bind its current world".into());
            }
            if commit.publications
                != receipt
                    .publications
                    .iter()
                    .map(Signed::source_sha256)
                    .collect::<Result<Vec<_>, _>>()?
            {
                return Err("publication evidence changed".into());
            }
            if receipt.publications.is_empty() {
                let mut identity = commit.review.clone();
                identity.report.clear();
                if identity.before != identity.after
                    || identity.source != commit.current_world
                    || json_sha256(&identity)? != commit.review.report
                {
                    return Err("nonidentity effect omitted its publication evidence".into());
                }
            }
            if !receipt.publications.is_empty() {
                let last = authority
                    .verify_publications(&receipt.publications)?
                    .ok_or("missing publication prefix")?;
                super::publication_matches(&commit.review, &last)?;
            }
            if commit.facts
                != facts
                    .iter()
                    .map(json_sha256)
                    .collect::<Result<Vec<_>, _>>()?
            {
                return Err("receipt fact projection changed".into());
            }
            Ok::<_, String>(Some((receipt, commit_index)))
        })();
        match checked {
            Ok(Some((receipt, commit_index))) => {
                let operation = receipt.action.effect.operation.clone();
                let outcome = VerifiedOutcome {
                    action: receipt.action,
                    commit_index,
                };
                if verified.insert(operation.clone(), outcome).is_some() {
                    report.duplicates.push(operation);
                }
            }
            Ok(None) => (),
            Err(_) => report.invalid_receipts += 1,
        }
    }
    let mut seen = BTreeSet::new();
    for action in journal
        .actions
        .iter()
        .filter(|action| in_scope(&action.effect.operation))
    {
        let operation = &action.effect.operation;
        if !seen.insert(operation.clone()) {
            report.duplicates.push(operation.clone());
        }
        match verified.get(operation) {
            None => report.missing_receipts.push(operation.clone()),
            Some(receipt) if &receipt.action != action => report.mismatched.push(operation.clone()),
            Some(_) => (),
        }
    }
    if let Ok(commits) = &history {
        let mut intents = BTreeSet::new();
        for (commit_index, commit) in commits
            .records()
            .iter()
            .enumerate()
            .filter(|(_, commit)| in_scope(&commit.effect.operation))
        {
            let operation = &commit.effect.operation;
            if !intents.insert(operation) {
                report.duplicates.push(operation.clone());
            }
            let resolved = verified.get(operation).is_some_and(|outcome| {
                outcome.action.effect == commit.effect
                    && outcome.commit_index == commit_index
                    && observed.contains(&outcome.action)
            });
            if !resolved {
                report.unresolved_precommits.push(operation.clone());
            }
        }
    }
    report
        .missing_actions
        .extend(verified.into_keys().filter(|id| !seen.contains(id)));
    for items in [
        &mut report.unresolved_precommits,
        &mut report.missing_receipts,
        &mut report.missing_actions,
        &mut report.mismatched,
        &mut report.duplicates,
    ] {
        items.sort();
        items.dedup();
    }
    report
}

#[cfg(test)]
#[path = "../../tests/unit/gateway_verified_log.rs"]
mod tests;
