//! Reconciliation from public log, source and gateway trust material.
use super::{
    Commit, FactAuthority, LogSnapshot, ProviderJournal, Receipt, Signed, Version, verify,
    verify_log,
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
}
/// External auditor entrypoint: no private signer or gateway state is required.
pub fn reconcile(
    journal: &ProviderJournal,
    receipts: &[Signed],
    snapshot: &LogSnapshot,
    authority: &AuditAuthority,
) -> Reconciliation {
    let history = verify_log(snapshot, &authority.log_key, authority.minimum_size);
    let mut report = Reconciliation {
        invalid_log: history.is_err(),
        ..Reconciliation::default()
    };
    let mut verified = BTreeMap::new();
    for signed in receipts {
        let checked = (|| {
            if report.invalid_log {
                return Err("invalid witness history".into());
            }
            let receipt: Receipt = verify(signed, &authority.gateway_key)?;
            let commit: Commit = verify(&receipt.commit, &authority.log_key)?;
            let facts = authority.facts.accepts(&receipt.facts)?;
            if commit.publications
                != receipt
                    .publications
                    .iter()
                    .map(json_sha256)
                    .collect::<Result<Vec<_>, _>>()?
            {
                return Err("publication evidence changed".into());
            }
            if receipt.publications.is_empty() {
                let mut identity = commit.review.clone();
                identity.report.clear();
                if identity.before != identity.after
                    || json_sha256(&identity)? != commit.review.report
                {
                    return Err("nonidentity effect omitted its publication evidence".into());
                }
            }
            if !receipt.publications.is_empty() {
                let trust = authority
                    .review_trust
                    .as_ref()
                    .ok_or("missing independent review trust")?;
                let last = super::verify_publications(
                    &receipt.publications,
                    &authority.gateway_key,
                    trust,
                )?
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
            if receipt.version != (Version { major: 1, minor: 0 })
                || commit.version != receipt.version
                || commit.effect != receipt.action.effect
                || !snapshot.entries.iter().any(|entry| {
                    entry.payload == receipt.commit.payload
                        && entry.signature == receipt.commit.signature
                })
            {
                return Err("unanchored outcome".into());
            }
            Ok::<_, String>(receipt)
        })();
        match checked {
            Ok(receipt) => {
                let operation = receipt.action.effect.operation.clone();
                if verified.insert(operation.clone(), receipt.action).is_some() {
                    report.duplicates.push(operation);
                }
            }
            Err(_) => report.invalid_receipts += 1,
        }
    }
    let mut seen = BTreeSet::new();
    for action in &journal.actions {
        let operation = &action.effect.operation;
        if !seen.insert(operation.clone()) {
            report.duplicates.push(operation.clone());
        }
        match verified.get(operation) {
            None => report.missing_receipts.push(operation.clone()),
            Some(receipt) if receipt != action => report.mismatched.push(operation.clone()),
            Some(_) => (),
        }
    }
    if let Ok(commits) = history {
        report
            .unresolved_precommits
            .extend(commits.into_iter().filter_map(|commit| {
                let operation = commit.effect.operation;
                let resolved = verified
                    .get(&operation)
                    .is_some_and(|receipt| journal.actions.iter().any(|action| action == receipt));
                (!resolved).then_some(operation)
            }));
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
