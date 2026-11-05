//! Offline, process-local Host execution for a tool-using language-model system.

use cedar_poo_agentic::boundary::SelectionDelta;
use cedar_poo_core::authority_consumption::{AuthorityGrant, AuthorityId, AuthorityLedger};
use cedar_poo_core::operation_identity::OperationId;
use cedar_poo_disclosure_host::{
    DispatchOutcome, Effect, Evidence, Grant, InMemoryDisclosureHost, RecipientGrant,
    ValidatedDisclosurePolicy,
};
use cedar_poo_runtime::ValidatedManifest;
use serde_json::json;
use std::{env, fs, process, sync::Arc, thread};

const HOSPITAL: &str = "Dataset::\"hospital-patients\"";
const RESEARCH: &str = "Dataset::\"research-patients\"";
const SINK: &str = "DisclosureSink::\"study-workspace\"";
const STEWARD: &str = "Actor::\"clinical-steward\"";
const AGENT: &str = "Actor::\"analytics-agent\"";
const ACTION: &str = "Action::\"publish-derived-result\"";

fn grant(source: &str) -> Grant {
    Grant {
        issuer: STEWARD.into(),
        grantee: AGENT.into(),
        action: ACTION.into(),
        source: source.into(),
        destination: SINK.into(),
        purpose: "study-one".into(),
        revision: 0,
        expires_at: 10,
    }
}

fn evidence() -> Evidence {
    Evidence {
        epoch: 0,
        policy_revision: 0,
        approval_revision: 0,
        delegation_revision: 0,
        audience_revision: 0,
        now: 1,
        budget: 2,
        trusted_sources: vec![HOSPITAL.into(), RESEARCH.into()],
        trusted_owner: STEWARD.into(),
        allowed_destinations: vec![SINK.into()],
        current_recipients: vec!["researcher-a".into()],
        recipient_grants: [HOSPITAL, RESEARCH]
            .map(|source| RecipientGrant {
                source: source.into(),
                recipient: "researcher-a".into(),
            })
            .to_vec(),
        observed_digest: "cohort-first".into(),
        observed_candidate_ids: ["p1", "p2", "p3", "p4"].map(str::to_owned).to_vec(),
        observed_selection_delta: None,
        approvals: vec![grant(HOSPITAL), grant(RESEARCH)],
        delegations: vec![grant(HOSPITAL), grant(RESEARCH)],
        possible_ids: (1..=6).map(|n| format!("p{n}")).collect(),
        minimum_cohort: 3,
        audit_ready: true,
    }
}

fn effect(operation_id: &str, digest: &str, channel: &str, candidates: &[&str]) -> Effect {
    Effect {
        operation_id: OperationId::from(operation_id),
        sources: vec![HOSPITAL.into(), RESEARCH.into()],
        destination: SINK.into(),
        purpose: "study-one".into(),
        channel: channel.into(),
        recipients: vec!["researcher-a".into()],
        payload_digest: digest.into(),
        candidate_ids: candidates.iter().map(|id| (*id).into()).collect(),
        selection_delta: None,
    }
}

fn authority(first: &Effect, independent: &Effect, second: &Effect) -> AuthorityLedger<Effect> {
    AuthorityLedger {
        grants: [
            ("approval-first", first),
            ("approval-retry", first),
            ("approval-independent", independent),
            ("approval-second", second),
        ]
        .into_iter()
        .map(|(id, effect)| AuthorityGrant {
            id: AuthorityId::from(id),
            effect: effect.clone(),
            max_uses: 1,
            used: 0,
        })
        .collect(),
    }
}

fn run() -> Result<(), String> {
    let path = env::args().nth(1).ok_or("expected Lean manifest path")?;
    let manifest: ValidatedManifest =
        serde_json::from_slice(&fs::read(path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    let policy = ValidatedDisclosurePolicy::from_manifest(&manifest)?;
    let first = effect(
        "release-one",
        "cohort-first",
        "workspace",
        &["p1", "p2", "p3", "p4"],
    );
    let independent = effect(
        "release-independent",
        "cohort-first",
        "workspace",
        &["p1", "p2", "p3", "p4"],
    );
    let second = effect(
        "release-two",
        "cohort-second",
        "message",
        &["p3", "p4", "p5", "p6"],
    );
    let host = InMemoryDisclosureHost::new(
        &policy,
        evidence(),
        authority(&first, &independent, &second),
    );
    let ticket = host
        .prepare(AuthorityId::from("approval-first"), first.clone())?
        .ok_or("first release was denied")?;
    let stale = host
        .prepare(AuthorityId::from("approval-first"), first.clone())?
        .ok_or("racing prepare was denied")?;
    let mut changed_channel = first.clone();
    changed_channel.channel = "message".into();
    if host.commit(ticket.clone(), &changed_channel)?.is_some() {
        return Err("changed channel consumed the ticket".into());
    }
    let receipt = host
        .commit(ticket, &first)?
        .ok_or("first commit was denied")?;
    if host.commit(stale, &first)?.is_some() {
        return Err("stale racing ticket committed".into());
    }
    let fresh_reissue_denied = host
        .prepare(AuthorityId::from("approval-first"), first.clone())?
        .is_none();
    if !fresh_reissue_denied
        || host.authority_used(&AuthorityId::from("approval-first"))? != Some(1)
    {
        return Err("a fresh ticket reused the consumed approval".into());
    }

    let cross_approval_replay_denied = host
        .prepare(AuthorityId::from("approval-retry"), first.clone())?
        .is_none()
        && host.authority_used(&AuthorityId::from("approval-retry"))? == Some(0)
        && host.operation_admitted(&OperationId::from("release-one"))?;
    if !cross_approval_replay_denied {
        return Err("a new approval replayed the same workflow operation".into());
    }

    let separate = InMemoryDisclosureHost::new(
        &policy,
        evidence(),
        authority(&first, &independent, &second),
    );
    let first_independent = separate
        .prepare(AuthorityId::from("approval-first"), first.clone())?
        .ok_or("first independent preparation denied")?;
    separate
        .commit(first_independent, &first)?
        .ok_or("first independent commit denied")?;
    let other_ticket = separate
        .prepare(
            AuthorityId::from("approval-independent"),
            independent.clone(),
        )?
        .ok_or("distinct approval preparation denied")?;
    let distinct_approval_accepted = separate.commit(other_ticket, &independent)?.is_some()
        && separate.authority_used(&AuthorityId::from("approval-independent"))? == Some(1);
    if !distinct_approval_accepted {
        return Err("distinct approval could not use remaining budget".into());
    }

    let concurrent = Arc::new(InMemoryDisclosureHost::new(
        &policy,
        evidence(),
        authority(&first, &independent, &second),
    ));
    let prepared = (0..2)
        .map(|_| {
            concurrent
                .prepare(AuthorityId::from("approval-first"), first.clone())?
                .ok_or_else(|| "parallel prepare denied".to_owned())
        })
        .collect::<Result<Vec<_>, String>>()?;
    let start = Arc::new(std::sync::Barrier::new(2));
    let attempts = prepared
        .into_iter()
        .map(|ticket| {
            let host = Arc::clone(&concurrent);
            let start = Arc::clone(&start);
            let effect = first.clone();
            thread::spawn(move || {
                start.wait();
                host.commit(ticket, &effect)
            })
        })
        .collect::<Vec<_>>();
    let mut committed_parallel = 0;
    for attempt in attempts {
        if attempt
            .join()
            .map_err(|_| "parallel commit panicked")??
            .is_some()
        {
            committed_parallel += 1;
        }
    }
    let concurrent_audit_count = concurrent.audit()?.len();
    let concurrent_single_commit = committed_parallel == 1 && concurrent_audit_count == 1;
    if !concurrent_single_commit {
        return Err(format!(
            "parallel commits were not serialized: committed={committed_parallel} audit={concurrent_audit_count}"
        ));
    }
    host.observe_output(
        "cohort-second".into(),
        ["p3", "p4", "p5", "p6"].map(str::to_owned).to_vec(),
    )?;
    let cumulative_denied = host
        .prepare(AuthorityId::from("approval-second"), second.clone())?
        .is_none();
    if !cumulative_denied || host.audit()?.len() != 1 {
        return Err("cross-channel cumulative release was not denied".into());
    }

    let alone = InMemoryDisclosureHost::new(
        &policy,
        Evidence {
            observed_digest: "cohort-second".into(),
            observed_candidate_ids: ["p3", "p4", "p5", "p6"].map(str::to_owned).to_vec(),
            ..evidence()
        },
        authority(&first, &independent, &second),
    );
    let second_alone_allowed = alone
        .prepare(AuthorityId::from("approval-second"), second.clone())?
        .is_some();
    if !second_alone_allowed {
        return Err("independent second release was denied".into());
    }

    // Both channels see the same authenticated result and shared ledger revision.
    let mut alternate = independent.clone();
    alternate.channel = "message".into();
    for workspace_first in [true, false] {
        let shared = InMemoryDisclosureHost::new(
            &policy,
            evidence(),
            authority(&first, &alternate, &second),
        );
        let separate_scope = InMemoryDisclosureHost::new(
            &policy,
            evidence(),
            authority(&first, &alternate, &second),
        );
        let workspace = shared
            .prepare(AuthorityId::from("approval-first"), first.clone())?
            .ok_or("workspace preparation denied")?;
        let message = shared
            .prepare(AuthorityId::from("approval-independent"), alternate.clone())?
            .ok_or("message preparation denied")?;
        if separate_scope.commit(workspace.clone(), &first)?.is_some() {
            return Err("foreign observer scope accepted a prepared ticket".into());
        }
        let (winner, effect, loser, other) = if workspace_first {
            (workspace, &first, message, &alternate)
        } else {
            (message, &alternate, workspace, &first)
        };
        if shared.commit(winner, effect)?.is_none()
            || shared.commit(loser, other)?.is_some()
            || shared.audit()?.len() != 1
        {
            return Err("cross-channel tickets did not share one deciding revision".into());
        }
    }

    let mut replan = first.clone();
    replan.channel = "message".into();
    let ambiguous =
        InMemoryDisclosureHost::new(&policy, evidence(), authority(&first, &replan, &second));
    let original = ambiguous
        .prepare(AuthorityId::from("approval-first"), first.clone())?
        .ok_or("dispatch preparation denied")?;
    let retry = ambiguous
        .prepare(AuthorityId::from("approval-independent"), replan.clone())?
        .ok_or("alternative channel was not initially eligible")?;
    let mut sends = 0;
    let dispatched = ambiguous.commit_and_dispatch(original, &first, |actual| {
        assert_eq!(actual, &first);
        sends += 1;
        Err("simulated lost provider reply".into())
    })?;
    if !matches!(dispatched, Some(DispatchOutcome::Unknown(receipt)) if receipt.remaining_budget == 1)
        || ambiguous
            .commit_and_dispatch(retry, &replan, |_| {
                sends += 1;
                Ok(())
            })?
            .is_some()
        || ambiguous
            .prepare(AuthorityId::from("approval-independent"), replan)?
            .is_some()
        || ambiguous.authority_used(&AuthorityId::from("approval-independent"))? != Some(0)
        || ambiguous.audit()?.len() != 1
        || sends != 1
    {
        return Err("lost reply allowed a second send or changed the original charge".into());
    }

    #[cfg(all(unix, feature = "recovery-replay"))]
    check_restarted_dispatch(&policy, &first)?;

    let first_delta = SelectionDelta {
        before: (1..=6).map(|n| format!("p{n}")).collect(),
        after: ["p1", "p2", "p3", "p4"].map(str::to_owned).to_vec(),
    };
    let second_delta = SelectionDelta {
        before: (1..=6).map(|n| format!("p{n}")).collect(),
        after: ["p3", "p4", "p5", "p6"].map(str::to_owned).to_vec(),
    };
    let first_selection = Effect {
        selection_delta: Some(first_delta.clone()),
        ..effect(
            "selection-first",
            "selection-first",
            "workspace",
            &["p1", "p2", "p3", "p4"],
        )
    };
    let second_selection = Effect {
        selection_delta: Some(second_delta.clone()),
        ..effect(
            "selection-second",
            "selection-second",
            "message",
            &["p3", "p4", "p5", "p6"],
        )
    };
    let selection_authority = AuthorityLedger {
        grants: [
            (&first_selection, "approval-selection-first"),
            (&second_selection, "approval-selection-second"),
        ]
        .into_iter()
        .map(|(effect, id)| AuthorityGrant {
            id: AuthorityId::from(id),
            effect: effect.clone(),
            max_uses: 1,
            used: 0,
        })
        .collect(),
    };
    let selection_host = InMemoryDisclosureHost::new(&policy, evidence(), selection_authority);
    let unobserved_selection_denied = selection_host
        .prepare(
            AuthorityId::from("approval-selection-first"),
            first_selection.clone(),
        )?
        .is_none();
    selection_host.observe_selection("selection-first".into(), first_delta)?;
    let selection_ticket = selection_host
        .prepare(
            AuthorityId::from("approval-selection-first"),
            first_selection.clone(),
        )?
        .ok_or("observed selection was denied")?;
    let selection_receipt = selection_host
        .commit(selection_ticket, &first_selection)?
        .ok_or("observed selection commit was denied")?;
    selection_host.observe_selection("selection-second".into(), second_delta)?;
    let cumulative_selection_denied = selection_host
        .prepare(
            AuthorityId::from("approval-selection-second"),
            second_selection,
        )?
        .is_none();
    if !unobserved_selection_denied
        || !selection_receipt.selection_mutation
        || !cumulative_selection_denied
        || selection_host.audit()?.len() != 1
    {
        return Err("selection mutation bypassed observation or cumulative state".into());
    }

    let revoked = InMemoryDisclosureHost::new(
        &policy,
        evidence(),
        authority(&first, &independent, &second),
    );
    let before_revoke = revoked
        .prepare(AuthorityId::from("approval-first"), first.clone())?
        .ok_or("revoke prepare was denied")?;
    revoked.revoke_delegation()?;
    let revoke_denied = revoked.commit(before_revoke, &first)?.is_none();
    if !revoke_denied || !revoked.audit()?.is_empty() {
        return Err("revoked delegation committed".into());
    }

    let changed_audience = InMemoryDisclosureHost::new(
        &policy,
        evidence(),
        authority(&first, &independent, &second),
    );
    let audience_ticket = changed_audience
        .prepare(AuthorityId::from("approval-first"), first.clone())?
        .ok_or("audience prepare was denied")?;
    changed_audience.replace_audience(vec!["researcher-a".into(), "outsider".into()])?;
    let audience_change_denied = changed_audience.commit(audience_ticket, &first)?.is_none()
        && changed_audience
            .prepare(AuthorityId::from("approval-first"), first.clone())?
            .is_none()
        && changed_audience.audit()?.is_empty();
    if !audience_change_denied {
        return Err("expanded audience accepted an old or new ticket".into());
    }
    let revoked_recipient = InMemoryDisclosureHost::new(
        &policy,
        evidence(),
        authority(&first, &independent, &second),
    );
    let recipient_ticket = revoked_recipient
        .prepare(AuthorityId::from("approval-first"), first.clone())?
        .ok_or("recipient revocation prepare was denied")?;
    if !revoked_recipient.revoke_recipient_grant(RESEARCH, "researcher-a")? {
        return Err("research recipient grant was missing before revocation".into());
    }
    let recipient_revocation_denied = revoked_recipient
        .commit(recipient_ticket, &first)?
        .is_none()
        && revoked_recipient
            .prepare(AuthorityId::from("approval-first"), first.clone())?
            .is_none()
        && revoked_recipient.audit()?.is_empty();
    if !recipient_revocation_denied {
        return Err("revoked source recipient grant accepted an old or new ticket".into());
    }
    let mut missing_recipient_grant = evidence();
    missing_recipient_grant.recipient_grants.pop();
    let missing_recipient_grant_denied = InMemoryDisclosureHost::new(
        &policy,
        missing_recipient_grant,
        authority(&first, &independent, &second),
    )
    .prepare(AuthorityId::from("approval-first"), first.clone())?
    .is_none();
    if !missing_recipient_grant_denied {
        return Err("missing source recipient grant was accepted".into());
    }

    let failed_audit = InMemoryDisclosureHost::new(
        &policy,
        evidence(),
        authority(&first, &independent, &second),
    );
    let before_failure = failed_audit
        .prepare(AuthorityId::from("approval-first"), first.clone())?
        .ok_or("audit prepare was denied")?;
    failed_audit.set_audit_ready(false)?;
    let audit_failure_denied = failed_audit.commit(before_failure, &first)?.is_none();
    if !audit_failure_denied
        || !failed_audit.audit()?.is_empty()
        || failed_audit.authority_used(&AuthorityId::from("approval-first"))? != Some(0)
    {
        return Err("audit failure committed".into());
    }

    let mut wrong_issuer = evidence();
    wrong_issuer.approvals[0].issuer = "Actor::\"other-steward\"".into();
    let wrong_issuer_denied = InMemoryDisclosureHost::new(
        &policy,
        wrong_issuer,
        authority(&first, &independent, &second),
    )
    .prepare(AuthorityId::from("approval-first"), first.clone())?
    .is_none();
    if !wrong_issuer_denied {
        return Err("wrong grant issuer was accepted".into());
    }

    let mut substituted_candidates = evidence();
    substituted_candidates.observed_candidate_ids = ["p1", "p2"].map(str::to_owned).to_vec();
    let candidate_substitution_denied = InMemoryDisclosureHost::new(
        &policy,
        substituted_candidates,
        authority(&first, &independent, &second),
    )
    .prepare(AuthorityId::from("approval-first"), first.clone())?
    .is_none();
    if !candidate_substitution_denied {
        return Err("proposed candidate set overrode observed output".into());
    }

    let mut duplicate_authority = authority(&first, &independent, &second);
    duplicate_authority
        .grants
        .push(duplicate_authority.grants[0].clone());
    let duplicate_approval_denied =
        InMemoryDisclosureHost::new(&policy, evidence(), duplicate_authority)
            .prepare(AuthorityId::from("approval-first"), first.clone())?
            .is_none();
    if !duplicate_approval_denied {
        return Err("duplicate approval ID was accepted".into());
    }

    println!(
        "{}",
        json!({
            "committed": receipt,
            "secondAloneAllowed": second_alone_allowed,
            "cumulativeSecondDenied": cumulative_denied,
            "concurrentSingleCommit": concurrent_single_commit,
            "freshReissueDenied": fresh_reissue_denied,
            "crossApprovalReplayDenied": cross_approval_replay_denied,
            "distinctApprovalAccepted": distinct_approval_accepted,
            "duplicateApprovalDenied": duplicate_approval_denied,
            "revokedDenied": revoke_denied,
            "audienceChangeDenied": audience_change_denied,
            "recipientRevocationDenied": recipient_revocation_denied,
            "missingRecipientGrantDenied": missing_recipient_grant_denied,
            "auditFailureDenied": audit_failure_denied,
            "wrongIssuerDenied": wrong_issuer_denied,
            "candidateSubstitutionDenied": candidate_substitution_denied,
            "unobservedSelectionDenied": unobserved_selection_denied,
            "cumulativeSelectionDenied": cumulative_selection_denied,
            "crossChannelRevisionSerialized": true,
            "lostReplyCrossChannelRetryDenied": true,
            "restartReconciliationAndFencing": cfg!(all(unix, feature = "recovery-replay")),
            "auditEntries": host.audit()?.len(),
        })
    );
    Ok(())
}

#[cfg(all(unix, feature = "recovery-replay"))]
fn check_restarted_dispatch(
    policy: &ValidatedDisclosurePolicy,
    first: &Effect,
) -> Result<(), String> {
    use cedar_poo_disclosure_host::{
        DisclosureOutcome, DisclosureReceiver, PersistentDisclosureHost, ReceiverCut,
    };
    use cedar_poo_runtime::gateway::{Signed, verify};
    use p256::ecdsa::{Signature, SigningKey, signature::Signer};

    let path = env::temp_dir().join(format!("cedar-disclosure-restart-{}", process::id()));
    let sender_path = path.join("sender");
    let receiver_path = path.join("receiver");
    fs::create_dir(&path).map_err(|e| e.to_string())?;
    let result = (|| {
        fs::create_dir(&sender_path).map_err(|e| e.to_string())?;
        fs::create_dir(&receiver_path).map_err(|e| e.to_string())?;
        let mut replan = first.clone();
        replan.channel = "message".into();
        let mut delayed = first.clone();
        delayed.operation_id = OperationId::from("delayed-operation");
        let mut uncertain = first.clone();
        uncertain.operation_id = OperationId::from("effect-without-durable-receipt");
        let approval = |id| AuthorityId::from(id);
        let cut = ReceiverCut {
            scope: "study-observers".into(),
            generation: 7,
        };
        assert!(PersistentDisclosureHost::open(&sender_path, policy).is_err());
        assert!(DisclosureReceiver::open(&receiver_path).is_err());
        let mut grants = authority(first, &replan, &delayed);
        grants.grants.push(AuthorityGrant {
            id: approval("approval-uncertain"),
            effect: uncertain.clone(),
            max_uses: 1,
            used: 0,
        });
        PersistentDisclosureHost::initialize(
            &sender_path,
            policy,
            Evidence {
                budget: 3,
                ..evidence()
            },
            grants,
        )?;
        DisclosureReceiver::initialize(&receiver_path, &cut)?;
        let stale_sender = path.join("stale-sender");
        let stale_receiver = path.join("stale-receiver");
        copy_replica(&sender_path, &stale_sender)?;
        copy_replica(&receiver_path, &stale_receiver)?;
        let receiver = DisclosureReceiver::open(&receiver_path)?;
        let mut sends = 0;
        let provider = SigningKey::from_slice(&[11; 32]).map_err(|e| e.to_string())?;
        let foreign = SigningKey::from_slice(&[12; 32]).map_err(|e| e.to_string())?;
        let key = provider.verifying_key().to_encoded_point(false);
        let sign = |payload: Vec<u8>| {
            let signature: Signature = provider.sign(&payload);
            Signed {
                payload,
                signature: signature.to_bytes().to_vec(),
            }
        };
        let sign_outcome = |binding: &cedar_poo_disclosure_host::DispatchBinding| {
            serde_json::to_vec(&DisclosureOutcome {
                domain: DisclosureOutcome::DOMAIN.into(),
                binding: binding.clone(),
                delivered: true,
            })
            .map(sign)
            .map_err(|e| e.to_string())
        };
        {
            let sender = PersistentDisclosureHost::open(&sender_path, policy)?;
            let ticket = sender
                .prepare(approval("approval-first"), first.clone())?
                .ok_or("initial persistent dispatch denied")?;
            let competing = PersistentDisclosureHost::open(&sender_path, policy)?;
            let stale = competing
                .prepare(approval("approval-independent"), replan.clone())?
                .ok_or("competing channel did not prepare before reservation")?;
            // A staging failure occurs after the candidate image is computed.
            // No part of that image or external effect may become visible.
            let staged = sender_path.join("sender.staged");
            fs::create_dir(&staged).map_err(|e| e.to_string())?;
            assert!(
                sender
                    .commit_and_dispatch(ticket.clone(), first, cut.clone(), |_, _| {
                        sends += 1;
                        Ok(())
                    })
                    .is_err()
            );
            let unchanged = PersistentDisclosureHost::open(&sender_path, policy)?;
            assert!(unchanged.audit()?.is_empty());
            assert_eq!(
                unchanged.approval_used(&approval("approval-first"))?,
                Some(0)
            );
            assert_eq!(sends, 0);
            fs::remove_dir(&staged).map_err(|e| e.to_string())?;
            let result =
                sender.commit_and_dispatch(ticket, first, cut.clone(), |binding, actual| {
                    assert!(
                        receiver
                            .receive(binding, actual, key.as_bytes(), |_| {
                                sends += 1;
                                sign_outcome(binding)
                            })?
                            .is_some()
                    );
                    Err("lost provider reply".into())
                })?;
            assert!(matches!(result, Some(DispatchOutcome::Unknown(_))));
            assert!(
                competing
                    .commit_and_dispatch(stale, &replan, cut.clone(), |_, _| {
                        sends += 1;
                        Ok(())
                    })?
                    .is_none()
            );
        }

        // An uncommitted staged write cannot replace the live image on reopen.
        fs::write(sender_path.join("sender.staged"), b"partial").map_err(|e| e.to_string())?;
        let restarted = PersistentDisclosureHost::open(&sender_path, policy)?;
        let audit = restarted.audit()?;
        assert_eq!(audit.len(), 1);
        assert_eq!(audit[0].remaining_budget, 2);
        assert_eq!(audit[0].remaining_candidates, 4);
        assert_eq!(audit[0].operation_id, first.operation_id.0);
        assert_eq!(
            restarted.approval_used(&approval("approval-first"))?,
            Some(1)
        );
        assert_eq!(
            restarted.approval_used(&approval("approval-independent"))?,
            Some(0)
        );
        assert!(
            restarted
                .prepare(approval("approval-independent"), replan.clone())?
                .is_none()
        );

        drop(receiver);
        let receiver = DisclosureReceiver::open(&receiver_path)?;
        let signed = receiver
            .outcome(&first.operation_id, key.as_bytes())?
            .ok_or("provider lost acknowledged signed receipt after reopen")?;
        assert!(
            receiver
                .outcome(
                    &first.operation_id,
                    foreign.verifying_key().to_encoded_point(false).as_bytes()
                )
                .is_err()
        );
        let outcome: DisclosureOutcome = verify(&signed, provider.verifying_key())?;
        assert!(
            receiver
                .receive(&outcome.binding, first, key.as_bytes(), |_| {
                    sends += 1;
                    Err("duplicate reached the effect".into())
                })?
                .is_none()
        );
        let staged = sender_path.join("sender.staged");
        fs::remove_file(&staged).map_err(|e| e.to_string())?;
        fs::create_dir(&staged).map_err(|e| e.to_string())?;
        assert!(
            restarted
                .reconcile(&first.operation_id, &signed, key.as_bytes())
                .is_err()
        );
        assert_eq!(restarted.audit()?.len(), 1);
        fs::remove_dir(&staged).map_err(|e| e.to_string())?;
        // This replica has the correct admission revision and reservation,
        // but was copied before the independently accepted settlement.
        let unsettled_sender = path.join("unsettled-sender");
        copy_replica(&sender_path, &unsettled_sender)?;
        assert!(restarted.reconcile(&first.operation_id, &signed, key.as_bytes())?);
        let mut conflict = serde_json::to_value(&outcome).map_err(|e| e.to_string())?;
        conflict["delivered"] = json!(false);
        let conflict = sign(serde_json::to_vec(&conflict).map_err(|e| e.to_string())?);
        let settled = PersistentDisclosureHost::open(&sender_path, policy)?;
        assert_eq!(
            settled
                .reconcile(&first.operation_id, &conflict, key.as_bytes())
                .err()
                .as_deref(),
            Some("conflicting authenticated provider settlement")
        );
        assert!(settled.reconcile(&first.operation_id, &signed, key.as_bytes())?);

        assert!(
            restarted
                .reconcile(
                    &first.operation_id,
                    &signed,
                    foreign.verifying_key().to_encoded_point(false).as_bytes()
                )
                .is_err()
        );
        let mut altered = serde_json::to_value(&outcome).map_err(|e| e.to_string())?;
        altered["binding"]["effect"] = json!("different observed effect");
        let altered = sign(serde_json::to_vec(&altered).map_err(|e| e.to_string())?);
        assert!(
            restarted
                .reconcile(&first.operation_id, &altered, key.as_bytes())
                .is_err()
        );
        assert!(
            restarted
                .prepare(approval("approval-independent"), replan)?
                .is_none()
        );
        assert_eq!(restarted.audit()?.len(), 1);

        let next = ReceiverCut {
            generation: 8,
            ..cut.clone()
        };
        receiver.advance(&next)?;
        let stale_cut = serde_json::to_vec(&cut).map_err(|e| e.to_string())?;
        fs::write(receiver_path.join("receiver.staged"), stale_cut).map_err(|e| e.to_string())?;
        drop(receiver);
        let receiver = DisclosureReceiver::open(&receiver_path)?;
        let sender_point = restarted.recovery_point()?;
        assert!(
            PersistentDisclosureHost::open_failover(&unsettled_sender, policy, &sender_point)
                .is_err()
        );

        let receiver_point = receiver.recovery_point()?;
        assert!(
            PersistentDisclosureHost::open_failover(&stale_sender, policy, &sender_point).is_err()
        );
        assert!(DisclosureReceiver::open_failover(&stale_receiver, &receiver_point).is_err());

        let promoted_sender = path.join("promoted-sender");
        let promoted_receiver = path.join("promoted-receiver");
        let missing_receipt = path.join("missing-receipt");
        copy_replica(&sender_path, &promoted_sender)?;
        copy_replica(&receiver_path, &promoted_receiver)?;
        copy_replica(&receiver_path, &missing_receipt)?;
        let receipt_hash = cedar_poo_runtime::gateway_source_sha256(&first.operation_id.0)?;
        fs::remove_file(missing_receipt.join(format!("outcome-{receipt_hash}.json")))
            .map_err(|e| e.to_string())?;
        assert!(DisclosureReceiver::open_failover(&missing_receipt, &receiver_point).is_err());

        drop(receiver);
        drop(restarted);
        drop(settled);
        let sender_path = promoted_sender;
        let receiver_path = promoted_receiver;
        let restarted =
            PersistentDisclosureHost::open_failover(&sender_path, policy, &sender_point)?;
        let reopened = DisclosureReceiver::open_failover(&receiver_path, &receiver_point)?;
        let recovered = reopened
            .outcome(&first.operation_id, key.as_bytes())?
            .ok_or("promoted receiver lost the signed outcome")?;
        assert_eq!(recovered.payload, signed.payload);
        assert_eq!(recovered.signature, signed.signature);
        let mut alternate_channel = first.clone();
        alternate_channel.channel = "message".into();
        assert!(
            restarted
                .prepare(approval("approval-independent"), alternate_channel)?
                .is_none()
        );
        assert!(
            restarted
                .reconcile(&first.operation_id, &conflict, key.as_bytes())
                .is_err()
        );
        assert!(restarted.reconcile(&first.operation_id, &recovered, key.as_bytes())?);
        assert!(reopened.advance(&cut).is_err());
        let delayed_ticket = restarted
            .prepare(approval("approval-second"), delayed.clone())?
            .ok_or("recovered sender lost the remaining budget or distinct approval")?;
        let result =
            restarted.commit_and_dispatch(delayed_ticket, &delayed, cut, |binding, actual| {
                assert!(
                    reopened
                        .receive(binding, actual, key.as_bytes(), |_| {
                            sends += 1;
                            Err("retired cut reached the effect".into())
                        })?
                        .is_none()
                );
                Err("receiver rejected retired cut".into())
            })?;
        assert!(
            matches!(result, Some(DispatchOutcome::Unknown(receipt)) if receipt.remaining_budget == 1)
        );
        assert_eq!(sends, 1);
        let latest = PersistentDisclosureHost::open(&sender_path, policy)?;
        assert_eq!(latest.audit()?.len(), 2);
        assert!(
            latest
                .reconcile(&first.operation_id, &conflict, key.as_bytes())
                .is_err()
        );
        assert!(latest.reconcile(&first.operation_id, &signed, key.as_bytes())?);
        let operation = &uncertain.operation_id;
        let digest = cedar_poo_runtime::gateway_source_sha256(&operation.0)?;
        let staged = receiver_path.join(format!("outcome-{digest}.staged"));
        fs::create_dir(&staged).map_err(|e| e.to_string())?;
        let ticket = latest
            .prepare(approval("approval-uncertain"), uncertain.clone())?
            .ok_or("missing budget for receipt crash control")?;
        let failed = latest.commit_and_dispatch(ticket, &uncertain, next, |binding, actual| {
            let result = reopened.receive(binding, actual, key.as_bytes(), |_| {
                sends += 1;
                sign_outcome(binding)
            });
            assert!(result.is_err());
            let recovered = DisclosureReceiver::open(&receiver_path)?;
            assert!(recovered.outcome(operation, key.as_bytes())?.is_none());
            assert!(
                recovered
                    .receive(binding, actual, key.as_bytes(), |_| {
                        sends += 1;
                        Err("receipt failure released receiver reservation".into())
                    })?
                    .is_none()
            );
            Err("provider receipt persistence failed after effect".into())
        })?;
        assert!(
            matches!(failed, Some(DispatchOutcome::Unknown(receipt)) if receipt.remaining_budget == 0)
        );
        assert_eq!(sends, 2);
        let pending_point = reopened.recovery_point()?;
        let missing_reservation = path.join("missing-reservation");
        copy_replica(&receiver_path, &missing_reservation)?;
        fs::remove_file(missing_reservation.join(digest)).map_err(|e| e.to_string())?;
        assert!(DisclosureReceiver::open_failover(&missing_reservation, &pending_point).is_err());
        Ok(())
    })();
    let cleanup = fs::remove_dir_all(path).map_err(|e| e.to_string());
    result.and(cleanup)
}

#[cfg(all(unix, feature = "recovery-replay"))]
fn copy_replica(source: &std::path::Path, destination: &std::path::Path) -> Result<(), String> {
    fs::create_dir(destination).map_err(|e| e.to_string())?;
    for entry in fs::read_dir(source).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        if entry.file_type().map_err(|e| e.to_string())?.is_file() {
            fs::copy(entry.path(), destination.join(entry.file_name()))
                .map_err(|e| e.to_string())?;
        }
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        process::exit(1);
    }
}
