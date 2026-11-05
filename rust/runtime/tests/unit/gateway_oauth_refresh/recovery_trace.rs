use super::{FirstCommit, RestartFixture, actual, settlement_race};
use crate::gateway::oauth_refresh_durable::{
    DurableEffectRecovery, DurableFinalUse, DurableRefreshLedger, EffectStatus,
};
use crate::gateway::provider_durable::{DurableReceiver, LegacyReceiverTrust, ReceiverTrust};
use crate::gateway::receipt_identity::ReceiptIdentityContext;
use crate::gateway::wire::{sign, simulation_key};
use crate::gateway::{
    AuditAuthority, FactAuthority, ProviderAuditTrust, ProviderJournal, ProviderOutcome, Signed,
    Witness, WitnessFrontier, verify,
};
use cedar_poo_core::operation_identity::OperationId;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub(crate) enum Worker {
    A,
    B,
}

impl Worker {
    pub fn name(self) -> &'static str {
        match self {
            Self::A => "a",
            Self::B => "b",
        }
    }

    pub fn other(self) -> Self {
        match self {
            Self::A => Self::B,
            Self::B => Self::A,
        }
    }

    pub fn phase(self, prefix: &str) -> String {
        format!("{prefix}-{}", self.name())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Step {
    event: String,
    worker: String,
    writer_advance: u64,
    receiver_advance: u64,
    original_status: String,
    missing_status: String,
    stored_receipt: String,
    receiver_receipt: String,
    intent_bound: bool,
    missing_intent_bound: bool,
    revocation_preserved: bool,
    original_idempotent: bool,
    conflict_refused: bool,
    missing_preserved: bool,
    old_writer_fenced: bool,
    old_replica_fenced: bool,
    no_resend: bool,
    mapping_accepted: bool,
    cross_operation_refused: bool,
    cross_authority_refused: bool,
    foreign_provider_refused: bool,
    foreign_witness_refused: bool,
    source_substitution_refused: bool,
    intent_substitution_refused: bool,
    mapping_persisted: bool,
    missing_mapping_absent: bool,
}

#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RecoveryRound {
    pub first_worker: Worker,
    pub steps: Vec<Step>,
    pub handoffs_after_first: u64,
    pub handoffs_after_second: u64,
    pub handoffs_after_confirmation: u64,
    pub expected_advances: u64,
    pub expected_crashes: u64,
}

impl RecoveryRound {
    pub fn baseline() -> Self {
        Self {
            first_worker: Worker::A,
            steps: Vec::new(),
            handoffs_after_first: 2,
            handoffs_after_second: 2,
            handoffs_after_confirmation: 2,
            expected_advances: 6,
            expected_crashes: 3,
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RecoveryPlan {
    format: String,
    scope: String,
    identity_mapping: String,
    rounds: Vec<RecoveryRound>,
}

#[test]
#[ignore = "requires the Lean-generated recovery plan from just check-gateway"]
fn lean_plan_drives_both_native_commit_orders() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.lake/build/gateway-recovery-plan.json");
    let plan: RecoveryPlan = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    assert_eq!(plan.format, "cedar-poo-legacy-recovery-plan-v4");
    assert_eq!(plan.scope, "settled-read-only-recovery");
    assert_eq!(
        plan.identity_mapping,
        "operation-authority-provider-and-exact-signed-sources"
    );
    assert_eq!(plan.rounds.len(), 3);
    for round in &plan.rounds {
        assert!(round.handoffs_after_first > 0);
        assert!(round.handoffs_after_second > 0);
        assert!(round.handoffs_after_confirmation > 0);
        assert_eq!(
            round.expected_advances,
            round.handoffs_after_first
                + round.handoffs_after_second
                + round.handoffs_after_confirmation
        );
        assert_eq!(round.expected_crashes, 3);
        assert_eq!(round.steps.len() as u64, round.expected_advances + 7);
    }
    settlement_race(
        "model-aligned-takeover",
        true,
        Some(FirstCommit::Takeover),
        &plan.rounds,
        None,
    );
    settlement_race(
        "model-aligned-migration",
        true,
        Some(FirstCommit::Migration),
        &plan.rounds,
        None,
    );
}

fn status_name(status: EffectStatus) -> &'static str {
    match status {
        EffectStatus::Unreserved => "unreserved",
        EffectStatus::Unresolved => "unresolved",
        EffectStatus::Reconciled => "reconciled",
    }
}

pub(super) struct RoundObserver {
    root: PathBuf,
    round: usize,
    original: Signed,
    conflict: Signed,
    conflict_journal: ProviderJournal,
    audit: AuditAuthority,
    ledger: serde_json::Value,
    initial_writer: u64,
    initial_receiver: u64,
    expected: Vec<Step>,
    next: usize,
}

impl RoundObserver {
    pub fn new(
        root: &Path,
        fixture: &RestartFixture,
        round: &RecoveryRound,
        receiver: u64,
        original: &Signed,
    ) -> Self {
        std::fs::create_dir_all(root.join("identity-foreign-authority")).unwrap();
        let provider = simulation_key(8);
        let original = original.clone();
        let mut conflict: ProviderOutcome = verify(&original, provider.verifying_key()).unwrap();
        conflict.outcome.action.result = "different completion".into();
        let signed_conflict = sign(&conflict, &provider).unwrap();
        assert_ne!(
            original.source_sha256().unwrap(),
            signed_conflict.source_sha256().unwrap()
        );
        let log_key = Witness::simulation().verifying_key();
        let issuer = simulation_key(3);
        let audit = AuditAuthority {
            gateway_key: *simulation_key(4).verifying_key(),
            log_key,
            facts: FactAuthority::new(
                vec![fixture.fact.clone()],
                [(fixture.fact.issuer.clone(), *issuer.verifying_key())].into(),
                14,
            )
            .unwrap(),
            minimum_size: 1,
            independent_frontier: Some(
                WitnessFrontier::from_checkpoint(&fixture.history.checkpoint, &log_key).unwrap(),
            ),
            review_trust: None,
            prepared_publications: None,
        };
        let oauth_path = root.join("oauth");
        let oauth =
            DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
        let checkpoint = serde_json::to_value(oauth.checkpoint().unwrap()).unwrap();
        Self {
            root: root.into(),
            round: fixture.round,
            original,
            conflict: signed_conflict,
            conflict_journal: ProviderJournal::observation(conflict.outcome.action),
            audit,
            ledger: checkpoint.get("ledger").unwrap().clone(),
            initial_writer: fixture.writer.generation(),
            initial_receiver: receiver,
            expected: round.steps.clone(),
            next: 0,
        }
    }

    pub fn observe(&mut self, fixture: &RestartFixture, event: &str, worker: &str) {
        let provider = simulation_key(8);
        let sender = simulation_key(4);
        let log_key = Witness::simulation().verifying_key();
        let pin = self.root.join("pin");
        let trust = || ReceiverTrust {
            scope: "settlement-race",
            sender: sender.verifying_key(),
            witness: &log_key,
            provider: &provider,
        };
        let receiver = DurableReceiver::managed(&fixture.active, &pin, trust()).unwrap();
        let retired = DurableReceiver::managed(&fixture.retired, &pin, trust()).unwrap();
        let trusted = LegacyReceiverTrust::from_config(&pin, "settlement-race").unwrap();
        let oauth_path = self.root.join("oauth");
        let oauth =
            DurableRefreshLedger::new(&oauth_path, "settlement-race").for_writer(fixture.writer);
        let operation = OperationId(fixture.effect.operation.clone());
        let missing_operation = OperationId(fixture.missing.operation.clone());
        assert_ne!(operation, missing_operation);
        let before = std::fs::read(oauth_path.join("checkpoint.json")).unwrap();
        let original = oauth.effect_observation(&operation).unwrap().unwrap();
        let missing = oauth
            .effect_observation(&missing_operation)
            .unwrap()
            .unwrap();
        let original_id = self.original.source_sha256().unwrap();
        let expected: ProviderOutcome = verify(&self.original, provider.verifying_key()).unwrap();
        let received = receiver.evidence(&operation).unwrap().unwrap();
        assert_eq!(received.outcome, self.original);
        assert_eq!(original.outcome_identity.as_ref(), Some(&original_id));
        assert!(missing.outcome_identity.is_none());
        assert!(receiver.evidence(&missing_operation).unwrap().is_none());
        let outcomes = std::slice::from_ref(&self.original);
        let audit = ProviderAuditTrust {
            authority: &self.audit,
            provider_key: provider.verifying_key(),
        };
        let original_input = || DurableEffectRecovery {
            effect: &fixture.effect,
            journal: &received.journal,
            outcomes,
            history: &fixture.history,
            trust: audit,
        };
        let confirmed =
            receiver.migrate_legacy_oauth_batch_at(&oauth, [original_input()], &trusted, |_, _| {
                panic!("step observation wrote a checkpoint")
            });
        let conflicting = receiver.migrate_legacy_oauth_batch_at(
            &oauth,
            [DurableEffectRecovery {
                journal: &self.conflict_journal,
                outcomes: std::slice::from_ref(&self.conflict),
                ..original_input()
            }],
            &trusted,
            |_, _| panic!("conflict replaced the original receipt"),
        );
        let empty = ProviderJournal::default();
        let absent = receiver.migrate_legacy_oauth_batch_at(
            &oauth,
            [DurableEffectRecovery {
                effect: &fixture.missing,
                journal: &empty,
                outcomes: &[],
                ..original_input()
            }],
            &trusted,
            |_, _| panic!("missing evidence changed an operation"),
        );
        let context = ReceiptIdentityContext {
            receiver: &trusted,
            provider_key: provider.verifying_key(),
            witness_key: &log_key,
            effect: &fixture.effect,
            intent: &expected.outcome.commit,
            outcome: &received.outcome,
        };
        let mapping = context.prepare().unwrap();
        let candidate = original
            .receipt_identity
            .as_ref()
            .expect("durable receipt mapping");
        assert_eq!(candidate, &mapping.candidate());
        assert_eq!(candidate.identity.outcome_sha256, original_id);
        assert_eq!(candidate.identity.intent_sha256, original.intent_identity);
        let prefix_operation = OperationId(fixture.prefix.operation.clone());
        let prefix = receiver.evidence(&prefix_operation).unwrap().unwrap();
        let prefix_outcome: ProviderOutcome =
            verify(&prefix.outcome, provider.verifying_key()).unwrap();
        let prefix_mapping = ReceiptIdentityContext {
            effect: &fixture.prefix,
            intent: &prefix_outcome.outcome.commit,
            outcome: &prefix.outcome,
            ..context
        }
        .prepare()
        .unwrap();
        let mut disguised_operation = prefix_mapping.candidate();
        disguised_operation.identity.operation = operation.clone();
        let cross_operation = receiver.migrate_legacy_oauth_batch_at(
            &oauth,
            [DurableEffectRecovery {
                journal: &prefix.journal,
                outcomes: std::slice::from_ref(&prefix.outcome),
                ..original_input()
            }],
            &trusted,
            |_, _| panic!("cross-operation receipt replaced the original"),
        );
        let cross_pending = receiver.migrate_legacy_oauth_batch_at(
            &oauth,
            [DurableEffectRecovery {
                effect: &fixture.missing,
                ..original_input()
            }],
            &trusted,
            |_, _| panic!("cross-operation receipt bound a missing operation"),
        );
        let foreign = LegacyReceiverTrust::from_config(
            &self.root.join("identity-foreign-authority"),
            "settlement-race",
        )
        .unwrap();
        let foreign_mapping = ReceiptIdentityContext {
            receiver: &foreign,
            ..context
        }
        .prepare()
        .unwrap();
        let foreign_authority =
            receiver.migrate_legacy_oauth_batch_at(&oauth, [original_input()], &foreign, |_, _| {
                panic!("cross-authority receipt replaced the original")
            });
        let foreign_provider = simulation_key(9);
        let foreign_source = sign(&expected, &foreign_provider).unwrap();
        let foreign_provider_mapping = ReceiptIdentityContext {
            provider_key: foreign_provider.verifying_key(),
            outcome: &foreign_source,
            ..context
        }
        .prepare()
        .unwrap();
        let foreign_key_recovery = receiver.migrate_legacy_oauth_batch_at(
            &oauth,
            [DurableEffectRecovery {
                outcomes: std::slice::from_ref(&foreign_source),
                trust: ProviderAuditTrust {
                    provider_key: foreign_provider.verifying_key(),
                    ..audit
                },
                ..original_input()
            }],
            &trusted,
            |_, _| panic!("another provider authority replaced the original receipt"),
        );
        let mut foreign_witness = (*candidate).clone();
        foreign_witness.identity.witness_key = foreign_provider
            .verifying_key()
            .to_encoded_point(false)
            .as_bytes()
            .to_vec();
        let mut changed_source = (*candidate).clone();
        changed_source.outcome.payload[0] ^= 1;
        let mut changed_intent = (*candidate).clone();
        changed_intent.intent.signature[0] ^= 1;
        let old = oauth.for_writer(fixture.retired_writer.unwrap());
        let old_writer = receiver.migrate_legacy_oauth_batch(&old, [original_input()], &trusted);
        let old_replica = retired.migrate_legacy_oauth_batch(&oauth, [original_input()], &trusted);
        let checkpoint = oauth.checkpoint().unwrap();
        let current = actual(
            fixture.grant.clone(),
            14,
            &format!("trace-round-{}-step-{}", self.round, self.next),
        );
        let no_resend = !oauth
            .execute_final(
                DurableFinalUse {
                    checked: &checkpoint,
                    replica: &checkpoint,
                    current: &current,
                    base_allowed: true,
                },
                || panic!("revoked authorization allowed an effect"),
            )
            .unwrap();
        let portable = serde_json::to_value(&checkpoint).unwrap();
        let actual = Step {
            event: event.into(),
            worker: worker.into(),
            writer_advance: fixture.writer.generation() - self.initial_writer,
            receiver_advance: receiver.cut().unwrap().generation - self.initial_receiver,
            original_status: status_name(original.status).into(),
            missing_status: status_name(missing.status).into(),
            stored_receipt: "original".into(),
            receiver_receipt: "original".into(),
            intent_bound: original.intent_identity
                == expected.outcome.commit.source_sha256().unwrap(),
            missing_intent_bound: missing.intent_identity
                == fixture.missing_intent.source_sha256().unwrap(),
            revocation_preserved: portable.get("ledger") == Some(&self.ledger),
            original_idempotent: confirmed.confirmed == [operation.clone()]
                && confirmed.pending.is_empty()
                && confirmed.stopped.is_none(),
            conflict_refused: conflicting.pending == [operation.clone()]
                && conflicting.confirmed.is_empty()
                && conflicting.stopped.is_none(),
            missing_preserved: absent.pending == [missing_operation]
                && absent.confirmed.is_empty()
                && absent.stopped.is_none()
                && missing.outcome_identity.is_none(),
            old_writer_fenced: old_writer
                .stopped
                .is_some_and(|stop| stop.error == "OAuth writer fenced"),
            old_replica_fenced: old_replica.stopped.is_some_and(|stop| {
                stop.error == "receiver replica differs from the independent checkpoint"
            }),
            no_resend,
            mapping_accepted: mapping.check(candidate) == Some(candidate.identity.clone()),
            cross_operation_refused: mapping.check(&prefix_mapping.candidate()).is_none()
                && mapping.check(&disguised_operation).is_none()
                && cross_operation.confirmed.is_empty()
                && cross_operation.pending == [operation.clone()]
                && cross_operation.stopped.is_none()
                && cross_pending.confirmed.is_empty()
                && cross_pending.pending == [OperationId(fixture.missing.operation.clone())]
                && cross_pending.stopped.is_none(),
            cross_authority_refused: mapping.check(&foreign_mapping.candidate()).is_none()
                && foreign_authority.confirmed.is_empty()
                && foreign_authority.pending == [operation.clone()]
                && foreign_authority.stopped.is_none(),
            foreign_provider_refused: mapping
                .check(&foreign_provider_mapping.candidate())
                .is_none()
                && foreign_key_recovery.confirmed.is_empty()
                && foreign_key_recovery.pending == [operation.clone()]
                && foreign_key_recovery.stopped.is_none(),
            foreign_witness_refused: mapping.check(&foreign_witness).is_none(),
            source_substitution_refused: mapping.check(&changed_source).is_none(),
            intent_substitution_refused: mapping.check(&changed_intent).is_none(),
            mapping_persisted: mapping.check(candidate) == Some(candidate.identity.clone()),
            missing_mapping_absent: missing.receipt_identity.is_none(),
        };
        assert!(actual.intent_bound && actual.missing_intent_bound && actual.revocation_preserved);
        assert!(actual.mapping_persisted && actual.missing_mapping_absent);
        assert!(actual.original_idempotent && actual.conflict_refused && actual.missing_preserved);
        assert!(actual.old_writer_fenced && actual.old_replica_fenced && actual.no_resend);
        assert!(
            actual.mapping_accepted
                && actual.cross_operation_refused
                && actual.cross_authority_refused
        );
        assert!(
            actual.foreign_provider_refused
                && actual.foreign_witness_refused
                && actual.source_substitution_refused
                && actual.intent_substitution_refused
        );
        if !self.expected.is_empty() {
            assert_eq!(
                self.expected.get(self.next),
                Some(&actual),
                "recovery step {}",
                self.next
            );
        }
        assert_eq!(
            std::fs::read(oauth_path.join("checkpoint.json")).unwrap(),
            before
        );
        eprintln!(
            "RECOVERY-STEP-OK {}",
            serde_json::json!({
                "round": self.round, "index": self.next, "state": actual,
                "native_outcome_sha256": original_id,
                "native_intent_sha256": original.intent_identity,
                "native_conflict_sha256": self.conflict.source_sha256().unwrap()
            })
        );
        self.next += 1;
    }

    pub fn finish(self) {
        if !self.expected.is_empty() {
            assert_eq!(self.next, self.expected.len());
        }
    }
}
