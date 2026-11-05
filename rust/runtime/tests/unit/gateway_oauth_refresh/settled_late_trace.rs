use super::{RestartFixture, actual};
use crate::gateway::checkpoint_store::CheckpointStage;
use crate::gateway::oauth_refresh_durable::{
    DurableEffectObservation, DurableEffectRecovery, DurableFinalUse, DurableRefreshLedger,
    EffectStatus,
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

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Step {
    event: String,
    worker: String,
    writer_advance: u64,
    receipt: String,
    operation_bound: bool,
    authority_bound: bool,
    intent_source_bound: bool,
    outcome_source_bound: bool,
    version_bound: bool,
    intent_bound: bool,
    legacy_digest_bound: bool,
    original_idempotent: bool,
    conflict_refused: bool,
    old_writer_fenced: bool,
    old_replica_fenced: bool,
    missing_preserved: bool,
    intents_preserved: bool,
    revocation_preserved: bool,
    no_resend: bool,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Plan {
    format: String,
    scope: String,
    identity_mapping: String,
    steps: Vec<Step>,
}

pub(super) struct Observer {
    root: PathBuf,
    initial_writer: u64,
    initial_receiver: u64,
    original: Signed,
    conflict: Signed,
    conflict_journal: ProviderJournal,
    audit: AuditAuthority,
    missing: DurableEffectObservation,
    first: DurableEffectObservation,
    ledger: serde_json::Value,
    intents: serde_json::Value,
    expected: Vec<Step>,
    next: usize,
}

// Compare every retained operation's signed intent, not mutable receipt metadata.
fn retained_intents(path: &Path) -> serde_json::Value {
    let image: serde_json::Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    let intents: serde_json::Map<String, serde_json::Value> = image["effects"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(operation, row)| (operation.clone(), row["intent"].clone()))
        .collect();
    intents.into()
}

fn readonly(_: &OperationId, _: CheckpointStage) -> Result<(), String> {
    panic!("step observation wrote a checkpoint")
}

impl Observer {
    pub fn new(root: &Path, fixture: &RestartFixture, original: &Signed) -> Self {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../.lake/build/gateway-settled-late-plan.json");
        let plan: Plan = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        assert_eq!(plan.format, "cedar-poo-settled-late-plan-v1");
        assert_eq!(plan.scope, "late-settled-receipt-step-alignment");
        assert_eq!(
            plan.identity_mapping,
            "operation-authority-version-and-exact-signed-sources"
        );
        assert_eq!(plan.steps.len(), 22);
        let provider = simulation_key(8);
        let mut conflicting: ProviderOutcome = verify(original, provider.verifying_key()).unwrap();
        conflicting.outcome.action.result = "conflicting delayed completion".into();
        let conflict = sign(&conflicting, &provider).unwrap();
        assert_ne!(
            original.source_sha256().unwrap(),
            conflict.source_sha256().unwrap()
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
        let sender = simulation_key(4);
        let pin = root.join("pin");
        let receiver = DurableReceiver::managed(
            &fixture.active,
            &pin,
            ReceiverTrust {
                scope: "settlement-race",
                sender: sender.verifying_key(),
                witness: &log_key,
                provider: &provider,
            },
        )
        .unwrap();
        Self {
            root: root.into(),
            initial_writer: fixture.writer.generation(),
            initial_receiver: receiver.cut().unwrap().generation,
            original: original.clone(),
            conflict,
            conflict_journal: ProviderJournal::observation(conflicting.outcome.action),
            audit,
            missing: oauth
                .effect_observation(&OperationId(fixture.missing.operation.clone()))
                .unwrap()
                .unwrap(),
            first: oauth
                .effect_observation(&OperationId(fixture.effect.operation.clone()))
                .unwrap()
                .unwrap(),
            ledger: checkpoint["ledger"].clone(),
            intents: retained_intents(&root.join("oauth/checkpoint.json")),
            expected: plan.steps,
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
        let operation = OperationId(fixture.prefix.operation.clone());
        let missing_operation = OperationId(fixture.missing.operation.clone());
        let before = std::fs::read(oauth_path.join("checkpoint.json")).unwrap();
        let target = oauth.effect_observation(&operation).unwrap().unwrap();
        let missing = oauth
            .effect_observation(&missing_operation)
            .unwrap()
            .unwrap();
        assert_eq!(target.status, EffectStatus::Reconciled);
        let received = receiver.evidence(&operation).unwrap().unwrap();
        assert_eq!(received.outcome, self.original);
        let decoded: ProviderOutcome = verify(&self.original, provider.verifying_key()).unwrap();
        let context = ReceiptIdentityContext {
            receiver: &trusted,
            provider_key: provider.verifying_key(),
            witness_key: &log_key,
            effect: &fixture.prefix,
            intent: &decoded.outcome.commit,
            outcome: &self.original,
        };
        let mapping = context.prepare().unwrap();
        let canonical = mapping.candidate();
        let input = || DurableEffectRecovery {
            effect: &fixture.prefix,
            journal: &received.journal,
            outcomes: std::slice::from_ref(&self.original),
            history: &fixture.history,
            trust: ProviderAuditTrust {
                authority: &self.audit,
                provider_key: provider.verifying_key(),
            },
        };
        let original_idempotent = target.receipt_identity.is_some() && {
            let report =
                receiver.migrate_settled_oauth_mappings_at(&oauth, [input()], &trusted, readonly);
            report.confirmed == [operation.clone()]
                && report.pending.is_empty()
                && report.stopped.is_none()
        };
        let conflict = receiver.migrate_settled_oauth_mappings_at(
            &oauth,
            [DurableEffectRecovery {
                journal: &self.conflict_journal,
                outcomes: std::slice::from_ref(&self.conflict),
                ..input()
            }],
            &trusted,
            readonly,
        );
        let empty = ProviderJournal::default();
        let absent = receiver.migrate_settled_oauth_mappings_at(
            &oauth,
            [DurableEffectRecovery {
                effect: &fixture.missing,
                journal: &empty,
                outcomes: &[],
                ..input()
            }],
            &trusted,
            readonly,
        );
        let old_writer = receiver.migrate_settled_oauth_mappings_at(
            &oauth.for_writer(fixture.retired_writer.unwrap()),
            [input()],
            &trusted,
            readonly,
        );
        let old_replica =
            retired.migrate_settled_oauth_mappings_at(&oauth, [input()], &trusted, readonly);
        let checkpoint = oauth.checkpoint().unwrap();
        let current = actual(
            fixture.grant.clone(),
            14,
            &format!("late-step-{}", self.next),
        );
        let no_resend = !oauth
            .execute_final(
                DurableFinalUse {
                    checked: &checkpoint,
                    replica: &checkpoint,
                    current: &current,
                    base_allowed: true,
                },
                || panic!("recovery observation authorized a new effect"),
            )
            .unwrap();
        let candidate = target.receipt_identity.as_ref();
        if let Some(stored) = candidate {
            assert_eq!(stored, &canonical);
            assert_eq!(mapping.check(stored), Some(stored.identity.clone()));
            let mut substituted = stored.clone();
            substituted.outcome.signature[0] ^= 1;
            assert!(mapping.check(&substituted).is_none());
            substituted = stored.clone();
            substituted.identity.operation = OperationId(fixture.effect.operation.clone());
            assert!(mapping.check(&substituted).is_none());
            substituted = stored.clone();
            substituted.identity.authority.scope = "foreign-authority".into();
            assert!(mapping.check(&substituted).is_none());
        }
        let actual = Step {
            event: event.into(),
            worker: worker.into(),
            writer_advance: fixture.writer.generation() - self.initial_writer,
            receipt: candidate
                .map_or("absent", |row| {
                    if row.outcome == self.original {
                        "original"
                    } else {
                        "conflict"
                    }
                })
                .into(),
            operation_bound: candidate.is_some_and(|row| row.identity.operation == operation),
            authority_bound: candidate.is_some_and(|row| {
                row.identity.authority == canonical.identity.authority
                    && row.identity.provider_key == canonical.identity.provider_key
                    && row.identity.witness_key == canonical.identity.witness_key
            }),
            intent_source_bound: candidate.is_some_and(|row| {
                row.intent == canonical.intent
                    && row.identity.intent_sha256 == canonical.identity.intent_sha256
            }),
            outcome_source_bound: candidate.is_some_and(|row| {
                row.outcome == self.original
                    && row.identity.outcome_sha256 == self.original.source_sha256().unwrap()
            }),
            version_bound: candidate
                .is_some_and(|row| row.identity.version == canonical.identity.version),
            intent_bound: target.intent_identity == decoded.outcome.commit.source_sha256().unwrap(),
            legacy_digest_bound: target.outcome_identity
                == Some(self.original.source_sha256().unwrap()),
            original_idempotent,
            conflict_refused: conflict.confirmed.is_empty()
                && conflict.pending == [operation]
                && conflict.stopped.is_none(),
            old_writer_fenced: old_writer
                .stopped
                .is_some_and(|stop| stop.error == "OAuth writer fenced"),
            old_replica_fenced: old_replica.stopped.is_some_and(|stop| {
                stop.error == "receiver replica differs from the independent checkpoint"
            }),
            missing_preserved: missing.receipt_identity.is_none()
                && missing == self.missing
                && absent.confirmed.is_empty()
                && absent.pending == [missing_operation]
                && absent.stopped.is_none()
                && oauth
                    .effect_observation(&OperationId(fixture.effect.operation.clone()))
                    .unwrap()
                    .as_ref()
                    == Some(&self.first),
            intents_preserved: retained_intents(&oauth_path.join("checkpoint.json"))
                == self.intents,
            revocation_preserved: serde_json::to_value(&checkpoint).unwrap()["ledger"]
                == self.ledger,
            no_resend,
        };
        let receiver_advance = receiver.cut().unwrap().generation - self.initial_receiver;
        assert_eq!(receiver_advance, actual.writer_advance);
        assert_eq!(
            self.expected.get(self.next),
            Some(&actual),
            "late recovery step {}",
            self.next
        );
        assert_eq!(
            std::fs::read(oauth_path.join("checkpoint.json")).unwrap(),
            before
        );
        eprintln!(
            "SETTLED-LATE-STEP-OK {}",
            serde_json::json!({
                "index": self.next, "state": actual, "receiver_advance": receiver_advance,
                "native_identity": candidate.map(|row| &row.identity),
                "native_intent_sha256": target.intent_identity,
                "native_outcome_sha256": target.outcome_identity,
                "native_conflict_sha256": self.conflict.source_sha256().unwrap(),
            })
        );
        self.next += 1;
    }

    pub fn finish(self) {
        assert_eq!(
            self.next,
            self.expected.len(),
            "late recovery trace truncated"
        );
    }
}
