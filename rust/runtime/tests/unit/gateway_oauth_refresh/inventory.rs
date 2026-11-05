use super::{DurableRefreshLedger, durable_directory};
use crate::gateway::oauth_refresh_durable::EffectStatus;
use cedar_poo_core::operation_identity::OperationId;

#[test]
fn durable_restore_requires_explicit_effect_inventory() {
    let directory = durable_directory("required-effect-inventory");
    let ledger = DurableRefreshLedger::new(&directory, "authority");
    ledger.initialize().unwrap();
    let path = directory.join("checkpoint.json");
    let original = std::fs::read(&path).unwrap();
    let mut image: serde_json::Value = serde_json::from_slice(&original).unwrap();
    assert_eq!(image["effects"], serde_json::json!({}));
    image.as_object_mut().unwrap().remove("effects");
    let missing = serde_json::to_vec(&image).unwrap();
    std::fs::write(&path, &missing).unwrap();
    for _ in 0..2 {
        let restarted = DurableRefreshLedger::new(&directory, "authority");
        assert!(
            restarted.checkpoint().is_err(),
            "missing inventory silently restored"
        );
        assert!(
            restarted
                .effect_status(&OperationId("effect".into()))
                .is_err()
        );
        assert_eq!(std::fs::read(&path).unwrap(), missing);
    }
    std::fs::write(&path, original).unwrap();
    assert_eq!(
        ledger.effect_status(&OperationId("effect".into())).unwrap(),
        EffectStatus::Unreserved
    );
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn retained_effect_inventory_is_unique_bound_and_never_reopens_unknown_work() {
    use super::{Confirmation, DurableFinalUse, actual, digest, enroll_with, verified};
    use crate::gateway::oauth_refresh_durable::DurableEffectUse;
    use crate::gateway::wire::simulation_key;
    use crate::gateway::witness::PrecommitInput;
    use crate::gateway::{
        AuditAuthority, EffectIdentity, FactAuthority, FactBinding, Origin, ProviderAuditTrust,
        ReviewBinding, Witness, WitnessFrontier,
    };
    use serde_json::{Value, json};

    for confirmation in [
        Confirmation::Dpop("key".into()),
        Confirmation::Mtls("cert".into()),
    ] {
        let directory = durable_directory("bound-effect-inventory");
        let ledger = DurableRefreshLedger::new(&directory, "authority");
        ledger.initialize().unwrap();
        let grant = enroll_with(confirmation, |input| ledger.enroll(input).unwrap());
        let checked = ledger.checkpoint().unwrap();
        let effect = EffectIdentity {
            operation: "effect".into(),
            object: "object".into(),
            generation: 0,
            payload: "payload".into(),
            action_schema: "schema".into(),
            audience: "fhir".into(),
        };
        let fact = FactBinding {
            issuer: "facts".into(),
            subject: "subject".into(),
            audience: "fhir".into(),
            source: "world".into(),
            field: "field".into(),
            value: "value".into(),
            generation: 0,
            origin: Origin::Observed,
            not_before: 10,
            expires_at: 20,
        };
        let mut review = ReviewBinding {
            before: "policy".into(),
            after: "policy".into(),
            schema: "schema".into(),
            source: "world".into(),
            epoch: 0,
            report: String::new(),
        };
        review.report = crate::json_sha256(&review).unwrap();
        let mut witness = Witness::simulation();
        let intent = witness
            .append(PrecommitInput {
                current_world: "world",
                effect: &effect,
                review: &review,
                facts: std::slice::from_ref(&fact),
                publications: &[],
            })
            .unwrap();
        let unrelated = EffectIdentity {
            operation: "unrelated-effect".into(),
            payload: "unrelated-payload".into(),
            ..effect.clone()
        };
        let unrelated_intent = witness
            .append(PrecommitInput {
                current_world: "world",
                effect: &unrelated,
                review: &review,
                facts: std::slice::from_ref(&fact),
                publications: &[],
            })
            .unwrap();
        let history = witness.snapshot();
        let log_key = witness.verifying_key();
        let provider = simulation_key(8);
        let audit = AuditAuthority {
            gateway_key: *simulation_key(4).verifying_key(),
            log_key,
            facts: FactAuthority::new(
                vec![fact.clone()],
                [("facts".into(), *simulation_key(3).verifying_key())].into(),
                14,
            )
            .unwrap(),
            minimum_size: 1,
            independent_frontier: Some(
                WitnessFrontier::from_checkpoint(&history.checkpoint, &log_key).unwrap(),
            ),
            review_trust: None,
            prepared_publications: None,
        };
        let trust = ProviderAuditTrust {
            authority: &audit,
            provider_key: provider.verifying_key(),
        };
        let first_current = actual(grant.clone(), 14, "first");
        let retry_current = actual(grant.clone(), 14, "fresh-retry");
        let admission = |current| DurableEffectUse {
            admission: DurableFinalUse {
                checked: &checked,
                replica: &checked,
                current,
                base_allowed: true,
            },
            effect: &effect,
            intent: &intent,
            history: &history,
            trust,
        };
        let mut dispatched = 0;
        assert!(
            ledger
                .execute_effect(admission(&first_current), |_| {
                    dispatched += 1;
                    Err("lost completion reply".into())
                })
                .is_err()
        );
        let operation = OperationId(effect.operation.clone());
        assert_eq!(
            ledger.effect_status(&operation).unwrap(),
            EffectStatus::Unresolved
        );
        let original_identity = ledger
            .effect_observation(&operation)
            .unwrap()
            .unwrap()
            .intent_identity;
        let path = directory.join("checkpoint.json");
        let original = std::fs::read(&path).unwrap();
        let base: Value = serde_json::from_slice(&original).unwrap();
        let record = base["effects"]["effect"].clone();
        let raw_record = serde_json::to_string(&record).unwrap();
        let mut conflicting = record.clone();
        conflicting["resolved"] = json!(true);
        let raw_conflicting = serde_json::to_string(&conflicting).unwrap();
        let mut absent = base.clone();
        absent.as_object_mut().unwrap().remove("effects");
        let prefix = serde_json::to_string(&absent).unwrap();
        let prefix = prefix.strip_suffix('}').unwrap();
        let raw_map = |members: String| {
            (prefix.to_owned() + r#","effects":{"# + &members + "}}").into_bytes()
        };
        let mut variants = vec![
            ("missing", serde_json::to_vec(&absent).unwrap()),
            (
                "duplicate",
                raw_map(format!(r#""effect":{raw_record},"effect":{raw_record}"#)),
            ),
            (
                "escaped duplicate",
                raw_map(format!(
                    r#""effect":{raw_record},"\u0065ffect":{raw_record}"#
                )),
            ),
            (
                "conflicting last",
                raw_map(format!(
                    r#""effect":{raw_record},"effect":{raw_conflicting}"#
                )),
            ),
            (
                "conflicting first",
                raw_map(format!(
                    r#""effect":{raw_conflicting},"effect":{raw_record}"#
                )),
            ),
        ];
        for key in ["", "different-operation"] {
            let mut changed = base.clone();
            changed["effects"] = json!({key: record.clone()});
            variants.push(("wrong key", serde_json::to_vec(&changed).unwrap()));
        }
        let mut changed = base.clone();
        changed["effects"] = Value::Null;
        variants.push(("null", serde_json::to_vec(&changed).unwrap()));
        let mut malformed = base.clone();
        let mut changed_intent = intent.clone();
        changed_intent.payload = b"{}".to_vec();
        malformed["effects"]["effect"]["intent"] = serde_json::to_value(changed_intent).unwrap();
        variants.push(("malformed intent", serde_json::to_vec(&malformed).unwrap()));
        for (label, bytes) in variants {
            std::fs::write(&path, &bytes).unwrap();
            for _ in 0..2 {
                let restarted = DurableRefreshLedger::new(&directory, "authority");
                assert!(restarted.checkpoint().is_err(), "{label}");
                assert!(restarted.effect_status(&operation).is_err(), "{label}");
                assert!(
                    restarted
                        .execute_effect(admission(&retry_current), |_| {
                            dispatched += 1;
                            Ok(())
                        },)
                        .is_err(),
                    "{label}"
                );
                assert_eq!(std::fs::read(&path).unwrap(), bytes, "{label}");
                assert_eq!(dispatched, 1);
            }
        }
        std::fs::write(&path, &original).unwrap();
        // Fresh work may be interleaved with recovery, without deleting or
        // replacing the earlier unknown operation.
        let sibling_current = actual(grant.clone(), 14, "sibling-proof");
        let sibling_checked = ledger.checkpoint().unwrap();
        let mut sibling_dispatches = 0;
        assert!(
            ledger
                .execute_effect(
                    DurableEffectUse {
                        admission: DurableFinalUse {
                            checked: &sibling_checked,
                            replica: &sibling_checked,
                            current: &sibling_current,
                            base_allowed: true,
                        },
                        effect: &unrelated,
                        intent: &unrelated_intent,
                        history: &history,
                        trust,
                    },
                    |_| {
                        sibling_dispatches += 1;
                        Ok(())
                    }
                )
                .unwrap()
        );
        assert_eq!(sibling_dispatches, 1);
        let mut previous_cut = Default::default();
        for round in 0..3 {
            let previous =
                DurableRefreshLedger::new(&directory, "authority").for_writer(previous_cut);
            let cut = previous.rotate_writer().unwrap();
            assert!(previous.checkpoint().is_err());
            previous_cut = cut;
            let restarted = DurableRefreshLedger::new(&directory, "authority").for_writer(cut);
            assert_eq!(
                restarted.effect_status(&operation).unwrap(),
                EffectStatus::Unresolved
            );
            assert_eq!(
                restarted
                    .effect_observation(&operation)
                    .unwrap()
                    .unwrap()
                    .intent_identity,
                original_identity,
            );
            assert_eq!(
                restarted
                    .effect_status(&OperationId(unrelated.operation.clone()))
                    .unwrap(),
                EffectStatus::Unresolved,
            );
            let fresh = restarted.checkpoint().unwrap();
            assert!(
                !restarted
                    .execute_effect(
                        DurableEffectUse {
                            admission: DurableFinalUse {
                                checked: &fresh,
                                replica: &fresh,
                                current: &retry_current,
                                base_allowed: true,
                            },
                            effect: &effect,
                            intent: &intent,
                            history: &history,
                            trust,
                        },
                        |_| {
                            dispatched += 1;
                            Ok(())
                        },
                    )
                    .unwrap()
            );
            if round == 0 {
                assert!(restarted.revoke(verified(digest())).unwrap());
            }
            assert_eq!(
                restarted.effect_status(&operation).unwrap(),
                EffectStatus::Unresolved
            );
            assert_eq!(dispatched, 1);
        }
        // Signature/current-head authentication is independent from these decoder checks.
        std::fs::remove_dir_all(directory).unwrap();
    }
}

#[test]
fn missing_writer_cut_cannot_reactivate_original_worker() {
    let directory = durable_directory("required-writer-cut");
    let old = DurableRefreshLedger::new(&directory, "authority");
    old.initialize().unwrap();
    let cut = old.rotate_writer().unwrap();
    let current = DurableRefreshLedger::new(&directory, "authority").for_writer(cut);
    assert!(old.checkpoint().is_err());
    assert!(current.checkpoint().is_ok());
    let path = directory.join("checkpoint.json");
    let original = std::fs::read(&path).unwrap();
    let mut image: serde_json::Value = serde_json::from_slice(&original).unwrap();
    image["checkpoint"]
        .as_object_mut()
        .unwrap()
        .remove("writer");
    let missing = serde_json::to_vec(&image).unwrap();
    std::fs::write(&path, &missing).unwrap();
    assert!(
        old.checkpoint().is_err(),
        "omitted cut reactivated writer zero"
    );
    assert!(current.checkpoint().is_err());
    assert_eq!(std::fs::read(&path).unwrap(), missing);
    std::fs::write(&path, original).unwrap();
    assert!(old.checkpoint().is_err());
    assert!(current.checkpoint().is_ok());
    std::fs::remove_dir_all(directory).unwrap();
}
