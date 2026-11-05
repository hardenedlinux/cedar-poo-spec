use super::{AuditAuthority, FactAuthority, ProviderJournal, Reconciliation, reconcile_recovery};
use crate::gateway::wire::simulation_key;
use crate::gateway::{FactBinding, Origin, Witness};

#[test]
fn verified_log_reuse_keeps_the_original_root_and_current_independent_floor() {
    let log = Witness::simulation();
    let history =
        crate::gateway::witness::verify_view(log.view(), &log.verifying_key(), 0).unwrap();
    let fact = FactBinding {
        issuer: "issuer".into(),
        subject: "subject".into(),
        audience: "audience".into(),
        source: "source".into(),
        field: "field".into(),
        value: "value".into(),
        generation: 0,
        origin: Origin::Observed,
        not_before: 0,
        expires_at: 1,
    };
    let facts = FactAuthority::new(
        vec![fact],
        [("issuer".into(), *simulation_key(3).verifying_key())].into(),
        0,
    )
    .unwrap();
    let mut authority = AuditAuthority {
        gateway_key: *simulation_key(3).verifying_key(),
        log_key: log.verifying_key(),
        facts,
        minimum_size: 0,
        independent_frontier: None,
        review_trust: None,
        prepared_publications: None,
    };
    let journal = ProviderJournal::default();
    assert_eq!(
        reconcile_recovery(&journal, &[], &history, &authority, None, None),
        (Reconciliation::default(), None)
    );
    authority.log_key = *simulation_key(7).verifying_key();
    assert!(
        reconcile_recovery(&journal, &[], &history, &authority, None, None)
            .0
            .invalid_log
    );
    authority.log_key = log.verifying_key();
    authority.minimum_size = 1;
    assert!(
        reconcile_recovery(&journal, &[], &history, &authority, None, None)
            .0
            .invalid_log
    );

    // Two authenticated writers using the same key can produce distinct,
    // same-height branches. The independent checkpoint chooses the prefix.
    let mut chosen = Witness::simulation();
    let mut fork = Witness::simulation();
    let effect = crate::gateway::EffectIdentity {
        operation: "operation".into(),
        object: "object".into(),
        generation: 0,
        payload: "payload".into(),
        action_schema: "schema".into(),
        audience: "audience".into(),
    };
    let review = crate::gateway::ReviewBinding {
        before: "before".into(),
        after: "after".into(),
        schema: "schema".into(),
        source: "source".into(),
        epoch: 0,
        report: "report".into(),
    };
    let append = |witness: &mut Witness, world| {
        witness
            .append(crate::gateway::witness::PrecommitInput {
                current_world: world,
                effect: &effect,
                review: &review,
                facts: &[],
                publications: &[],
            })
            .unwrap();
    };
    append(&mut chosen, "chosen");
    append(&mut fork, "fork");
    let chosen_snapshot = chosen.snapshot();
    let fork_snapshot = fork.snapshot();
    assert!(crate::gateway::verify_log(&fork_snapshot, &authority.log_key, 1).is_ok());
    assert!(!super::reconcile(&journal, &[], &fork_snapshot, &authority).invalid_log);
    authority.independent_frontier = Some(
        crate::gateway::WitnessFrontier::from_checkpoint(
            &chosen_snapshot.checkpoint,
            &authority.log_key,
        )
        .unwrap(),
    );
    assert!(!super::reconcile(&journal, &[], &chosen_snapshot, &authority).invalid_log);
    assert!(super::reconcile(&journal, &[], &fork_snapshot, &authority).invalid_log);
    let verified_fork =
        crate::gateway::witness::verify_view(fork.view(), &authority.log_key, 1).unwrap();
    assert!(
        reconcile_recovery(&journal, &[], &verified_fork, &authority, None, None)
            .0
            .invalid_log
    );
    append(&mut chosen, "extension");
    assert!(!super::reconcile(&journal, &[], &chosen.snapshot(), &authority).invalid_log);

    #[cfg(unix)]
    {
        let directory =
            std::env::temp_dir().join(format!("cedar-checkpoint-store-{}", std::process::id()));
        std::fs::create_dir(&directory).unwrap();
        let key = authority.log_key;
        let store = crate::gateway::CheckpointStore::new(&directory, &key);
        assert!(store.load().is_err());
        assert!(store.advance(&chosen_snapshot).is_err());
        let empty = Witness::simulation().snapshot();
        store.initialize(&empty.checkpoint).unwrap();
        assert!(store.initialize(&chosen_snapshot.checkpoint).is_err());

        let barrier = std::sync::Barrier::new(2);
        let (left, right) = std::thread::scope(|race| {
            let left = race.spawn(|| {
                barrier.wait();
                store.advance(&chosen_snapshot)
            });
            let right = race.spawn(|| {
                barrier.wait();
                store.advance(&fork_snapshot)
            });
            (left.join().unwrap(), right.join().unwrap())
        });
        assert_ne!(left.is_ok(), right.is_ok());
        let (winner, loser) = if left.is_ok() {
            (&chosen_snapshot, &fork_snapshot)
        } else {
            (&fork_snapshot, &chosen_snapshot)
        };
        let reopened = crate::gateway::CheckpointStore::new(&directory, &key);
        let pin = reopened.load().unwrap();
        assert!(pin.verify_extension(winner).is_ok());
        assert!(pin.verify_extension(loser).is_err());
        assert!(reopened.advance(&empty).is_err());
        let extension = if left.is_ok() {
            chosen.snapshot()
        } else {
            append(&mut fork, "extension");
            fork.snapshot()
        };
        reopened.advance(&extension).unwrap();
        assert!(reopened.load().unwrap().verify_extension(winner).is_err());
        std::fs::write(directory.join("checkpoint.json"), b"incomplete checkpoint").unwrap();
        assert!(reopened.load().is_err());
        assert!(reopened.advance(&extension).is_err());
        std::fs::remove_dir_all(directory).unwrap();
    }
}
