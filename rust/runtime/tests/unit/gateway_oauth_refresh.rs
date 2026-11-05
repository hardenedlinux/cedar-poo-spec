use super::{RefreshDigest, RefreshEnrollment, RefreshExchange, RefreshLedger, RefreshRequest};
use crate::gateway::oauth::{
    Confirmation, CurrentUse, DpopObservation, Grant, Identity, ReplayGuard, SenderObservation,
    Target,
};
use crate::gateway::oauth_code;
use crate::gateway::oauth_par::{
    Authorization, Credential, ParLedger, ParRequest, ParSender, ParTokenRequest, ParUri, Push,
    Registration, TokenSender, VerifiedClient, VerifiedTokenDpop,
};

fn verified<T>(request: T) -> VerifiedClient<T> {
    VerifiedClient {
        issuer: "issuer".into(),
        client: "client".into(),
        credential: Credential::PrivateKeyJwt("client-key".into()),
        request,
    }
}

fn token_sender(confirmation: &Confirmation) -> TokenSender {
    match confirmation {
        Confirmation::Dpop(key) => TokenSender::Dpop(VerifiedTokenDpop(key.clone())),
        Confirmation::Mtls(peer) => TokenSender::Mtls(peer.clone()),
    }
}

fn digest() -> RefreshDigest {
    RefreshDigest("refresh-digest".into())
}

fn enroll(ledger: &RefreshLedger, confirmation: Confirmation) -> Grant {
    enroll_with(confirmation, |input| ledger.enroll(input).unwrap())
}

fn enroll_with(
    confirmation: Confirmation,
    commit: impl FnOnce(RefreshEnrollment) -> bool,
) -> Grant {
    let session = oauth_code::Session {
        issuer: "issuer".into(),
        client: "client".into(),
        redirect: "https://client.example/callback".into(),
        state: "state".into(),
        browser: "browser".into(),
        s256: "E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM".into(),
    };
    let grant = Grant {
        identity: Identity {
            issuer: session.issuer.clone(),
            client: session.client.clone(),
            subject: "subject".into(),
        },
        audiences: vec!["fhir".into()],
        scopes: vec!["patient.read".into()],
        token_hash: "initial".into(),
        not_before: 10,
        expires_at: 15,
        confirmation,
    };
    let registration = Registration {
        issuer: session.issuer.clone(),
        client: session.client.clone(),
        credential: Credential::PrivateKeyJwt("client-key".into()),
        redirects: vec![session.redirect.clone()],
        scopes: grant.scopes.clone(),
    };
    let par = ParLedger::default();
    assert!(
        par.push(Push {
            registration: &registration,
            verified: verified(ParRequest {
                session: session.clone(),
                audiences: grant.audiences.clone(),
                scopes: grant.scopes.clone(),
                sender: match &grant.confirmation {
                    Confirmation::Dpop(key) => ParSender::Dpop {
                        jkt: Some(key.clone()),
                        proof: None
                    },
                    Confirmation::Mtls(_) => ParSender::Mtls,
                },
            }),
            uri: ParUri("par"),
            now: 10,
            expires_at: 16,
        })
        .unwrap()
    );
    let code = par
        .authorize(Authorization {
            expected_uri: ParUri("par"),
            session: &session,
            uri: ParUri("par"),
            client: &session.client,
            has_extra_parameters: false,
            now: 11,
            code: "code".into(),
            code_expires_at: 15,
            grant: grant.clone(),
        })
        .unwrap()
        .unwrap();
    let redeemed = code
        .redeem(
            &verified(ParTokenRequest {
                redemption: oauth_code::Request {
                    code: "code".into(),
                    response_issuer: session.issuer,
                    client: session.client,
                    redirect: session.redirect,
                    state: session.state,
                    browser: session.browser,
                    verifier: "dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk".into(),
                },
                sender: token_sender(&grant.confirmation),
            }),
            12,
        )
        .unwrap()
        .unwrap();
    assert!(commit(RefreshEnrollment {
        redeemed,
        digest: digest(),
        now: 12,
        expires_at: 40,
    }));
    grant
}

fn exchange(original: &Grant, hash: &str, now: u64) -> RefreshExchange {
    let mut next = original.clone();
    next.token_hash = hash.into();
    next.not_before = now;
    next.expires_at = now + 12;
    RefreshExchange {
        verified: verified(RefreshRequest {
            digest: digest(),
            sender: token_sender(&original.confirmation),
        }),
        next,
        now,
    }
}

fn actual(grant: Grant, now: u64, proof_id: &str) -> CurrentUse {
    let target = Target {
        identity: grant.identity.clone(),
        audience: "fhir".into(),
        required_scopes: vec!["patient.read".into()],
        method: "GET".into(),
        uri: "https://gateway.example/patient".into(),
    };
    let sender = match &grant.confirmation {
        Confirmation::Mtls(peer) => SenderObservation::Mtls(peer.clone()),
        Confirmation::Dpop(key) => SenderObservation::Dpop(DpopObservation {
            thumbprint: key.clone(),
            method: target.method.clone(),
            uri: target.uri.clone(),
            token_hash: grant.token_hash.clone(),
            issued_at: now,
            proof_id: proof_id.into(),
            signature_verified: true,
            nonce_satisfied: true,
        }),
    };
    CurrentUse {
        grant,
        target,
        sender,
        now,
        max_proof_age: 5,
        token_authenticated: true,
        active: true,
    }
}

#[test]
fn refresh_requires_original_sender_and_revokes_every_linked_access_token() {
    for (confirmation, replacement) in [
        (
            Confirmation::Dpop("key".into()),
            Confirmation::Dpop("other-key".into()),
        ),
        (
            Confirmation::Mtls("cert".into()),
            Confirmation::Mtls("other-cert".into()),
        ),
    ] {
        let ledger = RefreshLedger::default();
        let original = enroll(&ledger, confirmation);
        let mut wrong = exchange(&original, "next", 13);
        wrong.verified.request.sender = token_sender(&replacement);
        assert!(ledger.refresh(wrong).unwrap().is_none());
        let mut changed = exchange(&original, "next", 13);
        changed.next.confirmation = replacement.clone();
        assert!(ledger.refresh(changed).unwrap().is_none());
        let mut broadened = exchange(&original, "next", 13);
        broadened.next.scopes.push("patient.write".into());
        assert!(ledger.refresh(broadened).unwrap().is_none());
        let mut other = exchange(&original, "next", 13);
        other.verified.client = "other".into();
        assert!(ledger.refresh(other).unwrap().is_none());

        let first = ledger
            .refresh(exchange(&original, "first", 13))
            .unwrap()
            .unwrap();
        let second = ledger
            .refresh(exchange(&original, "second", 14))
            .unwrap()
            .unwrap();
        assert!(
            ledger
                .refresh(exchange(&original, "first", 14))
                .unwrap()
                .is_none()
        );
        assert!(
            ledger
                .refresh(exchange(&original, "expired", 40))
                .unwrap()
                .is_none()
        );
        let guard = ReplayGuard::default();
        for (i, grant) in [&original, &first, &second].into_iter().enumerate() {
            let mut request = actual(grant.clone(), 14, &format!("before-{i}"));
            let mut substitute = grant.clone();
            substitute.confirmation = replacement.clone();
            request.sender = actual(substitute, 14, "replacement").sender;
            assert!(!ledger.admit_use(&guard, true, &request).unwrap());
            assert!(
                ledger
                    .admit_use(
                        &guard,
                        true,
                        &actual(grant.clone(), 14, &format!("before-{i}"))
                    )
                    .unwrap()
            );
        }
        let mut wrong_client = verified(digest());
        wrong_client.client = "other".into();
        assert!(!ledger.revoke(wrong_client).unwrap());
        assert!(ledger.revoke(verified(digest())).unwrap());
        assert!(ledger.revoke(verified(digest())).unwrap());
        assert!(
            ledger
                .refresh(exchange(&original, "after", 14))
                .unwrap()
                .is_none()
        );
        for (i, grant) in [original, first, second].into_iter().enumerate() {
            assert!(
                !ledger
                    .admit_use(&guard, true, &actual(grant, 14, &format!("after-{i}")))
                    .unwrap()
            );
        }
    }
}

#[test]
fn racing_refresh_is_either_refused_or_revoked_with_its_family() {
    let ledger = RefreshLedger::default();
    let original = enroll(&ledger, Confirmation::Dpop("key".into()));
    let start = std::sync::Barrier::new(2);
    let raced = std::thread::scope(|threads| {
        let refresh = threads.spawn(|| {
            start.wait();
            ledger.refresh(exchange(&original, "race", 13)).unwrap()
        });
        start.wait();
        assert!(ledger.revoke(verified(digest())).unwrap());
        refresh.join().unwrap()
    });
    let guard = ReplayGuard::default();
    if let Some(grant) = raced {
        assert!(
            !ledger
                .admit_use(&guard, true, &actual(grant, 14, "raced"))
                .unwrap()
        );
    }
    assert!(
        ledger
            .refresh(exchange(&original, "later", 14))
            .unwrap()
            .is_none()
    );
}

#[test]
fn a_stale_replica_cannot_observe_an_acknowledged_revocation() {
    let authority = RefreshLedger::default();
    let replica = RefreshLedger::default();
    let original = enroll(&authority, Confirmation::Dpop("key".into()));
    assert_eq!(original, enroll(&replica, Confirmation::Dpop("key".into())));
    let issued = authority
        .refresh(exchange(&original, "issued", 13))
        .unwrap()
        .unwrap();
    assert_eq!(
        replica.refresh(exchange(&original, "issued", 13)).unwrap(),
        Some(issued.clone())
    );

    assert!(authority.revoke(verified(digest())).unwrap());
    let request = actual(issued, 14, "same-fresh-proof");
    assert!(
        !authority
            .admit_use(&ReplayGuard::default(), true, &request)
            .unwrap()
    );
    assert!(
        replica
            .admit_use(&ReplayGuard::default(), true, &request)
            .unwrap()
    );
    assert!(
        authority
            .refresh(exchange(&original, "later", 14))
            .unwrap()
            .is_none()
    );
    assert!(
        replica
            .refresh(exchange(&original, "later", 14))
            .unwrap()
            .is_some()
    );
}

#[test]
fn final_effect_rejects_old_forked_and_changed_checkpoints() {
    let ledger = RefreshLedger::default();
    let original = enroll(&ledger, Confirmation::Dpop("key".into()));
    let issued = ledger
        .refresh(exchange(&original, "issued", 13))
        .unwrap()
        .unwrap();
    let checked = ledger.checkpoint().unwrap();
    let current = actual(issued, 14, "actual-proof");
    let guard = ReplayGuard::default();
    let input = |checked, replica| super::FinalRefreshUse {
        checked,
        replica,
        current: &current,
        guard: &guard,
        base_allowed: true,
    };

    let unrelated = RefreshLedger::default();
    enroll(&unrelated, Confirmation::Dpop("key".into()));
    unrelated
        .refresh(exchange(&original, "issued", 13))
        .unwrap()
        .unwrap();
    let foreign = unrelated.checkpoint().unwrap();
    assert_eq!(foreign.image.position, checked.image.position);
    assert!(
        !ledger
            .execute_final(input(&foreign, &foreign), || panic!("foreign effect"))
            .unwrap()
    );

    let inspected = actual(current.grant.clone(), 14, "preview");
    assert!(
        ledger
            .admit_use(&ReplayGuard::default(), true, &inspected)
            .unwrap()
    );
    assert!(ledger.revoke(verified(digest())).unwrap());
    let live = ledger.checkpoint().unwrap();
    let mut forged = checked.clone();
    std::sync::Arc::make_mut(&mut forged.image).position = live.image.position;
    for (prepared, replica) in [
        (&checked, &checked),
        (&forged, &forged),
        (&checked, &live),
        (&live, &live),
    ] {
        assert!(
            !ledger
                .execute_final(input(prepared, replica), || panic!("revoked effect"))
                .unwrap()
        );
    }
}

#[test]
fn final_observer_and_revocation_share_the_same_ordering() {
    let ledger = RefreshLedger::default();
    let grant = enroll(&ledger, Confirmation::Dpop("key".into()));
    let checked = ledger.checkpoint().unwrap();
    let current = actual(grant, 14, "first");
    let guard = ReplayGuard::default();
    let input = || super::FinalRefreshUse {
        checked: &checked,
        replica: &checked,
        current: &current,
        guard: &guard,
        base_allowed: true,
    };
    let (entered, wait_for_effect) = std::sync::mpsc::channel();
    let (revoking, wait_for_revoke) = std::sync::mpsc::channel();
    let completed = std::sync::atomic::AtomicBool::new(false);
    use std::sync::atomic::Ordering;
    std::thread::scope(|threads| {
        let completed = &completed;
        let ledger = &ledger;
        let writer = threads.spawn(move || {
            wait_for_effect.recv().unwrap();
            revoking.send(()).unwrap();
            assert!(ledger.revoke(verified(digest())).unwrap());
            completed.store(true, Ordering::SeqCst);
        });
        assert!(
            ledger
                .execute_final(input(), || {
                    entered.send(()).unwrap();
                    drop(entered);
                    wait_for_revoke.recv().unwrap();
                    assert!(matches!(
                        ledger.image.try_lock(),
                        Err(std::sync::TryLockError::WouldBlock)
                    ));
                    assert!(!completed.load(Ordering::SeqCst));
                })
                .unwrap()
        );
        writer.join().unwrap();
    });
    assert!(completed.load(Ordering::SeqCst));
    assert!(
        !ledger
            .execute_final(input(), || panic!("late effect"))
            .unwrap()
    );
}

#[cfg(unix)]
use crate::gateway::oauth_refresh_durable::{
    DurableFinalUse, DurableRefreshLedger, DurableRevocationCheckpoint,
};

#[cfg(unix)]
fn durable_directory(case: &str) -> std::path::PathBuf {
    let directory = std::env::temp_dir().join(format!("cedar-oauth-{case}-{}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    directory
}

#[cfg(unix)]
#[test]
fn durable_worker_revocation_survives_reopening_and_refuses_stale_replica() {
    const WORKER_DIR: &str = "CEDAR_OAUTH_DURABLE_TEST_WORKER_DIR";
    if let Some(directory) = std::env::var_os(WORKER_DIR) {
        let worker = DurableRefreshLedger::new(std::path::Path::new(&directory), "authority");
        assert!(worker.revoke(verified(digest())).unwrap());
        return;
    }

    let directory = durable_directory("restart");
    let (grant, saved) = {
        let writer = DurableRefreshLedger::new(&directory, "authority");
        assert!(writer.checkpoint().is_err());
        writer.initialize().unwrap();
        assert!(writer.initialize().is_err());
        let original = enroll_with(Confirmation::Dpop("key".into()), |input| {
            writer.enroll(input).unwrap()
        });
        let grant = writer
            .refresh(exchange(&original, "issued", 13))
            .unwrap()
            .unwrap();
        let checked = writer.checkpoint().unwrap();
        let actual = actual(grant.clone(), 14, "persisted-proof");
        assert!(
            writer
                .execute_final(
                    DurableFinalUse {
                        checked: &checked,
                        replica: &checked,
                        current: &actual,
                        base_allowed: true,
                    },
                    || {}
                )
                .unwrap()
        );
        (grant, serde_json::to_vec(&checked).unwrap())
    };

    let restored = DurableRefreshLedger::new(&directory, "authority");
    let replica: DurableRevocationCheckpoint = serde_json::from_slice(&saved).unwrap();
    assert!(restored.recover(&replica).unwrap());
    let replay = actual(grant.clone(), 14, "persisted-proof");
    assert!(
        !restored
            .execute_final(
                DurableFinalUse {
                    checked: &replica,
                    replica: &replica,
                    current: &replay,
                    base_allowed: true,
                },
                || panic!("replayed effect")
            )
            .unwrap()
    );

    let worker = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "gateway::oauth_refresh::tests::durable_worker_revocation_survives_reopening_and_refuses_stale_replica"])
        .env(WORKER_DIR, &directory)
        .output()
        .unwrap();
    assert!(
        worker.status.success(),
        "{}",
        String::from_utf8_lossy(&worker.stdout)
    );
    assert!(String::from_utf8_lossy(&worker.stdout).contains("1 passed"));

    let restarted = DurableRefreshLedger::new(&directory, "authority");
    assert!(!restarted.recover(&replica).unwrap());
    assert!(
        restarted
            .refresh(exchange(&grant, "after-revoke", 14))
            .unwrap()
            .is_none()
    );
    let live = restarted.checkpoint().unwrap();
    assert!(restarted.recover(&live).unwrap());
    let mut forged: serde_json::Value = serde_json::from_slice(&saved).unwrap();
    forged["ledger"]["position"] =
        serde_json::to_value(&live).unwrap()["ledger"]["position"].clone();
    let forged = serde_json::from_value(forged).unwrap();
    assert!(!restarted.recover(&forged).unwrap());
    let current = actual(grant, 14, "fresh-proof");
    for (checked, view) in [
        (&replica, &replica),
        (&forged, &forged),
        (&replica, &live),
        (&live, &live),
    ] {
        assert!(
            !restarted
                .execute_final(
                    DurableFinalUse {
                        checked,
                        replica: view,
                        current: &current,
                        base_allowed: true,
                    },
                    || panic!("revoked effect")
                )
                .unwrap()
        );
    }
    assert!(
        DurableRefreshLedger::new(&directory, "another-authority")
            .recover(&live)
            .is_err()
    );
    std::fs::write(directory.join("checkpoint.json"), b"invalid").unwrap();
    assert!(restarted.recover(&live).is_err());
    assert!(restarted.initialize().is_err());
    std::fs::remove_file(directory.join("checkpoint.json")).unwrap();
    assert!(restarted.recover(&replica).is_err());
    std::fs::remove_dir_all(directory).unwrap();
}

#[cfg(unix)]
#[test]
fn durable_final_effect_and_revocation_share_the_writer_lock() {
    let directory = durable_directory("ordering");
    let reader = DurableRefreshLedger::new(&directory, "authority");
    let writer = DurableRefreshLedger::new(&directory, "authority");
    reader.initialize().unwrap();
    let grant = enroll_with(Confirmation::Mtls("cert".into()), |input| {
        reader.enroll(input).unwrap()
    });
    let checked = reader.checkpoint().unwrap();
    let current = actual(grant, 14, "certificate");
    let input = || DurableFinalUse {
        checked: &checked,
        replica: &checked,
        current: &current,
        base_allowed: true,
    };
    let (enter, effect_started) = std::sync::mpsc::channel();
    let (revoke, writer_started) = std::sync::mpsc::channel();
    std::thread::scope(|workers| {
        let writer = workers.spawn(move || {
            effect_started.recv().unwrap();
            revoke.send(()).unwrap();
            writer.revoke(verified(digest())).unwrap()
        });
        assert!(
            reader
                .execute_final(input(), || {
                    enter.send(()).unwrap();
                    drop(enter);
                    writer_started.recv().unwrap();
                    let independent = std::fs::OpenOptions::new()
                        .read(true)
                        .write(true)
                        .open(directory.join("checkpoint.lock"))
                        .unwrap();
                    assert!(matches!(
                        independent.try_lock(),
                        Err(std::fs::TryLockError::WouldBlock)
                    ));
                })
                .unwrap()
        );
        assert!(writer.join().unwrap());
    });
    assert!(
        !reader
            .execute_final(input(), || panic!("late effect"))
            .unwrap()
    );
    std::fs::remove_dir_all(directory).unwrap();
}

#[cfg(unix)]
#[test]
fn staged_and_durable_revoke_crashes_restore_the_correct_image() {
    use crate::gateway::checkpoint_store::CheckpointStage;
    for (phase, name) in [
        (CheckpointStage::Staged, "staged"),
        (CheckpointStage::Durable, "durable"),
    ] {
        let directory = durable_directory(name);
        let (grant, old) = {
            let writer = DurableRefreshLedger::new(&directory, "authority");
            writer.initialize().unwrap();
            let grant = enroll_with(Confirmation::Mtls("cert".into()), |input| {
                writer.enroll(input).unwrap()
            });
            let old = writer.checkpoint().unwrap();
            assert_eq!(
                writer
                    .revoke_with_crash(verified(digest()), phase)
                    .unwrap_err(),
                "simulated checkpoint crash"
            );
            (grant, old)
        };
        let reopened = DurableRefreshLedger::new(&directory, "authority");
        let staged = phase == CheckpointStage::Staged;
        assert_eq!(directory.join("checkpoint.staged").exists(), staged);
        assert_eq!(reopened.recover(&old).unwrap(), staged);
        let current = actual(grant, 14, "proof");
        assert_eq!(
            reopened
                .execute_final(
                    DurableFinalUse {
                        checked: &old,
                        replica: &old,
                        current: &current,
                        base_allowed: true,
                    },
                    || {}
                )
                .unwrap(),
            staged
        );
        assert!(reopened.revoke(verified(digest())).unwrap());
        assert!(!reopened.recover(&old).unwrap());
        std::fs::remove_dir_all(directory).unwrap();
    }
}

#[cfg(unix)]
#[path = "gateway_oauth_refresh/receiver.rs"]
mod receiver;

#[cfg(unix)]
#[path = "gateway_oauth_refresh/settlement.rs"]
mod settlement;
