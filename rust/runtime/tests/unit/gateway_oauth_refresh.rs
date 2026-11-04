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
    assert!(
        ledger
            .enroll(RefreshEnrollment {
                redeemed,
                digest: digest(),
                now: 12,
                expires_at: 40,
            })
            .unwrap()
    );
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
