use super::{CodeLedger, Issued, Request, Session};
use crate::gateway::oauth::{
    Confirmation, CurrentUse, Grant, Identity, ReplayGuard, SenderObservation, Target,
};

const VERIFIER: &str = "dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk";
const CHALLENGE: &str = "E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM";

fn fixture() -> (Session, Request, Issued) {
    let identity = Identity {
        issuer: "issuer".into(),
        subject: "subject".into(),
        client: "client".into(),
    };
    let session = Session {
        issuer: identity.issuer.clone(),
        client: identity.client.clone(),
        redirect: "https://client.example/callback".into(),
        state: "state".into(),
        browser: "browser".into(),
        s256: CHALLENGE.into(),
    };
    let request = Request {
        code: "code".into(),
        response_issuer: session.issuer.clone(),
        client: session.client.clone(),
        redirect: session.redirect.clone(),
        state: session.state.clone(),
        browser: session.browser.clone(),
        verifier: VERIFIER.into(),
    };
    let grant = Grant {
        identity,
        audiences: vec!["fhir".into()],
        scopes: vec!["patient.read".into()],
        token_hash: "token-hash".into(),
        not_before: 10,
        expires_at: 20,
        confirmation: Confirmation::Mtls("cert".into()),
    };
    let item = Issued {
        code: request.code.clone(),
        session: session.clone(),
        grant,
        expires_at: 15,
    };
    (session, request, item)
}

#[test]
fn mixup_redirect_session_and_pkce_fail_without_consuming_the_code() {
    let (session, request, item) = fixture();
    let duplicate = CodeLedger::new(vec![item.clone(), item.clone()]);
    assert!(duplicate.redeem(&session, &request, 12).unwrap().is_none());
    let ledger = CodeLedger::new(vec![item]);
    for wrong in [
        Request {
            response_issuer: "other".into(),
            ..request.clone()
        },
        Request {
            redirect: format!("{}?x=1", session.redirect),
            ..request.clone()
        },
        Request {
            browser: "other".into(),
            ..request.clone()
        },
        Request {
            state: "other".into(),
            ..request.clone()
        },
        Request {
            client: "other".into(),
            ..request.clone()
        },
        Request {
            verifier: "x".repeat(43),
            ..request.clone()
        },
        Request {
            verifier: "too-short".into(),
            ..request.clone()
        },
    ] {
        assert!(ledger.redeem(&session, &wrong, 12).unwrap().is_none());
    }
    assert!(ledger.redeem(&session, &request, 15).unwrap().is_none());
    assert!(ledger.redeem(&session, &request, 12).unwrap().is_some());
}

#[test]
fn one_concurrent_redemption_and_fresh_resource_check() {
    let (session, request, item) = fixture();
    let ledger = CodeLedger::new(vec![item.clone()]);
    let start = std::sync::Barrier::new(2);
    let (first, second) = std::thread::scope(|threads| {
        let first = threads.spawn(|| {
            start.wait();
            ledger.redeem(&session, &request, 12).unwrap()
        });
        start.wait();
        let second = ledger.redeem(&session, &request, 12).unwrap();
        (first.join().unwrap(), second)
    });
    assert_ne!(first.is_some(), second.is_some());
    let redeemed = first.or(second).unwrap();
    assert!(ledger.redeem(&session, &request, 12).unwrap().is_none());
    let guard = ReplayGuard::default();
    let mut actual = CurrentUse {
        target: Target {
            identity: item.grant.identity.clone(),
            audience: "fhir".into(),
            required_scopes: vec!["patient.read".into()],
            method: "GET".into(),
            uri: "https://gateway.example/patient".into(),
        },
        grant: item.grant,
        sender: SenderObservation::Mtls("cert".into()),
        now: 12,
        max_proof_age: 5,
        token_authenticated: true,
        active: true,
    };
    assert!(redeemed.admit_use(&guard, true, &actual).unwrap());
    assert!(!redeemed.admit_use(&guard, false, &actual).unwrap());
    actual.grant.token_hash = "substitute".into();
    assert!(!redeemed.admit_use(&guard, true, &actual).unwrap());
    actual.grant.token_hash = "token-hash".into();
    actual.active = false;
    assert!(!redeemed.admit_use(&guard, true, &actual).unwrap());
}
