use super::{
    Authorization, Credential, ParLedger, ParRequest, ParUri, Push, Registration, Session,
    VerifiedClient,
};
use crate::gateway::oauth::{
    Confirmation, CurrentUse, Grant, Identity, ReplayGuard, SenderObservation, Target,
};
use crate::gateway::oauth_code;
use std::sync::Barrier;

struct Fixture {
    registration: Registration,
    session: Session,
    grant: Grant,
}

impl Fixture {
    fn new(credential: Credential) -> Self {
        let session = Session {
            issuer: "issuer".into(),
            client: "client".into(),
            redirect: "https://client.example/callback".into(),
            state: "state".into(),
            browser: "browser".into(),
            s256: "E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM".into(),
        };
        let registration = Registration {
            issuer: session.issuer.clone(),
            client: session.client.clone(),
            credential,
            redirects: vec![session.redirect.clone()],
            scopes: vec!["patient.read".into()],
        };
        let grant = Grant {
            identity: Identity {
                issuer: session.issuer.clone(),
                client: session.client.clone(),
                subject: "subject".into(),
            },
            audiences: vec!["fhir".into()],
            scopes: vec!["patient.read".into()],
            token_hash: "token-hash".into(),
            not_before: 10,
            expires_at: 20,
            confirmation: Confirmation::Mtls("sender-cert".into()),
        };
        Self {
            registration,
            session,
            grant,
        }
    }

    fn verified<T>(&self, request: T) -> VerifiedClient<T> {
        VerifiedClient {
            issuer: self.session.issuer.clone(),
            client: self.session.client.clone(),
            credential: self.registration.credential.clone(),
            request,
        }
    }

    fn pushed(&self) -> VerifiedClient<ParRequest> {
        self.verified(ParRequest {
            session: self.session.clone(),
            audiences: self.grant.audiences.clone(),
            scopes: self.grant.scopes.clone(),
        })
    }

    fn push<'a>(&'a self, uri: &'a str) -> Push<'a> {
        Push {
            registration: &self.registration,
            verified: self.pushed(),
            uri: ParUri(uri),
            now: 10,
            expires_at: 15,
        }
    }

    fn authorization(&self) -> Authorization<'_> {
        Authorization {
            expected_uri: ParUri("par"),
            session: &self.session,
            uri: ParUri("par"),
            client: &self.session.client,
            has_extra_parameters: false,
            now: 12,
            code: "code".into(),
            code_expires_at: 17,
            grant: self.grant.clone(),
        }
    }

    fn token(&self) -> VerifiedClient<oauth_code::Request> {
        self.verified(oauth_code::Request {
            code: "code".into(),
            response_issuer: self.session.issuer.clone(),
            client: self.session.client.clone(),
            redirect: self.session.redirect.clone(),
            state: self.session.state.clone(),
            browser: self.session.browser.clone(),
            verifier: "dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk".into(),
        })
    }
}

#[test]
fn rejects_par_replacement_and_cross_client_or_issuer_reference() {
    let f = Fixture::new(Credential::Mtls("client-cert".into()));
    let ledger = ParLedger::default();
    let mut wrong = f.pushed();
    wrong.issuer = "other".into();
    assert!(
        !ledger
            .push(Push {
                verified: wrong,
                ..f.push("par")
            })
            .unwrap()
    );
    let mut wrong = f.pushed();
    wrong.credential = Credential::PrivateKeyJwt("client-cert".into());
    assert!(
        !ledger
            .push(Push {
                verified: wrong,
                ..f.push("par")
            })
            .unwrap()
    );
    let mut wrong = f.pushed();
    wrong.request.scopes.push("patient.write".into());
    assert!(
        !ledger
            .push(Push {
                verified: wrong,
                ..f.push("par")
            })
            .unwrap()
    );
    let mut wrong = f.pushed();
    wrong.request.session.redirect.push_str("?override=1");
    assert!(
        !ledger
            .push(Push {
                verified: wrong,
                ..f.push("par")
            })
            .unwrap()
    );
    assert!(
        !ledger
            .push(Push {
                expires_at: 610,
                ..f.push("par")
            })
            .unwrap()
    );
    assert!(ledger.push(f.push("par")).unwrap());
    assert!(ledger.push(f.push("other")).unwrap());

    let mut wrong_issuer = f.session.clone();
    wrong_issuer.issuer = "other".into();
    let mut wrong_browser = f.session.clone();
    wrong_browser.browser = "other".into();
    let mut broadened = f.grant.clone();
    broadened.scopes.push("patient.write".into());
    for attempt in [
        Authorization {
            uri: ParUri("other"),
            ..f.authorization()
        },
        Authorization {
            client: "other",
            ..f.authorization()
        },
        Authorization {
            session: &wrong_issuer,
            ..f.authorization()
        },
        Authorization {
            session: &wrong_browser,
            ..f.authorization()
        },
        Authorization {
            has_extra_parameters: true,
            ..f.authorization()
        },
        Authorization {
            now: 15,
            ..f.authorization()
        },
        Authorization {
            grant: broadened,
            ..f.authorization()
        },
    ] {
        assert!(ledger.authorize(attempt).unwrap().is_none());
    }

    let barrier = Barrier::new(2);
    std::thread::scope(|threads| {
        let worker = threads.spawn(|| {
            barrier.wait();
            ledger.authorize(f.authorization()).unwrap().is_some()
        });
        barrier.wait();
        let authorized = ledger.authorize(f.authorization()).unwrap().is_some();
        assert_ne!(authorized, worker.join().unwrap());
    });
    assert!(!ledger.push(f.push("par")).unwrap());
    assert!(
        ledger
            .authorize(Authorization {
                expected_uri: ParUri("other"),
                uri: ParUri("other"),
                ..f.authorization()
            })
            .unwrap()
            .is_none()
    );
}

#[test]
fn authenticates_the_bound_code_once_and_checks_current_resource_access() {
    for credential in [
        Credential::Mtls("client-cert".into()),
        Credential::PrivateKeyJwt("client-jwt-key".into()),
    ] {
        let f = Fixture::new(credential);
        let ledger = ParLedger::default();
        assert!(ledger.push(f.push("par")).unwrap());
        let authorized = ledger.authorize(f.authorization()).unwrap().unwrap();
        let mut wrong_client = f.token();
        wrong_client.client = "other".into();
        let mut wrong_credential = f.token();
        wrong_credential.credential = Credential::Mtls("replacement".into());
        let mut wrong_callback = f.token();
        wrong_callback.request.response_issuer = "other".into();
        let mut wrong_verifier = f.token();
        wrong_verifier.request.verifier = "a".repeat(43);
        let mut wrong_endpoint = f.token();
        wrong_endpoint.issuer = "other".into();
        for token in [
            wrong_client,
            wrong_credential,
            wrong_callback,
            wrong_verifier,
            wrong_endpoint,
        ] {
            assert!(authorized.redeem(&token, 13).unwrap().is_none());
        }
        let redeemed = authorized.redeem(&f.token(), 13).unwrap().unwrap();
        assert!(authorized.redeem(&f.token(), 13).unwrap().is_none());
        let guard = ReplayGuard::default();
        let mut actual = CurrentUse {
            target: Target {
                identity: f.grant.identity.clone(),
                audience: "fhir".into(),
                required_scopes: vec!["patient.read".into()],
                method: "GET".into(),
                uri: "https://gateway.example/patient".into(),
            },
            grant: f.grant,
            sender: SenderObservation::Mtls("sender-cert".into()),
            now: 13,
            max_proof_age: 5,
            token_authenticated: true,
            active: true,
        };
        assert!(redeemed.admit_use(&guard, true, &actual).unwrap());
        assert!(!redeemed.admit_use(&guard, false, &actual).unwrap());
        actual.active = false;
        assert!(!redeemed.admit_use(&guard, true, &actual).unwrap());
    }
}
