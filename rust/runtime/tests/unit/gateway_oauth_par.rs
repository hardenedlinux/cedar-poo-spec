use super::{
    Authorization, Credential, ParLedger, ParRequest, ParSender, ParTokenRequest, ParUri, Push,
    Registration, Session, TokenSender, VerifiedClient, VerifiedParDpop, VerifiedTokenDpop,
};
use crate::gateway::oauth::{
    Confirmation, CurrentUse, DpopObservation, Grant, Identity, ReplayGuard, SenderObservation,
    Target,
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
        let sender_cert = match &credential {
            Credential::Mtls(peer) => peer.clone(),
            Credential::PrivateKeyJwt(_) => "sender-cert".into(),
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
            confirmation: Confirmation::Mtls(sender_cert),
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
            sender: match &self.grant.confirmation {
                Confirmation::Dpop(key) => ParSender::Dpop {
                    jkt: Some(key.clone()),
                    proof: None,
                },
                Confirmation::Mtls(_) => ParSender::Mtls,
            },
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

    fn token(&self) -> VerifiedClient<ParTokenRequest> {
        self.verified(ParTokenRequest {
            sender: match &self.grant.confirmation {
                Confirmation::Dpop(key) => TokenSender::Dpop(VerifiedTokenDpop(key.clone())),
                Confirmation::Mtls(peer) => TokenSender::Mtls(peer.clone()),
            },
            redemption: oauth_code::Request {
                code: "code".into(),
                response_issuer: self.session.issuer.clone(),
                client: self.session.client.clone(),
                redirect: self.session.redirect.clone(),
                state: self.session.state.clone(),
                browser: self.session.browser.clone(),
                verifier: "dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk".into(),
            },
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
fn rejects_overlong_codes_without_consuming_the_par_reference() {
    let f = Fixture::new(Credential::Mtls("client-cert".into()));
    let ledger = ParLedger::default();
    assert!(ledger.push(f.push("par")).unwrap());
    let mut input = f.authorization();
    input.code_expires_at = input.now + 61;
    assert!(ledger.authorize(input).unwrap().is_none());
    let mut input = f.authorization();
    input.code_expires_at = input.now;
    assert!(ledger.authorize(input).unwrap().is_none());
    let mut input = f.authorization();
    input.code_expires_at = input.now + 60;
    let expiry = input.code_expires_at;
    let authorized = ledger.authorize(input).unwrap().unwrap();
    assert!(authorized.redeem(&f.token(), expiry).unwrap().is_none());
    assert!(authorized.redeem(&f.token(), expiry - 1).unwrap().is_some());
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
        wrong_callback.request.redemption.response_issuer = "other".into();
        let mut wrong_verifier = f.token();
        wrong_verifier.request.redemption.verifier = "a".repeat(43);
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
        let mut wrong_peer = f.token();
        wrong_peer.request.sender = TokenSender::Mtls("other-peer".into());
        assert!(authorized.redeem(&wrong_peer, 13).unwrap().is_none());
        let redeemed = authorized.redeem(&f.token(), 13).unwrap().unwrap();
        assert!(authorized.redeem(&f.token(), 13).unwrap().is_none());
        let guard = ReplayGuard::default();
        let TokenSender::Mtls(peer) = f.token().request.sender else {
            unreachable!()
        };
        let mut actual = CurrentUse {
            target: Target {
                identity: f.grant.identity.clone(),
                audience: "fhir".into(),
                required_scopes: vec!["patient.read".into()],
                method: "GET".into(),
                uri: "https://gateway.example/patient".into(),
            },
            grant: f.grant,
            sender: SenderObservation::Mtls(peer.clone()),
            now: 13,
            max_proof_age: 5,
            token_authenticated: true,
            active: true,
        };
        assert!(redeemed.admit_use(&guard, true, &actual).unwrap());
        assert!(!redeemed.admit_use(&guard, false, &actual).unwrap());
        actual.sender = SenderObservation::Mtls("other-peer".into());
        assert!(!redeemed.admit_use(&guard, true, &actual).unwrap());
        actual.sender = SenderObservation::Mtls(peer);
        actual.active = false;
        assert!(!redeemed.admit_use(&guard, true, &actual).unwrap());
    }
}

#[test]
fn binds_par_dpop_key_through_issuance_and_resource_use() {
    let mut f = Fixture::new(Credential::Mtls("client-cert".into()));
    f.grant.confirmation = Confirmation::Dpop("key".into());
    for (jkt, proof) in [
        (Some("key"), None),
        (None, Some("key")),
        (Some("key"), Some("key")),
    ] {
        let ledger = ParLedger::default();
        let mut push = f.push("par");
        push.verified.request.sender = ParSender::Dpop {
            jkt: Some("key".into()),
            proof: Some(VerifiedParDpop("other".into())),
        };
        assert!(!ledger.push(push).unwrap());
        let mut push = f.push("par");
        push.verified.request.sender = ParSender::Dpop {
            jkt: None,
            proof: None,
        };
        assert!(!ledger.push(push).unwrap());
        let mut push = f.push("par");
        push.verified.request.sender = ParSender::Dpop {
            jkt: jkt.map(str::to_owned),
            proof: proof.map(|key| VerifiedParDpop(key.into())),
        };
        assert!(ledger.push(push).unwrap());
        for confirmation in [
            Confirmation::Dpop("other".into()),
            Confirmation::Mtls("client-cert".into()),
        ] {
            let mut replaced = f.authorization();
            replaced.grant.confirmation = confirmation;
            assert!(ledger.authorize(replaced).unwrap().is_none());
        }
        let authorized = ledger.authorize(f.authorization()).unwrap().unwrap();
        for sender in [
            TokenSender::Dpop(VerifiedTokenDpop("other".into())),
            TokenSender::Mtls("client-cert".into()),
        ] {
            let mut token = f.token();
            token.request.sender = sender;
            assert!(authorized.redeem(&token, 13).unwrap().is_none());
        }
        let redeemed = authorized.redeem(&f.token(), 13).unwrap().unwrap();
        assert!(authorized.redeem(&f.token(), 13).unwrap().is_none());

        let target = Target {
            identity: f.grant.identity.clone(),
            audience: "fhir".into(),
            required_scopes: vec!["patient.read".into()],
            method: "GET".into(),
            uri: "https://gateway.example/patient".into(),
        };
        let proof = DpopObservation {
            thumbprint: "key".into(),
            method: target.method.clone(),
            uri: target.uri.clone(),
            token_hash: f.grant.token_hash.clone(),
            issued_at: 13,
            proof_id: "original".into(),
            signature_verified: true,
            nonce_satisfied: true,
        };
        let mut actual = CurrentUse {
            grant: f.grant.clone(),
            target,
            sender: SenderObservation::Dpop(DpopObservation {
                thumbprint: "other".into(),
                ..proof.clone()
            }),
            now: 13,
            max_proof_age: 5,
            token_authenticated: true,
            active: true,
        };
        let guard = ReplayGuard::default();
        assert!(!redeemed.admit_use(&guard, true, &actual).unwrap());
        actual.sender = SenderObservation::Dpop(proof.clone());
        assert!(redeemed.admit_use(&guard, true, &actual).unwrap());
        assert!(!redeemed.admit_use(&guard, true, &actual).unwrap());
        actual.active = false;
        actual.sender = SenderObservation::Dpop(DpopObservation {
            proof_id: "fresh".into(),
            ..proof
        });
        assert!(!redeemed.admit_use(&guard, true, &actual).unwrap());
    }
}

#[test]
fn mtls_authentication_and_binding_share_the_token_connection() {
    let mut f = Fixture::new(Credential::Mtls("client-cert".into()));
    f.grant.confirmation = Confirmation::Mtls("different-peer".into());
    let ledger = ParLedger::default();
    assert!(ledger.push(f.push("par")).unwrap());
    let authorized = ledger.authorize(f.authorization()).unwrap().unwrap();
    // The proposed grant matches the presented sender value, but that value
    // disagrees with the mTLS client authentication on the same connection.
    assert!(authorized.redeem(&f.token(), 13).unwrap().is_none());
}
