use super::{
    Confirmation, CurrentUse, DpopObservation, Grant, Identity, ReplayGuard, SenderObservation,
    Target,
};

fn observed(audience: &str, scope: &str) -> CurrentUse {
    let identity = Identity {
        issuer: "issuer".into(),
        subject: "subject".into(),
        client: "client".into(),
    };
    CurrentUse {
        grant: Grant {
            identity: identity.clone(),
            audiences: vec![audience.into()],
            scopes: vec![scope.into()],
            token_hash: "access-token-digest".into(),
            not_before: 10,
            expires_at: 20,
            confirmation: Confirmation::Dpop("key".into()),
        },
        target: Target {
            identity,
            audience: audience.into(),
            required_scopes: vec![scope.into()],
            method: "GET".into(),
            uri: "https://gateway.example/resource".into(),
        },
        sender: SenderObservation::Dpop(DpopObservation {
            thumbprint: "key".into(),
            method: "GET".into(),
            uri: "https://gateway.example/resource".into(),
            token_hash: "access-token-digest".into(),
            issued_at: 12,
            proof_id: "proof".into(),
            signature_verified: true,
            nonce_satisfied: true,
        }),
        now: 13,
        max_proof_age: 5,
        token_authenticated: true,
        active: true,
    }
}

#[test]
fn agentcore_and_fhir_share_one_atomic_proof_reservation() {
    let guard = ReplayGuard::default();
    let mut agentcore = observed("agentcore", "invoke");
    agentcore.grant.audiences.push("fhir".into());
    agentcore.grant.scopes.push("patient.read".into());
    let mut fhir = agentcore.clone();
    fhir.target.audience = "fhir".into();
    fhir.target.required_scopes = vec!["patient.read".into()];
    // The same authenticated issuer, proof key and proof ID cannot be
    // accepted twice by two routes using the shared reservation authority.
    assert!(!guard.admit(false, &agentcore).unwrap());
    let start = std::sync::Barrier::new(2);
    let (agent, health) = std::thread::scope(|threads| {
        let agent = threads.spawn(|| {
            start.wait();
            guard.admit(true, &agentcore).unwrap()
        });
        start.wait();
        let health = guard.admit(true, &fhir).unwrap();
        (agent.join().unwrap(), health)
    });
    assert_ne!(agent, health);
    assert!(!guard.admit(true, &agentcore).unwrap());
    assert!(!guard.admit(true, &fhir).unwrap());
}

#[test]
fn revoked_grant_rejects_fresh_proof_and_current_certificate() {
    let guard = ReplayGuard::default();
    let mut use_at_receiver = observed("fhir", "patient.read");
    assert!(guard.admit(true, &use_at_receiver).unwrap());
    if let SenderObservation::Dpop(proof) = &mut use_at_receiver.sender {
        proof.proof_id = "fresh-after-revocation".into();
    }
    use_at_receiver.active = false;
    assert!(!guard.admit(true, &use_at_receiver).unwrap());

    let mut mtls = observed("agentcore", "invoke");
    mtls.grant.confirmation = Confirmation::Mtls("client-certificate".into());
    assert!(!guard.admit(true, &mtls).unwrap());
    mtls.sender = SenderObservation::Mtls("different-certificate".into());
    assert!(!guard.admit(true, &mtls).unwrap());
    mtls.sender = SenderObservation::Mtls("client-certificate".into());
    assert!(guard.admit(true, &mtls).unwrap());
    mtls.active = false;
    assert!(!guard.admit(true, &mtls).unwrap());
}

#[test]
fn wrong_resource_or_bound_request_cannot_use_valid_proof() {
    let guard = ReplayGuard::default();
    let valid = observed("agentcore", "invoke");
    let mut wrong = valid.clone();
    wrong.target.audience = "fhir".into();
    assert!(!guard.admit(true, &wrong).unwrap());
    let mut wrong = valid.clone();
    wrong.target.required_scopes = vec!["admin".into()];
    assert!(!guard.admit(true, &wrong).unwrap());
    let mut wrong = valid.clone();
    wrong.target.method = "POST".into();
    assert!(!guard.admit(true, &wrong).unwrap());
    let mut wrong = valid.clone();
    wrong.now = 20;
    assert!(!guard.admit(true, &wrong).unwrap());
    assert!(guard.admit(true, &valid).unwrap());
}
