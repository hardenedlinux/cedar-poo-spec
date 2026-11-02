use super::{CredentialMode, Grant, Scope};
fn scope() -> Scope<u8> {
    Scope {
        case_id: "case".into(),
        claim_digest: "digest".into(),
        source_actor: 1,
        target_actor: 2,
        source_root: "claims".into(),
        target_root: "bank".into(),
        credential_mode: "m2m".to_owned().try_into().expect("nonempty mode"),
    }
}
#[test]
fn current_exact_scope_is_required() {
    let expected = scope();
    let grant = Grant {
        scope: expected.clone(),
        epoch: 7,
        expires_at: 20,
    };
    assert!(grant.admits(&expected, 7, 19));
    assert!(!grant.admits(&expected, 8, 19));
    assert!(!grant.admits(&expected, 7, 20));
    for field in 0..7 {
        let mut changed = expected.clone();
        match field {
            0 => changed.case_id.push('x'),
            1 => changed.claim_digest.push('x'),
            2 => changed.source_actor = 3,
            3 => changed.target_actor = 3,
            4 => changed.source_root.push('x'),
            5 => changed.target_root.push('x'),
            _ => changed.credential_mode = "other".to_owned().try_into().unwrap(),
        }
        assert!(!grant.admits(&changed, 7, 19));
    }
}
#[test]
fn malformed_scope_refuses_even_an_identical_grant() {
    assert!(CredentialMode::try_from(String::new()).is_err());
    for field in 0..5 {
        let mut invalid = scope();
        match field {
            0 => invalid.case_id.clear(),
            1 => invalid.claim_digest.clear(),
            2 => invalid.source_root.clear(),
            3 => invalid.target_root.clear(),
            _ => invalid.target_actor = invalid.source_actor,
        }
        let grant = Grant {
            scope: invalid.clone(),
            epoch: 7,
            expires_at: 20,
        };
        assert!(!grant.admits(&invalid, 7, 19));
    }
}
