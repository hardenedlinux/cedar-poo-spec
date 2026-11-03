use super::{MAX_SIGNED_PAYLOAD, sign, simulation_key, verify};

#[test]
fn signed_payload_limit_matches_the_public_verifier_at_the_exact_byte_boundary() {
    let key = simulation_key(10);
    let at_limit = "a".repeat(MAX_SIGNED_PAYLOAD - 2);
    let signed = sign(&at_limit, &key).unwrap();
    assert_eq!(signed.payload.len(), MAX_SIGNED_PAYLOAD);
    assert_eq!(
        verify::<String>(&signed, key.verifying_key()).unwrap(),
        at_limit
    );
    let above_limit = "a".repeat(MAX_SIGNED_PAYLOAD - 1);
    assert_eq!(
        sign(&above_limit, &key).unwrap_err(),
        "oversized signed payload"
    );
}
