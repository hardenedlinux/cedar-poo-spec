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

#[test]
fn signed_stream_identity_matches_canonical_reference_for_all_byte_classes() {
    // Include base64 triplet tails, hash buffer boundaries, every byte value,
    // empty fields, and the public payload limit. Neither path validates trust.
    for length in [0, 1, 2, 3, 63, 64, 65, 1023, 1024, 1025, MAX_SIGNED_PAYLOAD] {
        for signature_length in [0, 1, 2, 64, 65] {
            let signed = super::Signed {
                payload: (0..length).map(|index| index as u8).collect(),
                signature: (0..signature_length)
                    .map(|index| (255 - index) as u8)
                    .collect(),
            };
            assert_eq!(
                signed.source_sha256().unwrap(),
                crate::json_sha256(&signed).unwrap(),
                "payload={length}, signature={signature_length}"
            );
        }
    }
    let mut signed = super::Signed {
        payload: vec![1, 2],
        signature: vec![3, 4],
    };
    let original = signed.source_sha256().unwrap();
    signed.payload[0] ^= 1;
    assert_ne!(original, signed.source_sha256().unwrap());
    signed.payload[0] ^= 1;
    signed.signature[0] ^= 1;
    assert_ne!(original, signed.source_sha256().unwrap());
}
