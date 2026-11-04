use super::{receipt, validated};
use crate::gateway::{Signed, Simulator};
use p256::ecdsa::{Signature, SigningKey, signature::Signer};

pub(super) fn setup() -> (crate::Case, cedar_poo_core::SchemaSourceJson, Simulator) {
    let case = receipt();
    let schema = validated(case.clone()).schema;
    let simulator = Simulator::new(&case, Some(&schema)).unwrap();
    (case, schema, simulator)
}
pub(super) fn signed(value: &impl serde::Serialize, key: &SigningKey) -> Signed {
    let payload = serde_json::to_vec(value).unwrap();
    let signature: Signature = key.sign(&payload);
    Signed {
        payload,
        signature: signature.to_bytes().to_vec(),
    }
}
