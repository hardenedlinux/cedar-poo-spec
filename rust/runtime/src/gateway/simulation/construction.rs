//! SDK-qualified source binding and exact original consumption construction.
use super::{Current, Simulator, field_inventory};
use crate::gateway::wire::{sign, simulation_key};
use crate::gateway::{
    EffectIdentity, Envelope, FactAuthority, FactBinding, Origin, ReviewBinding, Version,
};
use crate::{
    Case, Manifest, ReplayReceipt, ValidatedManifest, replay_manifest, replay_validated_manifest,
};
use crate::{json_sha256, value_sha256};
use cedar_poo_core::SchemaSourceJson;
use cedar_poo_core::authority_consumption::{AuthorityGrant, AuthorityId, AuthorityLedger};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
impl Simulator {
    pub fn new(case: &Case, schema: Option<&SchemaSourceJson>) -> Result<Self, String> {
        let cedar = if let Some(schema) = schema {
            replay_validated_manifest(&ValidatedManifest {
                schema: schema.clone(),
                cases: vec![case.clone()],
            })?
            .remove(0)
            .replay
        } else {
            replay_manifest(&Manifest {
                cases: vec![case.clone()],
            })?
            .remove(0)
        };
        Self::bind_simulated_sources(case, schema, cedar)
    }
    fn bind_simulated_sources(
        case: &Case,
        schema: Option<&SchemaSourceJson>,
        cedar: ReplayReceipt,
    ) -> Result<Self, String> {
        let source_keys: BTreeMap<_, _> = [
            ("binding-authority".to_owned(), simulation_key(1)),
            ("context-authority".to_owned(), simulation_key(4)),
            ("entity-authority".to_owned(), simulation_key(5)),
        ]
        .into();
        let schema_id = schema
            .map(crate::schema_sha256)
            .transpose()?
            .unwrap_or_else(|| "unvalidated".into());
        let policy_id = value_sha256(&case.policies)?;
        // Identity revisions have a reflexive no-gain proof. Nonidentity review
        // reports must come from the existing independent Delta review service.
        let review = ReviewBinding {
            before: policy_id.clone(),
            after: policy_id,
            schema: schema_id.clone(),
            source: json_sha256(&(&case.request, &*case.entities))?,
            epoch: 7,
            report: String::new(),
        };
        let review = ReviewBinding {
            report: json_sha256(&review)?,
            ..review
        };
        let effect = EffectIdentity {
            operation: json_sha256(&("cedar-poo-operation-v1", &case.revision, &case.name))?,
            object: case.request.resource.clone(),
            generation: 7,
            payload: cedar.request_sha256.clone(),
            action_schema: schema_id,
            audience: "gateway".into(),
        };
        let facts: Vec<_> = field_inventory(case)?
            .into_iter()
            .map(|(field, value)| FactBinding {
                issuer: if field.starts_with("context/") {
                    "context-authority"
                } else if field.starts_with("entity/") {
                    "entity-authority"
                } else {
                    "binding-authority"
                }
                .into(),
                subject: case.request.principal.clone(),
                audience: "gateway".into(),
                source: "current-world".into(),
                field,
                value,
                generation: 7,
                origin: Origin::Attested,
                not_before: 1,
                expires_at: 100,
            })
            .collect();
        let signed = facts
            .iter()
            .map(|fact| sign(fact, &source_keys[&fact.issuer]))
            .collect::<Result<Vec<_>, _>>()?;
        let initial = Envelope {
            version: Version { major: 1, minor: 0 },
            effect: effect.clone(),
            review: review.clone(),
            facts: signed,
        };
        let authority = FactAuthority::new(
            facts,
            source_keys
                .iter()
                .map(|(issuer, key)| (issuer.clone(), *key.verifying_key()))
                .collect(),
            10,
        )?
        .prepare_sources(&initial.facts)?;
        // The trusted simulated Host consumes an exact-effect original using
        // the same native owner as other effect-bound approval instances.
        let mut original = AuthorityLedger {
            grants: vec![AuthorityGrant {
                id: AuthorityId(effect.operation.clone()),
                effect: effect.clone(),
                max_uses: 1,
                used: 0,
            }],
        };
        original
            .consume(&AuthorityId(effect.operation.clone()), &effect)
            .map_err(|e| format!("original consumption: {e:?}"))?;
        Ok(Self {
            owner: Arc::new(()),
            current: Mutex::new(Current {
                generation: 0,
                effect,
                review,
                authority,
                enforcing: schema.is_some(),
                mapped: true,
                revoked: false,
                registered: true,
                original,
                unknown: false,
                spent: false,
            }),
            source_keys: Arc::new(source_keys),
            receipt_key: simulation_key(3),
            cedar,
            initial,
        })
    }
}
