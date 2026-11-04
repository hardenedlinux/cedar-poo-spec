//! SDK-qualified source binding and exact original consumption construction.
use super::lifecycle::{SourceWindow, prepare_facts};
use super::{Current, Simulator};
use crate::gateway::wire::simulation_key;
use crate::gateway::{EffectIdentity, Envelope, ReviewBinding, Version};
use crate::{Case, Manifest, ReplayReceipt, ValidatedProgram, replay_manifest};
use crate::{json_sha256, value_sha256};
use cedar_poo_core::SchemaSourceJson;
use cedar_poo_core::authority_consumption::{AuthorityGrant, AuthorityId, AuthorityLedger};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
impl Simulator {
    pub fn new(case: &Case, schema: Option<&SchemaSourceJson>) -> Result<Self, String> {
        let (program, cedar) = if let Some(schema) = schema {
            let (program, receipt) = ValidatedProgram::prepare(schema, case)?;
            (Some(program), receipt.replay)
        } else {
            (
                None,
                replay_manifest(&Manifest {
                    cases: vec![case.clone()],
                })?
                .remove(0),
            )
        };
        Self::bind_simulated_sources(case, program, cedar)
    }

    pub(super) fn with_program(case: &Case, program: &ValidatedProgram) -> Result<Self, String> {
        let receipt = program.replay(case)?;
        Self::bind_simulated_sources(case, Some(program.clone()), receipt.replay)
    }
    fn bind_simulated_sources(
        case: &Case,
        program: Option<ValidatedProgram>,
        cedar: ReplayReceipt,
    ) -> Result<Self, String> {
        static SOURCES: std::sync::LazyLock<Arc<BTreeMap<String, p256::ecdsa::SigningKey>>> =
            std::sync::LazyLock::new(|| {
                Arc::new(
                    [
                        ("binding-authority".to_owned(), simulation_key(1)),
                        ("context-authority".to_owned(), simulation_key(4)),
                        ("entity-authority".to_owned(), simulation_key(5)),
                    ]
                    .into(),
                )
            });
        let source_keys = SOURCES.clone();
        let enforcing = program.is_some();
        let schema_id = program
            .as_ref()
            .map(|p| p.schema_sha256().map(str::to_owned))
            .transpose()?
            .unwrap_or_else(|| "unvalidated".into());
        let sources = prepare_facts(
            case,
            &source_keys,
            SourceWindow {
                generation: 7,
                now: 10,
                expires_at: 100,
            },
        )?;
        let policy_id = value_sha256(&case.policies)?;
        // Identity revisions have a reflexive no-gain proof. Nonidentity review
        // reports must come from the existing independent Delta review service.
        let review = ReviewBinding {
            before: policy_id.clone(),
            after: policy_id,
            schema: schema_id.clone(),
            source: sources.world.clone(),
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
        let initial = Envelope {
            current_world: sources.world.clone(),
            version: Version { major: 1, minor: 0 },
            effect: effect.clone(),
            review: review.clone(),
            facts: sources.facts.clone(),
        };
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
        let owner = Arc::new(());
        Ok(Self {
            owner: Arc::clone(&owner),
            current: Arc::new(Mutex::new(Current {
                generation: 0,
                active_owner: owner,
                fact_generation: 7,
                sources_current: true,
                facts: sources.facts,
                world: sources.world,
                case: case.clone(),
                cedar,
                program,
                release_root: case.revision.clone(),
                model_source: review.after.clone(),
                pending_review: None,
                publications: vec![],
                publication_unknown: false,
                effect,
                review,
                authority: sources.authority,
                enforcing,
                mapped: true,
                revoked: false,
                registered: true,
                original,
                unknown: false,
                spent: false,
                retained_intent: None,
            })),
            source_keys,
            receipt_key: simulation_key(3),
            provider_key: *simulation_key(8).verifying_key(),
            review_trust: crate::gateway::ReviewTrust::simulation(),
            initial,
        })
    }
}
