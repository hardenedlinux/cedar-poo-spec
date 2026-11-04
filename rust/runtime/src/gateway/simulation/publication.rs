//! Serialized registration, publication and current policy replacement.
use super::{Current, Simulator};
use crate::gateway::wire::sign;
use crate::gateway::{
    AnalysisKind, PublicationDelivery, PublicationRecord, PublicationView, ReleaseIdentity,
    ReviewBinding, ReviewRecord, Signed, Version, verify_publications,
};
use crate::{Case, ReplayReceipt, json_sha256, value_sha256};
use cedar_poo_core::SchemaSourceJson;
use std::sync::Arc;

/// A trusted review submission contains source bytes, not a caller no-gain flag.
pub struct ReviewSubmission<'a> {
    pub review: &'a Signed,
    pub candidate: &'a Case,
    pub approval: Option<&'a Signed>,
}
#[derive(Clone)]
pub(super) struct RegisteredReview {
    pub(super) record: ReviewRecord,
    pub(super) signed: Signed,
    pub(super) approval: Option<Signed>,
    pub(super) candidate: Case,
    pub(super) cedar: ReplayReceipt,
    pub(super) program: crate::ValidatedProgram,
}
/// Private owner/generation capability for one exact registered review.
pub struct PublicationTicket {
    owner: Arc<()>,
    generation: u64,
    review: String,
}
impl Simulator {
    /// Configure the independently captured original root and declaration source.
    pub fn with_release(
        case: &Case,
        schema: &SchemaSourceJson,
        release: ReleaseIdentity,
    ) -> Result<Self, String> {
        let simulator = Self::new(case, Some(schema))?;
        {
            let mut current = simulator.current.lock().map_err(|_| "poisoned authority")?;
            current.release_root = release.root;
            current.model_source = release.source;
        }
        Ok(simulator)
    }
    /// Reuse an explicitly owned immutable SDK program, evaluating this operation
    /// afresh before binding its independently captured original release identity.
    pub fn with_prepared_release(
        case: &Case,
        program: &crate::ValidatedProgram,
        release: ReleaseIdentity,
    ) -> Result<Self, String> {
        let simulator = Self::with_program(case, program)?;
        {
            let mut current = simulator.current.lock().map_err(|_| "poisoned authority")?;
            current.release_root = release.root;
            current.model_source = release.source;
        }
        Ok(simulator)
    }
    /// Register authenticated assessment and prepare the candidate with the SDK.
    pub fn register_review(
        &self,
        input: ReviewSubmission<'_>,
    ) -> Result<PublicationTicket, String> {
        let (snapshot, registered) = self.prepare_review(input)?;
        self.register_checked(snapshot, registered)
    }
    fn prepare_review(
        &self,
        input: ReviewSubmission<'_>,
    ) -> Result<(u64, RegisteredReview), String> {
        let record = self.review_trust.verify_review(input.review)?;
        self.review_trust
            .verify_approval(input.review, input.approval)?;
        let snapshot = self
            .current
            .lock()
            .map_err(|_| "poisoned authority")?
            .clone();
        self.check_owner(&snapshot)?;
        check_base(&snapshot, &record, &self.verifying_key())?;
        if input.candidate.name != snapshot.case.name
            || input.candidate.revision != snapshot.case.revision
            || json_sha256(&(&input.candidate.request, &*input.candidate.entities))?
                != snapshot.world
            || value_sha256(&input.candidate.policies)? != record.after
        {
            return Err("candidate is not the reviewed policy at the original operation".into());
        }
        let (program, receipt) = snapshot
            .program
            .as_ref()
            .ok_or("unqualified schema")?
            .revise(input.candidate)?;
        let cedar = receipt.replay;
        if cedar.request_sha256 != snapshot.effect.payload {
            return Err("publication changed the effect payload".into());
        }
        Ok((
            snapshot.generation,
            RegisteredReview {
                record,
                signed: input.review.clone(),
                approval: input.approval.cloned(),
                candidate: input.candidate.clone(),
                cedar,
                program,
            },
        ))
    }
    fn register_checked(
        &self,
        captured_generation: u64,
        registered: RegisteredReview,
    ) -> Result<PublicationTicket, String> {
        let mut current = self.current.lock().map_err(|_| "poisoned authority")?;
        self.check_owner(&current)?;
        if current.generation != captured_generation {
            return Err("registration preparation became stale".into());
        }
        let generation = current
            .generation
            .checked_add(1)
            .ok_or("generation exhausted")?;
        let review = registered.signed.source_sha256()?;
        current.pending_review = Some(registered);
        current.generation = generation;
        Ok(PublicationTicket {
            owner: Arc::clone(&self.owner),
            generation,
            review,
        })
    }
    /// Publish only the exact current registration; no authority is re-consumed.
    pub fn publish_review(
        &self,
        ticket: PublicationTicket,
        delivery: PublicationDelivery,
    ) -> Result<PublicationView, String> {
        if !Arc::ptr_eq(&ticket.owner, &self.owner) {
            return Err("foreign publication ticket".into());
        }
        let mut current = self.current.lock().map_err(|_| "poisoned authority")?;
        self.check_owner(&current)?;
        if current.generation != ticket.generation || current.publication_unknown {
            return Err("stale or unresolved publication".into());
        }
        let registered = current
            .pending_review
            .as_ref()
            .ok_or("missing current registration")?
            .clone();
        if registered.signed.source_sha256()? != ticket.review {
            return Err("replaced review".into());
        }
        check_base(&current, &registered.record, &self.verifying_key())?;
        self.install_review(&mut current, registered, delivery)
    }
    fn install_review(
        &self,
        current: &mut Current,
        registered: RegisteredReview,
        delivery: PublicationDelivery,
    ) -> Result<PublicationView, String> {
        let generation = current
            .generation
            .checked_add(1)
            .ok_or("generation exhausted")?;
        let epoch = current
            .review
            .epoch
            .checked_add(1)
            .ok_or("release epoch exhausted")?;
        let record = PublicationRecord {
            version: Version { major: 1, minor: 0 },
            review: registered.signed.clone(),
            approval: registered.approval,
            previous: current
                .publications
                .last()
                .map(crate::gateway::Signed::source_sha256)
                .transpose()?,
            epoch,
            world: current.world.clone(),
            policies: registered.candidate.policies.clone(),
        };
        let signed = sign(&record, &self.receipt_key)?;
        current.review = ReviewBinding {
            before: registered.record.before,
            after: registered.record.after,
            schema: registered.record.schema,
            source: current.review.source.clone(),
            epoch,
            report: registered.signed.source_sha256()?,
        };
        current.release_root = registered.record.after_root;
        current.case = registered.candidate;
        current.cedar = registered.cedar;
        current.program = Some(registered.program);
        current.publications.push(signed);
        current.pending_review = None;
        current.publication_unknown = delivery == PublicationDelivery::LostReply;
        current.generation = generation;
        publication_view(current)
    }
    /// Read the actual model state, including unresolved publication delivery.
    pub fn publication_view(&self) -> Result<PublicationView, String> {
        publication_view(&*self.current.lock().map_err(|_| "poisoned authority")?)
    }
    /// Public registrar observations; these are not effect capabilities.
    pub fn publication_history(&self) -> Result<Vec<Signed>, String> {
        Ok(self
            .current
            .lock()
            .map_err(|_| "poisoned authority")?
            .publications
            .clone())
    }
    /// Confirm an independently read exact successor; effect exposure is retained.
    pub fn confirm_publication(&self, observed: &[Signed]) -> Result<(), String> {
        let last = verify_publications(observed, &self.verifying_key(), &self.review_trust)?
            .ok_or("missing publication")?;
        let mut current = self.current.lock().map_err(|_| "poisoned authority")?;
        self.check_owner(&current)?;
        if json_sha256(&observed)? != json_sha256(&current.publications)?
            || last.0.after_root != current.release_root
            || last.1.epoch != current.review.epoch
            || value_sha256(&current.case.policies)? != last.0.after
        {
            return Err("publication observation is stale".into());
        }
        let generation = current
            .generation
            .checked_add(1)
            .ok_or("generation exhausted")?;
        current.publication_unknown = false;
        current.generation = generation;
        Ok(())
    }
}
fn check_base(
    current: &Current,
    record: &ReviewRecord,
    gateway: &p256::ecdsa::VerifyingKey,
) -> Result<(), String> {
    if let Some(signed) = current.publications.last() {
        let publication: PublicationRecord = crate::gateway::verify(signed, gateway)?;
        if publication.world != current.world {
            return Err(
                "changed-world publication requires a separately bound release chain".into(),
            );
        }
    }
    current.authority.accepts(&current.facts)?;
    if !current.enforcing
        || !current.sources_current
        || current.spent
        || !super::state::original_consumed(current)
        || current.revoked
        || !current.mapped
        || !current.registered
        || current.unknown
        || current.publication_unknown
        || record.before_root != current.release_root
        || record.source != current.model_source
        || record.epoch != current.review.epoch
        || record.schema != current.effect.action_schema
        || record.before != value_sha256(&current.case.policies)?
    {
        return Err("review does not match the actual release/source/schema/frontier".into());
    }
    if record.analysis != AnalysisKind::NoGain && record.evidence.is_empty() {
        return Err("missing analysis evidence".into());
    }
    Ok(())
}
fn publication_view(current: &Current) -> Result<PublicationView, String> {
    Ok(PublicationView {
        root: current.release_root.clone(),
        policies: value_sha256(&current.case.policies)?,
        epoch: current.review.epoch,
        unknown: current.publication_unknown,
        publications: current.publications.len(),
    })
}
