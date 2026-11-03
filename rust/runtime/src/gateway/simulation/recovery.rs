//! Reviewed release reconstruction retains the signed publication prefix.
use super::{RecoveryEvidence, Simulator};
use crate::gateway::{
    ReleaseIdentity, ReviewBinding, Signed, publication_matches, verify_publications,
};
use crate::{Case, json_sha256, value_sha256};
use cedar_poo_core::SchemaSourceJson;

/// Independent release history and effect records for one original operation.
pub struct ReviewedRecovery<'a> {
    pub release: ReleaseIdentity,
    pub publications: &'a [Signed],
    pub effects: RecoveryEvidence<'a>,
}
impl Simulator {
    /// Restore the actual reviewed policy before reconciling original consumption.
    pub fn recover_reviewed(
        case: &Case,
        schema: &SchemaSourceJson,
        input: ReviewedRecovery<'_>,
    ) -> Result<Self, String> {
        let recovered = Self::with_release(case, schema, input.release.clone())?;
        let (review, published) = verify_publications(
            input.publications,
            &recovered.verifying_key(),
            &recovered.review_trust,
        )?
        .ok_or("missing reviewed publication")?;
        let first: crate::gateway::PublicationRecord =
            crate::gateway::verify(&input.publications[0], &recovered.verifying_key())?;
        let initial = recovered.review_trust.verify_review(&first.review)?;
        if initial.before_root != input.release.root
            || initial.source != input.release.source
            || review.after != value_sha256(&case.policies)?
            || review.schema != recovered.initial.effect.action_schema
            || published.world != recovered.initial.review.source
        {
            return Err("recovery sources do not match the installed release".into());
        }
        {
            let mut current = recovered.current.lock().map_err(|_| "poisoned authority")?;
            current.release_root = review.after_root.clone();
            current.review = ReviewBinding {
                before: review.before,
                after: review.after,
                schema: review.schema,
                source: published.world.clone(),
                epoch: published.epoch,
                report: json_sha256(&published.review)?,
            };
            current.publications = input.publications.to_vec();
            publication_matches(
                &current.review,
                &(
                    recovered.review_trust.verify_review(&published.review)?,
                    published,
                ),
            )?;
        }
        recovered.restore_effects(input.effects)?;
        Ok(recovered)
    }
}
