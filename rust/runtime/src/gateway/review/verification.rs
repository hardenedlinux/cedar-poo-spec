//! Public review/approval and contiguous publication verification.
use super::{AnalysisKind, GainApproval, PublicationRecord, ReviewAuthority, ReviewRecord};
use crate::gateway::{ReviewBinding, Signed, Version, verify};
use crate::value_sha256;
use p256::ecdsa::VerifyingKey;

/// Public review/approval trust roots, chosen outside the candidate artifact.
#[derive(Clone)]
pub struct ReviewTrust {
    pub review_key: VerifyingKey,
    pub approval_key: VerifyingKey,
}
impl ReviewTrust {
    pub(crate) fn simulation() -> Self {
        static TRUST: std::sync::LazyLock<ReviewTrust> =
            std::sync::LazyLock::new(|| ReviewAuthority::simulation().trust());
        TRUST.clone()
    }
    /// Authenticate the complete assessed source before considering classification.
    pub fn verify_review(&self, signed: &Signed) -> Result<ReviewRecord, String> {
        let record: ReviewRecord = verify(signed, &self.review_key)?;
        if record.version != (Version { major: 1, minor: 0 })
            || record.epoch == u64::MAX
            || (record.before == record.after && record.before_root == record.after_root)
            || record.evidence.is_empty()
        {
            return Err("invalid nonidentity review".into());
        }
        Ok(record)
    }
    /// No-gain is an authenticated analyzer result; expansion needs another issuer.
    pub fn verify_approval(
        &self,
        signed: &Signed,
        approval: Option<&Signed>,
    ) -> Result<(), String> {
        let record = self.verify_review(signed)?;
        if let Some(approval) = approval {
            let approved: GainApproval = verify(approval, &self.approval_key)?;
            if approved.version != record.version
                || approved.epoch != record.epoch
                || approved.review != signed.source_sha256()?
            {
                return Err("approval does not bind this exact review".into());
            }
        } else if record.analysis != AnalysisKind::NoGain {
            return Err("expansion approval missing".into());
        }
        Ok(())
    }
}
/// Verify every published source and successor, retaining the full signed prefix.
pub fn verify_publications(
    records: &[Signed],
    gateway: &VerifyingKey,
    trust: &ReviewTrust,
) -> Result<Option<(ReviewRecord, PublicationRecord)>, String> {
    records
        .iter()
        .try_fold(
            None,
            |prior: Option<(ReviewRecord, PublicationRecord, String)>, signed| {
                let publication: PublicationRecord = verify(signed, gateway)?;
                let review = trust.verify_review(&publication.review)?;
                trust.verify_approval(&publication.review, publication.approval.as_ref())?;
                if publication.version != review.version
                    || publication.epoch
                        != review
                            .epoch
                            .checked_add(1)
                            .ok_or("exhausted review epoch")?
                    || value_sha256(&publication.policies)? != review.after
                {
                    return Err("publication does not install the reviewed successor".into());
                }
                match &prior {
                    None if publication.previous.is_some() || review.epoch != 7 => {
                        return Err("missing initial publication prefix".into());
                    }
                    Some((old, installed, digest))
                        if publication.previous.as_ref() != Some(digest)
                            || review.before != old.after
                            || review.before_root != old.after_root
                            || review.epoch != installed.epoch
                            || review.source != old.source
                            || review.schema != old.schema
                            || publication.world != installed.world =>
                    {
                        return Err("publication prefix changed or rolled back".into());
                    }
                    _ => (),
                }
                Ok(Some((review, publication, signed.source_sha256()?)))
            },
        )
        .map(|last| last.map(|(review, publication, _)| (review, publication)))
}
/// Current-use retains the last published policy; fresh facts bind the use world.
pub fn publication_matches(
    binding: &ReviewBinding,
    last: &(ReviewRecord, PublicationRecord),
) -> Result<(), String> {
    let (review, published) = last;
    if binding.before != review.before
        || binding.after != review.after
        || binding.schema != review.schema
        || binding.source != published.world
        || binding.epoch != published.epoch
        || binding.report != published.review.source_sha256()?
    {
        return Err("effect is not bound to the current publication".into());
    }
    Ok(())
}
