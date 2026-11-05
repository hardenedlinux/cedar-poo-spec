//! Immutable public publication verification, bound to complete bytes and keys.
use super::{PublicationRecord, ReviewRecord, ReviewTrust, verify_publications};
use crate::gateway::Signed;
use p256::ecdsa::VerifyingKey;
use std::sync::Arc;

/// Verified public material only. It grants no current-use or execution authority.
#[derive(Clone)]
pub struct PreparedPublications {
    gateway: VerifyingKey,
    trust: ReviewTrust,
    records: Arc<[Signed]>,
    last: Option<(ReviewRecord, PublicationRecord)>,
}
impl PreparedPublications {
    /// Verify the full immutable prefix using independently selected public roots.
    pub fn new(
        records: &[Signed],
        gateway: &VerifyingKey,
        trust: &ReviewTrust,
    ) -> Result<Self, String> {
        let last = verify_publications(records, gateway, trust)?;
        Ok(Self {
            gateway: *gateway,
            trust: trust.clone(),
            records: records.into(),
            last,
        })
    }
    /// Reuse only exact original bytes under identical roots; changes take full
    /// verification again. Current facts, review binding and witness still check.
    pub fn verify(
        &self,
        records: &[Signed],
        gateway: &VerifyingKey,
        trust: &ReviewTrust,
    ) -> Result<Option<(ReviewRecord, PublicationRecord)>, String> {
        if self.gateway == *gateway
            && self.trust.review_key == trust.review_key
            && self.trust.approval_key == trust.approval_key
            && records.len() == self.records.len()
            && records
                .iter()
                .zip(self.records.iter())
                .all(|(a, b)| a.payload == b.payload && a.signature == b.signature)
        {
            Ok(self.last.clone())
        } else {
            verify_publications(records, gateway, trust)
        }
    }
}
