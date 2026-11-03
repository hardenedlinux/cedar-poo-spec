//! Independent simulated review and gain-approval issuers.
use super::{GainApproval, ReviewRecord, ReviewTrust};
use crate::gateway::wire::{sign, simulation_key};
use crate::gateway::{Signed, Version, verify};
use crate::json_sha256;
use p256::ecdsa::SigningKey;

/// Trusted simulation issuers; neither key is selected by an incoming envelope.
pub struct ReviewAuthority {
    review: SigningKey,
    approval: SigningKey,
}
impl ReviewAuthority {
    /// Public test keys for an explicit simulated authority, not deployed custody.
    pub fn simulation() -> Self {
        Self {
            review: simulation_key(6),
            approval: simulation_key(7),
        }
    }
    /// Public verification material, configured independently in the recipient.
    pub fn trust(&self) -> ReviewTrust {
        ReviewTrust {
            review_key: *self.review.verifying_key(),
            approval_key: *self.approval.verifying_key(),
        }
    }
    /// Certify trusted analyzer output; transports must never call this on client claims.
    pub fn certify(&self, record: &ReviewRecord) -> Result<Signed, String> {
        sign(record, &self.review)
    }
    /// Approve one exact authenticated review rather than an unbound Boolean.
    pub fn approve(&self, review: &Signed) -> Result<Signed, String> {
        let record: ReviewRecord = verify(review, self.review.verifying_key())?;
        sign(
            &GainApproval {
                version: Version { major: 1, minor: 0 },
                review: json_sha256(review)?,
                epoch: record.epoch,
            },
            &self.approval,
        )
    }
}
