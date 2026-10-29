//! Value-level handoff admission. The caller authenticates grants and actor identities.
/// A nonempty credential-mode label. Provider/LOB capability checks remain separate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CredentialMode(String);
impl TryFrom<String> for CredentialMode {
    type Error = &'static str;
    fn try_from(value: String) -> Result<Self, Self::Error> {
        if value.is_empty() {
            Err("empty credential mode")
        } else {
            Ok(Self(value))
        }
    }
}
impl CredentialMode {
    /// Borrow the exact mode label for owner-specific capability lookup.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Exact case, digest, actor and policy-root binding supplied by the Host.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scope<Actor> {
    pub case_id: String,
    pub claim_digest: String,
    pub source_actor: Actor,
    pub target_actor: Actor,
    pub source_root: String,
    pub target_root: String,
    pub credential_mode: CredentialMode,
}
impl<Actor: Eq> Scope<Actor> {
    /// Require complete scope labels and distinct typed actors.
    pub fn well_formed(&self) -> bool {
        !self.case_id.is_empty()
            && !self.claim_digest.is_empty()
            && !self.source_root.is_empty()
            && !self.target_root.is_empty()
            && self.source_actor != self.target_actor
    }
}
/// An already authenticated, epoch-bound grant with an exclusive expiry.
#[derive(Clone, Debug)]
pub struct Grant<Actor> {
    pub scope: Scope<Actor>,
    pub epoch: u64,
    pub expires_at: u64,
}
impl<Actor: Eq> Grant<Actor> {
    /// Compare the current selection and time; this does not authenticate a grant.
    pub fn admits(&self, expected: &Scope<Actor>, epoch: u64, now: u64) -> bool {
        expected.well_formed()
            && self.scope == *expected
            && self.epoch == epoch
            && now < self.expires_at
    }
}
#[cfg(test)]
#[path = "../tests/unit/handoff.rs"]
mod tests;
