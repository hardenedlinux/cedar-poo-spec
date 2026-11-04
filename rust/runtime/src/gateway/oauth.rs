//! Resource-side checks over trusted Host projections. HTTP, token verification,
//! and authenticated live grant status belong to the deploying Host.
use std::collections::HashSet;
use std::sync::Mutex;

/// Issuer-qualified resource owner and OAuth client identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Identity {
    pub issuer: String,
    pub subject: String,
    pub client: String,
}

/// Sender constraint carried by the verified grant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Confirmation {
    Dpop(String),
    Mtls(String),
}

/// Verified token claims used by the resource authorization model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Grant {
    pub identity: Identity,
    pub audiences: Vec<String>,
    pub scopes: Vec<String>,
    pub token_hash: String,
    pub not_before: u64,
    pub expires_at: u64,
    pub confirmation: Confirmation,
}

/// Identity, audience, and permissions required by the actual resource request.
#[derive(Clone, Debug)]
pub struct Target {
    pub identity: Identity,
    pub audience: String,
    pub required_scopes: Vec<String>,
    pub method: String,
    pub uri: String,
}

/// Effective DPoP claims and verification results supplied by the adapter.
#[derive(Clone, Debug)]
pub struct DpopObservation {
    pub thumbprint: String,
    pub method: String,
    pub uri: String,
    pub token_hash: String,
    pub issued_at: u64,
    pub proof_id: String,
    pub signature_verified: bool,
    pub nonce_satisfied: bool,
}

/// Observed proof or authenticated certificate for the current request.
#[derive(Clone, Debug)]
pub enum SenderObservation {
    Dpop(DpopObservation),
    Mtls(String),
}

/// Constructed by a trusted adapter for the same deciding view as Cedar.
#[derive(Clone, Debug)]
pub struct CurrentUse {
    pub grant: Grant,
    pub target: Target,
    pub sender: SenderObservation,
    pub now: u64,
    pub max_proof_age: u64,
    pub token_authenticated: bool,
    pub active: bool,
}

impl CurrentUse {
    fn grant_bound(&self) -> bool {
        self.token_authenticated
            && self.active
            && self.grant.identity == self.target.identity
            && !self.target.audience.is_empty()
            && self.grant.audiences.contains(&self.target.audience)
            && self
                .target
                .required_scopes
                .iter()
                .all(|scope| self.grant.scopes.contains(scope))
            && !self.grant.token_hash.is_empty()
            && self.grant.not_before <= self.now
            && self.now < self.grant.expires_at
    }

    fn dpop_bound(&self, key: &str, proof: &DpopObservation) -> bool {
        proof.signature_verified
            && proof.nonce_satisfied
            && !proof.proof_id.is_empty()
            && !key.is_empty()
            && proof.thumbprint == key
            && proof.method == self.target.method
            && proof.uri == self.target.uri
            && proof.token_hash == self.grant.token_hash
            && self
                .now
                .checked_sub(proof.issued_at)
                .is_some_and(|age| age <= self.max_proof_age)
    }
}

/// Process-local replay reference. Deployments need an authoritative shared
/// reservation across workers and restarts for the accepted proof window.
#[derive(Default)]
pub struct ReplayGuard {
    reserved: Mutex<HashSet<(String, String, String)>>,
}

impl ReplayGuard {
    /// Run at each actual use with current verified observations and the
    /// existing Gateway decision. An OAuth acceptance is not a send permit.
    pub fn admit(&self, base_allowed: bool, current: &CurrentUse) -> Result<bool, String> {
        if !base_allowed || !current.grant_bound() {
            return Ok(false);
        }
        match (&current.grant.confirmation, &current.sender) {
            (Confirmation::Dpop(key), SenderObservation::Dpop(proof))
                if current.dpop_bound(key, proof) =>
            {
                let mut reserved = self
                    .reserved
                    .lock()
                    .map_err(|_| "OAuth replay lock poisoned")?;
                Ok(reserved.insert((
                    current.grant.identity.issuer.clone(),
                    key.clone(),
                    proof.proof_id.clone(),
                )))
            }
            (Confirmation::Mtls(certificate), SenderObservation::Mtls(observed)) => {
                Ok(!certificate.is_empty() && observed == certificate)
            }
            _ => Ok(false),
        }
    }
}

#[cfg(test)]
#[path = "../../tests/unit/gateway_oauth.rs"]
mod tests;
