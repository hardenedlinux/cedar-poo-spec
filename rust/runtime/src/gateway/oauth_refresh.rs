//! Nonrotating, sender-constrained refresh families for the confidential-client profile.
use super::oauth::{CurrentUse, Grant, ReplayGuard};
use super::oauth_par::{ParRedeemed, Registration, TokenSender, VerifiedClient};
use std::collections::HashMap;
use std::sync::Mutex;

/// Trusted digest of an opaque refresh token presented to the issuer.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RefreshDigest(pub String);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct FamilyKey {
    issuer: String,
    refresh: RefreshDigest,
}

struct Family {
    registration: Registration,
    original: Grant,
    expires_at: u64,
    revoked: bool,
}

impl Family {
    fn permits(&self, next: &Grant) -> bool {
        next.identity == self.original.identity
            && next.confirmation == self.original.confirmation
            && next
                .audiences
                .iter()
                .all(|audience| self.original.audiences.contains(audience))
            && next
                .scopes
                .iter()
                .all(|scope| self.original.scopes.contains(scope))
    }
}

struct Access {
    family: FamilyKey,
    grant: Grant,
}

#[derive(Default)]
struct State {
    families: HashMap<FamilyKey, Family>,
    access: HashMap<String, Access>,
}

impl State {
    fn unissued(&self, digest: &str) -> bool {
        !digest.is_empty() && !self.access.contains_key(digest)
    }
}

/// Refresh metadata attached to a successful PAR redemption.
pub struct RefreshEnrollment {
    pub redeemed: ParRedeemed,
    pub digest: RefreshDigest,
    pub now: u64,
    pub expires_at: u64,
}

/// Authenticated refresh payload with proof verified on this token request.
pub struct RefreshRequest {
    pub digest: RefreshDigest,
    pub sender: TokenSender,
}

/// A proposed access grant to commit with the original refresh family.
pub struct RefreshExchange {
    pub verified: VerifiedClient<RefreshRequest>,
    pub next: Grant,
    pub now: u64,
}

/// Process-local reference. Enrollment, refresh, revocation, and resource
/// admission serialize on one ledger shared by all routes.
#[derive(Default)]
pub struct RefreshLedger(Mutex<State>);

impl RefreshLedger {
    /// Register the initial access grant and its refresh family together.
    /// Consumes the access-only redemption capability.
    pub fn enroll(&self, input: RefreshEnrollment) -> Result<bool, String> {
        let grant = input.redeemed.redeemed.grant();
        if input.digest.0.is_empty() || input.now >= input.expires_at {
            return Ok(false);
        }
        let mut state = self.0.lock().map_err(|_| "OAuth refresh lock poisoned")?;
        let key = FamilyKey {
            issuer: grant.identity.issuer.clone(),
            refresh: input.digest,
        };
        if !state.unissued(&grant.token_hash) || state.families.contains_key(&key) {
            return Ok(false);
        }
        state.families.insert(
            key.clone(),
            Family {
                registration: input.redeemed.registration,
                original: grant.clone(),
                expires_at: input.expires_at,
                revoked: false,
            },
        );
        state.access.insert(
            grant.token_hash.clone(),
            Access {
                family: key,
                grant: grant.clone(),
            },
        );
        Ok(true)
    }

    /// Issue a fresh access grant while keeping the original refresh handle.
    pub fn refresh(&self, input: RefreshExchange) -> Result<Option<Grant>, String> {
        let RefreshExchange {
            verified,
            next,
            now,
        } = input;
        let mut state = self.0.lock().map_err(|_| "OAuth refresh lock poisoned")?;
        let key = FamilyKey {
            issuer: verified.issuer.clone(),
            refresh: verified.request.digest.clone(),
        };
        let Some(family) = state.families.get(&key) else {
            return Ok(None);
        };
        if family.revoked
            || now >= family.expires_at
            || !verified.matches(&family.registration)
            || !verified
                .request
                .sender
                .matches(&verified.credential, &family.original.confirmation)
            || !family.permits(&next)
            || !state.unissued(&next.token_hash)
            || now < next.not_before
            || now >= next.expires_at
        {
            return Ok(None);
        }
        state.access.insert(
            next.token_hash.clone(),
            Access {
                family: key,
                grant: next.clone(),
            },
        );
        Ok(Some(next))
    }

    /// Revoke the authenticated client's family even if its sender key is lost.
    pub fn revoke(&self, verified: VerifiedClient<RefreshDigest>) -> Result<bool, String> {
        let mut state = self.0.lock().map_err(|_| "OAuth refresh lock poisoned")?;
        let key = FamilyKey {
            issuer: verified.issuer.clone(),
            refresh: verified.request.clone(),
        };
        let Some(family) = state.families.get_mut(&key) else {
            return Ok(false);
        };
        if !verified.matches(&family.registration) {
            return Ok(false);
        }
        family.revoked = true;
        Ok(true)
    }

    /// Resolve the actual grant to its family and check current resource authority.
    pub fn admit_use(
        &self,
        guard: &ReplayGuard,
        base_allowed: bool,
        current: &CurrentUse,
    ) -> Result<bool, String> {
        let state = self.0.lock().map_err(|_| "OAuth refresh lock poisoned")?;
        let Some(access) = state.access.get(&current.grant.token_hash) else {
            return Ok(false);
        };
        if access.grant != current.grant
            || state
                .families
                .get(&access.family)
                .is_none_or(|family| family.revoked)
        {
            return Ok(false);
        }
        guard.admit(base_allowed, current)
    }
}

#[cfg(test)]
#[path = "../../tests/unit/gateway_oauth_refresh.rs"]
mod tests;
