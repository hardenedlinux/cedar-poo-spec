//! Nonrotating, sender-constrained refresh families for the confidential-client profile.
use super::oauth::{CurrentUse, Grant, ReplayGuard};
use super::oauth_par::{ParRedeemed, Registration, TokenSender, VerifiedClient};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// Trusted digest of an opaque refresh token presented to the issuer.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RefreshDigest(pub String);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct FamilyKey {
    issuer: String,
    refresh: RefreshDigest,
}

#[derive(Clone, PartialEq, Eq)]
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

#[derive(Clone, PartialEq, Eq)]
struct Access {
    family: FamilyKey,
    grant: Grant,
}

#[derive(Clone, Default, PartialEq, Eq)]
struct State {
    position: u64,
    families: HashMap<FamilyKey, Family>,
    access: HashMap<String, Access>,
}

impl State {
    fn advance(image: &mut Arc<Self>) -> Result<&mut Self, String> {
        let next = image
            .position
            .checked_add(1)
            .ok_or("OAuth refresh position exhausted")?;
        let state = Arc::make_mut(image);
        state.position = next;
        Ok(state)
    }

    fn contains_active(&self, current: &CurrentUse) -> bool {
        self.access
            .get(&current.grant.token_hash)
            .is_some_and(|access| {
                access.grant == current.grant
                    && self
                        .families
                        .get(&access.family)
                        .is_some_and(|family| !family.revoked)
            })
    }

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

/// Immutable replica image with a source identity and committed position.
/// The process-local reference uses exact state equality as its content binding.
#[derive(Clone)]
pub struct RevocationCheckpoint {
    authority: Arc<()>,
    image: Arc<State>,
}

impl RevocationCheckpoint {
    fn matches(&self, authority: &Arc<()>, current: &Arc<State>) -> bool {
        Arc::ptr_eq(&self.authority, authority)
            && self.image.position == current.position
            && (Arc::ptr_eq(&self.image, current) || self.image == *current)
    }
}

/// Actual inputs for the final effect boundary, including the original check.
pub struct FinalRefreshUse<'a> {
    pub checked: &'a RevocationCheckpoint,
    pub replica: &'a RevocationCheckpoint,
    pub current: &'a CurrentUse,
    pub guard: &'a ReplayGuard,
    pub base_allowed: bool,
}

/// Process-local reference. Enrollment, refresh, revocation, and resource
/// admission serialize on one ledger shared by all routes.
#[derive(Default)]
pub struct RefreshLedger {
    authority: Arc<()>,
    image: Mutex<Arc<State>>,
}

impl RefreshLedger {
    /// Register the initial access grant and its refresh family together.
    /// Consumes the access-only redemption capability.
    pub fn enroll(&self, input: RefreshEnrollment) -> Result<bool, String> {
        let grant = input.redeemed.redeemed.grant();
        if input.digest.0.is_empty() || input.now >= input.expires_at {
            return Ok(false);
        }
        let mut image = self
            .image
            .lock()
            .map_err(|_| "OAuth refresh lock poisoned")?;
        let key = FamilyKey {
            issuer: grant.identity.issuer.clone(),
            refresh: input.digest,
        };
        if !image.unissued(&grant.token_hash) || image.families.contains_key(&key) {
            return Ok(false);
        }
        let state = State::advance(&mut image)?;
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
        let mut image = self
            .image
            .lock()
            .map_err(|_| "OAuth refresh lock poisoned")?;
        let key = FamilyKey {
            issuer: verified.issuer.clone(),
            refresh: verified.request.digest.clone(),
        };
        let Some(family) = image.families.get(&key) else {
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
            || !image.unissued(&next.token_hash)
            || now < next.not_before
            || now >= next.expires_at
        {
            return Ok(None);
        }
        State::advance(&mut image)?.access.insert(
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
        let mut image = self
            .image
            .lock()
            .map_err(|_| "OAuth refresh lock poisoned")?;
        let key = FamilyKey {
            issuer: verified.issuer.clone(),
            refresh: verified.request.clone(),
        };
        let Some(family) = image.families.get(&key) else {
            return Ok(false);
        };
        if !verified.matches(&family.registration) {
            return Ok(false);
        }
        if !family.revoked {
            let family = State::advance(&mut image)?
                .families
                .get_mut(&key)
                .ok_or("OAuth refresh family disappeared")?;
            family.revoked = true;
        }
        Ok(true)
    }

    /// Resolve the actual grant to its family and check current resource authority.
    pub fn admit_use(
        &self,
        guard: &ReplayGuard,
        base_allowed: bool,
        current: &CurrentUse,
    ) -> Result<bool, String> {
        let image = self
            .image
            .lock()
            .map_err(|_| "OAuth refresh lock poisoned")?;
        guard.admit(base_allowed && image.contains_active(current), current)
    }

    /// Capture an immutable image of the authoritative position and contents.
    pub fn checkpoint(&self) -> Result<RevocationCheckpoint, String> {
        let image = self
            .image
            .lock()
            .map_err(|_| "OAuth refresh lock poisoned")?;
        Ok(RevocationCheckpoint {
            authority: self.authority.clone(),
            image: image.clone(),
        })
    }

    /// Check against the independent live ledger and reserve the proof before
    /// invoking the synchronous effect observer, while revocation is excluded.
    /// The observer must not re-enter the ledger.
    pub fn execute_final(
        &self,
        input: FinalRefreshUse<'_>,
        observe_effect: impl FnOnce(),
    ) -> Result<bool, String> {
        let image = self
            .image
            .lock()
            .map_err(|_| "OAuth refresh lock poisoned")?;
        if !input.replica.matches(&self.authority, &image)
            || !input.checked.matches(&self.authority, &image)
            || !image.contains_active(input.current)
            || !input.guard.admit(input.base_allowed, input.current)?
        {
            return Ok(false);
        }
        observe_effect();
        Ok(true)
    }
}

#[cfg(test)]
#[path = "../../tests/unit/gateway_oauth_refresh.rs"]
mod tests;
