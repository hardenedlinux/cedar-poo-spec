//! Process-local model of a Host-owned, effect-bound approval instance.
//! Durable storage and approval authentication belong to the deploying Host.

/// Stable identity of one approval instance in the Host's authority store.
#[derive(Clone, Debug, Eq, Hash, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct AuthorityId(pub String);

impl From<&str> for AuthorityId {
    fn from(value: &str) -> Self {
        Self(value.into())
    }
}

/// One exact-effect approval with a Host-owned use limit and consumed count.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct AuthorityGrant<Effect> {
    pub id: AuthorityId,
    pub effect: Effect,
    pub max_uses: u64,
    pub used: u64,
}

/// Process-local collection of approval instances.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct AuthorityLedger<Effect> {
    pub grants: Vec<AuthorityGrant<Effect>>,
}

/// Reason an approval instance cannot authorize the proposed effect.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AuthorityError {
    Missing,
    Duplicate,
    EffectMismatch,
    Exhausted,
}

impl<Effect: PartialEq> AuthorityLedger<Effect> {
    /// The use limit comes from Host state, never from a prepared ticket.
    pub fn check(&self, id: &AuthorityId, effect: &Effect) -> Result<(), AuthorityError> {
        let mut matches = self.grants.iter().filter(|grant| &grant.id == id);
        let grant = matches.next().ok_or(AuthorityError::Missing)?;
        if matches.next().is_some() {
            return Err(AuthorityError::Duplicate);
        }
        if &grant.effect != effect {
            return Err(AuthorityError::EffectMismatch);
        }
        if grant.used >= grant.max_uses {
            return Err(AuthorityError::Exhausted);
        }
        Ok(())
    }

    /// Call under the same serialized transaction as budget and audit writes.
    pub fn consume(&mut self, id: &AuthorityId, effect: &Effect) -> Result<(), AuthorityError> {
        self.check(id, effect)?;
        let grant = self
            .grants
            .iter_mut()
            .find(|grant| &grant.id == id)
            .ok_or(AuthorityError::Missing)?;
        grant.used += 1;
        Ok(())
    }

    pub fn used(&self, id: &AuthorityId) -> Result<u64, AuthorityError> {
        let mut matches = self.grants.iter().filter(|grant| &grant.id == id);
        let grant = matches.next().ok_or(AuthorityError::Missing)?;
        if matches.next().is_some() {
            return Err(AuthorityError::Duplicate);
        }
        Ok(grant.used)
    }
}

#[cfg(test)]
#[path = "../tests/unit/authority_consumption.rs"]
mod tests;
