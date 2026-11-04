//! Process-local admission identity for one authenticated workflow operation.
//! An external effect needs a separate dispatch/result protocol.

use std::collections::HashMap;

/// Stable identity of one workflow operation across approval renewal and retry.
#[derive(Clone, Debug, Eq, Hash, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct OperationId(pub String);

impl From<&str> for OperationId {
    fn from(value: &str) -> Self {
        Self(value.into())
    }
}

/// Admission identity, not a record of delivery to a remote target.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct OperationLedger<Effect> {
    admitted: HashMap<OperationId, Effect>,
}

impl<Effect> Default for OperationLedger<Effect> {
    fn default() -> Self {
        Self {
            admitted: HashMap::new(),
        }
    }
}

/// Reason one operation ID cannot be admitted with the proposed effect.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OperationError {
    EmptyId,
    AlreadyAdmitted,
    EffectMismatch,
}

impl<Effect: Clone + PartialEq> OperationLedger<Effect> {
    pub fn check(&self, id: &OperationId, effect: &Effect) -> Result<(), OperationError> {
        if id.0.is_empty() {
            return Err(OperationError::EmptyId);
        }
        match self.admitted.get(id) {
            None => Ok(()),
            Some(existing) if existing == effect => Err(OperationError::AlreadyAdmitted),
            Some(_) => Err(OperationError::EffectMismatch),
        }
    }

    pub fn admit(&mut self, id: &OperationId, effect: &Effect) -> Result<(), OperationError> {
        self.check(id, effect)?;
        self.admitted.insert(id.clone(), effect.clone());
        Ok(())
    }

    pub fn admitted(&self, id: &OperationId) -> Option<&Effect> {
        self.admitted.get(id)
    }
}

#[cfg(test)]
#[path = "../tests/unit/operation_identity.rs"]
mod tests;
