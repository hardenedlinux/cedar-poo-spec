//! Authorization-code redemption reference over trusted session and code records.
use super::oauth::{CurrentUse, Grant, ReplayGuard};
use base64::{Engine, engine::general_purpose::URL_SAFE_NO_PAD};
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::sync::Mutex;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Session {
    pub issuer: String,
    pub client: String,
    pub redirect: String,
    pub state: String,
    pub browser: String,
    pub s256: String,
}

#[derive(Clone, Debug)]
pub struct Issued {
    pub code: String,
    pub session: Session,
    pub grant: Grant,
    pub expires_at: u64,
}

#[derive(Clone, Debug)]
pub struct Request {
    pub code: String,
    pub response_issuer: String,
    pub client: String,
    pub redirect: String,
    pub state: String,
    pub browser: String,
    pub verifier: String,
}

/// Process-local reference. An authorization server must serialize redemption
/// in the authoritative code store before exposing a token.
pub struct CodeLedger {
    issued: Vec<Issued>,
    spent: Mutex<HashSet<(String, String)>>,
}

pub struct RedeemedGrant(Grant);

impl RedeemedGrant {
    pub fn admit_use(
        &self,
        guard: &ReplayGuard,
        base_allowed: bool,
        actual: &CurrentUse,
    ) -> Result<bool, String> {
        guard.admit(base_allowed && self.0 == actual.grant, actual)
    }
}

impl CodeLedger {
    pub fn new(issued: Vec<Issued>) -> Self {
        Self {
            issued,
            spent: Mutex::default(),
        }
    }

    pub fn redeem(
        &self,
        session: &Session,
        request: &Request,
        now: u64,
    ) -> Result<Option<RedeemedGrant>, String> {
        if session.issuer.is_empty()
            || session.client.is_empty()
            || session.redirect.is_empty()
            || session.state.is_empty()
            || session.browser.is_empty()
            || request.code.is_empty()
            || request.response_issuer != session.issuer
            || request.client != session.client
            || request.redirect != session.redirect
            || request.state != session.state
            || request.browser != session.browser
            || s256(&request.verifier).as_deref() != Some(session.s256.as_str())
        {
            return Ok(None);
        }
        let mut records = self
            .issued
            .iter()
            .filter(|item| item.session.issuer == session.issuer && item.code == request.code);
        let Some(item) = records.next() else {
            return Ok(None);
        };
        if records.next().is_some()
            || item.session != *session
            || now >= item.expires_at
            || item.grant.identity.issuer != session.issuer
            || item.grant.identity.client != session.client
        {
            return Ok(None);
        }
        let mut spent = self.spent.lock().map_err(|_| "OAuth code lock poisoned")?;
        if !spent.insert((session.issuer.clone(), request.code.clone())) {
            return Ok(None);
        }
        Ok(Some(RedeemedGrant(item.grant.clone())))
    }
}

fn s256(verifier: &str) -> Option<String> {
    ((43..=128).contains(&verifier.len())
        && verifier
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'.' | b'_' | b'~')))
    .then(|| URL_SAFE_NO_PAD.encode(Sha256::digest(verifier.as_bytes())))
}

#[cfg(test)]
#[path = "../../tests/unit/gateway_oauth_code.rs"]
mod tests;
