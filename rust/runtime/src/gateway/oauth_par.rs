//! Pushed authorization reference for confidential clients.
use super::oauth::Grant;
use super::oauth_code::{self, CodeLedger, Issued, RedeemedGrant, Session};
use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

/// Registered client authentication method and verified credential identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Credential {
    Mtls(String),
    PrivateKeyJwt(String),
}

impl Credential {
    fn thumbprint(&self) -> &str {
        match self {
            Self::Mtls(value) | Self::PrivateKeyJwt(value) => value,
        }
    }
}

/// Trusted issuer-side OAuth client registration.
#[derive(Clone, Debug)]
pub struct Registration {
    pub issuer: String,
    pub client: String,
    pub credential: Credential,
    pub redirects: Vec<String>,
    pub scopes: Vec<String>,
}

/// Trusted adapter input. Construct only after authenticating this request
/// at the selected issuer's endpoint with the observed credential.
pub struct VerifiedClient<T> {
    pub issuer: String,
    pub client: String,
    pub credential: Credential,
    pub request: T,
}

impl<T> VerifiedClient<T> {
    fn matches(&self, registration: &Registration) -> bool {
        self.issuer == registration.issuer
            && self.client == registration.client
            && self.credential == registration.credential
            && !registration.credential.thumbprint().is_empty()
    }
}

/// Authorization parameters received in the authenticated back channel.
pub struct ParRequest {
    pub session: Session,
    pub audiences: Vec<String>,
    pub scopes: Vec<String>,
}

impl ParRequest {
    fn permits(&self, grant: &Grant) -> bool {
        grant.identity.issuer == self.session.issuer
            && grant.identity.client == self.session.client
            && grant
                .audiences
                .iter()
                .all(|audience| self.audiences.contains(audience))
            && grant.scopes.iter().all(|scope| self.scopes.contains(scope))
    }
}

struct Pushed {
    request: ParRequest,
    registration: Registration,
    expires_at: u64,
}

#[derive(Default)]
struct State {
    // A consumed handle remains reserved and cannot be reassigned.
    pushed: HashMap<(String, String), Option<Pushed>>,
    issued: HashSet<(String, String)>,
}

/// Process-local reference. All callers of an issuer share this instance.
#[derive(Default)]
pub struct ParLedger(Mutex<State>);

/// Opaque issuer-scoped request URI returned by the PAR endpoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParUri<'a>(pub &'a str);

/// Authenticated PAR submission and the server-issued reference and expiry.
pub struct Push<'a> {
    pub registration: &'a Registration,
    pub verified: VerifiedClient<ParRequest>,
    pub uri: ParUri<'a>,
    pub now: u64,
    pub expires_at: u64,
}

/// Trusted consent decision and effective front-channel authorization request.
pub struct Authorization<'a> {
    /// Trusted pending state selected independently of the front channel.
    pub expected_uri: ParUri<'a>,
    pub session: &'a Session,
    pub uri: ParUri<'a>,
    pub client: &'a str,
    pub has_extra_parameters: bool,
    pub now: u64,
    /// Code and consented grant supplied by the authorization server.
    pub code: String,
    pub code_expires_at: u64,
    pub grant: Grant,
}

/// Opaque result of successful PAR authorization. Owns the one code ledger
/// for this issued code. Sharing the result shares its redemption state.
pub struct Authorized {
    registration: Registration,
    session: Session,
    codes: CodeLedger,
}

impl ParLedger {
    pub fn push(&self, input: Push<'_>) -> Result<bool, String> {
        let Push {
            registration,
            verified,
            uri,
            now,
            expires_at,
        } = input;
        let session = &verified.request.session;
        if !verified.matches(registration)
            || session.issuer.is_empty()
            || session.client.is_empty()
            || session.redirect.is_empty()
            || session.state.0.is_empty()
            || session.browser.is_empty()
            || session.s256.is_empty()
            || session.issuer != registration.issuer
            || session.client != registration.client
            || !registration.redirects.contains(&session.redirect)
            || !verified
                .request
                .scopes
                .iter()
                .all(|scope| registration.scopes.contains(scope))
            || uri.0.is_empty()
            || expires_at <= now
            || expires_at - now >= 600
        {
            return Ok(false);
        }
        let mut state = self.0.lock().map_err(|_| "OAuth PAR lock poisoned")?;
        let key = (session.issuer.clone(), uri.0.to_owned());
        let std::collections::hash_map::Entry::Vacant(slot) = state.pushed.entry(key) else {
            return Ok(false);
        };
        slot.insert(Some(Pushed {
            request: verified.request,
            registration: registration.clone(),
            expires_at,
        }));
        Ok(true)
    }

    pub fn authorize(&self, input: Authorization<'_>) -> Result<Option<Authorized>, String> {
        if input.uri != input.expected_uri
            || input.client != input.session.client
            || input.has_extra_parameters
            || input.code.is_empty()
            || input.now >= input.code_expires_at
        {
            return Ok(None);
        }
        let mut state = self.0.lock().map_err(|_| "OAuth PAR lock poisoned")?;
        let State { pushed, issued } = &mut *state;
        let key = (input.session.issuer.clone(), input.uri.0.to_owned());
        let Some(slot) = pushed.get_mut(&key) else {
            return Ok(None);
        };
        let Some(record) = slot.as_ref() else {
            return Ok(None);
        };
        if record.request.session != *input.session
            || record.registration.issuer != input.session.issuer
            || record.registration.client != input.session.client
            || input.now >= record.expires_at
            || !record.request.permits(&input.grant)
            || !issued.insert((input.session.issuer.clone(), input.code.clone()))
        {
            return Ok(None);
        }
        let registration = record.registration.clone();
        let session = record.request.session.clone();
        let codes = CodeLedger::new(vec![Issued {
            code: input.code,
            session: session.clone(),
            grant: input.grant,
            expires_at: input.code_expires_at,
        }]);
        *slot = None;
        Ok(Some(Authorized {
            registration,
            session,
            codes,
        }))
    }
}

impl Authorized {
    pub fn redeem(
        &self,
        verified: &VerifiedClient<oauth_code::Request>,
        now: u64,
    ) -> Result<Option<RedeemedGrant>, String> {
        if !verified.matches(&self.registration) {
            return Ok(None);
        }
        self.codes.redeem(&self.session, &verified.request, now)
    }
}

#[cfg(test)]
#[path = "../../tests/unit/gateway_oauth_par.rs"]
mod tests;
