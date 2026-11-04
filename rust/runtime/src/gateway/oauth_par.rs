//! Pushed authorization reference for confidential clients.
use super::oauth::{Confirmation, CurrentUse, Grant, ReplayGuard};
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
    pub(super) fn matches(&self, registration: &Registration) -> bool {
        self.issuer == registration.issuer
            && self.client == registration.client
            && self.credential == registration.credential
            && !registration.credential.thumbprint().is_empty()
    }
}

/// Key from a DPoP proof verified for the actual PAR request.
pub struct VerifiedParDpop(pub String);

/// Sender constraint requested over the authenticated PAR back channel.
pub enum ParSender {
    Dpop {
        jkt: Option<String>,
        proof: Option<VerifiedParDpop>,
    },
    Mtls,
}

impl ParSender {
    fn key<'a>(jkt: Option<&'a str>, proof: Option<&'a VerifiedParDpop>) -> Option<&'a str> {
        let key = jkt.or(proof.map(|observed| observed.0.as_str()))?;
        (!key.is_empty() && proof.is_none_or(|observed| observed.0 == key)).then_some(key)
    }

    fn valid(&self) -> bool {
        match self {
            Self::Dpop { jkt, proof } => Self::key(jkt.as_deref(), proof.as_ref()).is_some(),
            Self::Mtls => true,
        }
    }

    fn permits(&self, confirmation: &Confirmation) -> bool {
        match (self, confirmation) {
            (Self::Dpop { jkt, proof }, Confirmation::Dpop(key)) => {
                Self::key(jkt.as_deref(), proof.as_ref()) == Some(key.as_str())
            }
            (Self::Mtls, Confirmation::Mtls(certificate)) => !certificate.is_empty(),
            _ => false,
        }
    }
}

/// Authorization parameters received in the authenticated back channel.
pub struct ParRequest {
    pub session: Session,
    pub audiences: Vec<String>,
    pub scopes: Vec<String>,
    pub sender: ParSender,
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
            && self.sender.permits(&grant.confirmation)
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
            || !verified.request.sender.valid()
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
            || input.code_expires_at - input.now > 60
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

/// Key from a DPoP proof verified for the actual token request.
pub struct VerifiedTokenDpop(pub String);

/// Sender evidence verified on the actual token request.
pub enum TokenSender {
    Dpop(VerifiedTokenDpop),
    Mtls(String),
}

impl TokenSender {
    pub(super) fn matches(&self, client: &Credential, confirmation: &Confirmation) -> bool {
        match (self, confirmation) {
            (Self::Dpop(proof), Confirmation::Dpop(key)) => !key.is_empty() && proof.0 == *key,
            (Self::Mtls(peer), Confirmation::Mtls(certificate)) => {
                !certificate.is_empty()
                    && peer == certificate
                    && match client {
                        Credential::Mtls(authenticated) => peer == authenticated,
                        Credential::PrivateKeyJwt(_) => true,
                    }
            }
            _ => false,
        }
    }
}

/// Token request with code redemption and sender-constraint evidence.
pub struct ParTokenRequest {
    pub redemption: oauth_code::Request,
    pub sender: TokenSender,
}

/// Successful PAR-backed redemption with the authenticated client lineage.
pub struct ParRedeemed {
    pub(super) redeemed: RedeemedGrant,
    pub(super) registration: Registration,
}

impl ParRedeemed {
    /// Check an access-only grant against current resource evidence.
    pub fn admit_use(
        &self,
        guard: &ReplayGuard,
        base_allowed: bool,
        current: &CurrentUse,
    ) -> Result<bool, String> {
        self.redeemed.admit_use(guard, base_allowed, current)
    }
}

impl Authorized {
    pub fn redeem(
        &self,
        verified: &VerifiedClient<ParTokenRequest>,
        now: u64,
    ) -> Result<Option<ParRedeemed>, String> {
        if !verified.matches(&self.registration) {
            return Ok(None);
        }
        self.codes
            .redeem_with(&self.session, &verified.request.redemption, now, |grant| {
                verified
                    .request
                    .sender
                    .matches(&verified.credential, &grant.confirmation)
            })
            .map(|redeemed| {
                redeemed.map(|redeemed| ParRedeemed {
                    redeemed,
                    registration: self.registration.clone(),
                })
            })
    }
}

#[cfg(test)]
#[path = "../../tests/unit/gateway_oauth_par.rs"]
mod tests;
