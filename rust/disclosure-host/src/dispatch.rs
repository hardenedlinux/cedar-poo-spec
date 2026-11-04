//! Trusted local persistence and a simulated final receiver for disclosure.
use super::Effect;
use cedar_poo_core::operation_identity::OperationId;
use cedar_poo_runtime::gateway::{Signed, public_key, verify};
use cedar_poo_runtime::gateway_source_sha256;
use serde::{Deserialize, Serialize};
use std::fs::{File, OpenOptions};
use std::io::{self, Read};
use std::path::{Path, PathBuf};

/// Exact acknowledged image identity retained independently of a candidate
/// replica. A fingerprint is evidence of equality, not an authority signature.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AcknowledgedImage {
    domain: String,
    digest: String,
}

impl AcknowledgedImage {
    pub(crate) fn capture(domain: &str, files: &impl Serialize) -> Result<Self, String> {
        Ok(Self {
            domain: domain.into(),
            digest: gateway_source_sha256(&(domain, files))?,
        })
    }

    pub(crate) fn require(&self, actual: &Self) -> Result<(), String> {
        if self != actual {
            return Err("candidate differs from independently acknowledged image".into());
        }
        Ok(())
    }
}

/// Authority identity and generation obtained through the trusted control plane.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverCut {
    pub scope: String,
    pub generation: u64,
}

/// Exact admitted operation, transmitted by an authenticated Host adapter.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DispatchBinding {
    operation: String,
    effect: String,
    cut: ReceiverCut,
}

impl DispatchBinding {
    pub(crate) fn new(effect: &Effect, cut: ReceiverCut) -> Result<Self, String> {
        if effect.operation_id.0.is_empty() || cut.scope.is_empty() {
            return Err("missing operation identity or receiver scope".into());
        }
        let selection = effect
            .selection_delta
            .as_ref()
            .map(|d| (&d.before, &d.after));
        let digest = gateway_source_sha256(&(
            "cedar-poo/disclosure-effect/v1",
            &effect.operation_id.0,
            &effect.sources,
            &effect.destination,
            &effect.purpose,
            &effect.channel,
            &effect.recipients,
            &effect.payload_digest,
            &effect.candidate_ids,
            selection,
        ))?;
        Ok(Self {
            operation: effect.operation_id.0.clone(),
            effect: digest,
            cut,
        })
    }
}

/// Provider evidence uses a dedicated signing root and an exact dispatch binding.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DisclosureOutcome {
    pub domain: String,
    pub binding: DispatchBinding,
    pub delivered: bool,
}

impl DisclosureOutcome {
    pub const DOMAIN: &str = "cedar-poo/disclosure-outcome/v1";
}

/// One trusted, non-rollback directory per workflow authority. Records are
/// immutable. A torn or unreadable reservation cannot authorize another send.
struct DispatchJournal<'a> {
    directory: &'a Path,
}

impl<'a> DispatchJournal<'a> {
    fn new(directory: &'a Path) -> Self {
        Self { directory }
    }

    fn path(&self, operation: &str) -> Result<PathBuf, String> {
        Ok(self.directory.join(gateway_source_sha256(&operation)?))
    }

    fn reserve(&self, binding: &DispatchBinding) -> Result<bool, String> {
        let path = self.path(&binding.operation)?;
        let mut file = match OpenOptions::new().write(true).create_new(true).open(path) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => return Ok(false),
            Err(error) => return Err(error.to_string()),
        };
        serde_json::to_writer(&mut file, binding).map_err(|e| e.to_string())?;
        file.sync_all().map_err(|e| e.to_string())?;
        File::open(self.directory)
            .and_then(|dir| dir.sync_all())
            .map_err(|e| e.to_string())?;
        Ok(true)
    }
}

pub(crate) fn verify_outcome(
    reserved: &DispatchBinding,
    signed: &Signed,
    configured_provider_key: &[u8],
) -> Result<bool, String> {
    let outcome: DisclosureOutcome = verify(signed, &public_key(configured_provider_key)?)?;
    if outcome.domain != DisclosureOutcome::DOMAIN || outcome.binding != *reserved {
        return Err("provider outcome does not match the retained dispatch".into());
    }
    Ok(outcome.delivered)
}

pub(crate) fn lock(directory: &Path, name: &str) -> Result<File, String> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(directory.join(format!("{name}.lock")))
        .map_err(|e| e.to_string())?;
    file.lock().map_err(|e| e.to_string())?;
    Ok(file)
}

pub(crate) fn read<T: serde::de::DeserializeOwned>(
    directory: &Path,
    name: &str,
) -> Result<T, String> {
    let file = File::open(directory.join(format!("{name}.json"))).map_err(|e| e.to_string())?;
    serde_json::from_reader(file).map_err(|e| e.to_string())
}

/// Call under the matching stable file lock.
pub(crate) fn atomic_write(
    directory: &Path,
    name: &str,
    value: &impl Serialize,
) -> Result<(), String> {
    let staged = directory.join(format!("{name}.staged"));
    match std::fs::remove_file(&staged) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.to_string()),
    }
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&staged)
        .map_err(|e| e.to_string())?;
    serde_json::to_writer(&mut file, value).map_err(|e| e.to_string())?;
    file.sync_all().map_err(|e| e.to_string())?;
    std::fs::rename(staged, directory.join(format!("{name}.json"))).map_err(|e| e.to_string())?;
    sync_directory(directory)
}

pub(crate) fn durable_contents(path: &Path) -> Result<String, String> {
    let mut file = File::open(path).map_err(|e| e.to_string())?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .map_err(|e| e.to_string())?;
    file.sync_all().map_err(|e| e.to_string())?;
    Ok(contents)
}

pub(crate) fn sync_directory(directory: &Path) -> Result<(), String> {
    File::open(directory)
        .and_then(|dir| dir.sync_all())
        .map_err(|e| e.to_string())
}

/// Receiver cut writers and effect application share the durable file lock.
/// Real transports must authenticate the Host before calling this boundary.
pub struct DisclosureReceiver {
    directory: PathBuf,
}

impl DisclosureReceiver {
    pub fn initialize(directory: &Path, current: &ReceiverCut) -> Result<(), String> {
        let _guard = lock(directory, "receiver")?;
        if current.scope.is_empty() {
            return Err("missing receiver scope".into());
        }
        match std::fs::symlink_metadata(directory.join("receiver.json")) {
            Ok(_) => return Err("receiver already initialized".into()),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error.to_string()),
        }
        atomic_write(directory, "receiver", current)
    }

    pub fn open(directory: &Path) -> Result<Self, String> {
        let _guard = lock(directory, "receiver")?;
        let current: ReceiverCut = read(directory, "receiver")?;
        if current.scope.is_empty() {
            return Err("missing receiver scope".into());
        }
        Ok(Self {
            directory: directory.into(),
        })
    }

    /// Capture under the receiver lock at the promotion barrier. Persist the
    /// result in an independent trusted store before losing the source replica.
    pub fn recovery_point(&self) -> Result<AcknowledgedImage, String> {
        let _guard = lock(&self.directory, "receiver")?;
        receiver_point(&self.directory)
    }

    /// Quiesce the old writer and qualify the candidate before enabling it.
    pub fn open_failover(directory: &Path, expected: &AcknowledgedImage) -> Result<Self, String> {
        let _guard = lock(directory, "receiver")?;
        expected.require(&receiver_point(directory)?)?;
        Ok(Self {
            directory: directory.into(),
        })
    }

    pub fn advance(&self, next: &ReceiverCut) -> Result<(), String> {
        let _guard = lock(&self.directory, "receiver")?;
        let current: ReceiverCut = read(&self.directory, "receiver")?;
        if current.scope != next.scope || next.generation <= current.generation {
            return Err("receiver cut regressed or changed scope".into());
        }
        atomic_write(&self.directory, "receiver", next)
    }

    /// Apply only once, then persist the independent provider's signed
    /// observation before returning it. Failure after apply remains unknown.
    pub fn receive(
        &self,
        request: &DispatchBinding,
        actual: &Effect,
        provider_key: &[u8],
        apply: impl FnOnce(&Effect) -> Result<Signed, String>,
    ) -> Result<Option<Signed>, String> {
        let _guard = lock(&self.directory, "receiver")?;
        let current: ReceiverCut = read(&self.directory, "receiver")?;
        let journal = DispatchJournal::new(&self.directory);
        if request.cut != current
            || DispatchBinding::new(actual, current)? != *request
            || !journal.reserve(request)?
        {
            return Ok(None);
        }
        let signed = apply(actual)?;
        verify_outcome(request, &signed, provider_key)?;
        atomic_write(&self.directory, &outcome_name(&request.operation)?, &signed)?;
        Ok(Some(signed))
    }

    /// A restarted provider can return evidence without reapplying the effect.
    /// Missing outcome bytes are unknown, including for a reserved operation.
    pub fn outcome(&self, id: &OperationId, provider_key: &[u8]) -> Result<Option<Signed>, String> {
        let _guard = lock(&self.directory, "receiver")?;
        let name = outcome_name(&id.0)?;
        let file = match File::open(self.directory.join(format!("{name}.json"))) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(error.to_string()),
        };
        let signed = serde_json::from_reader(file).map_err(|e| e.to_string())?;
        let reservation = File::open(DispatchJournal::new(&self.directory).path(&id.0)?)
            .map_err(|e| e.to_string())?;
        let binding: DispatchBinding =
            serde_json::from_reader(reservation).map_err(|e| e.to_string())?;
        if binding.operation != id.0 {
            return Err("provider reservation belongs to a different operation".into());
        }
        verify_outcome(&binding, &signed, provider_key)?;
        sync_directory(&self.directory)?;
        Ok(Some(signed))
    }
}

fn outcome_name(operation: &str) -> Result<String, String> {
    Ok(format!("outcome-{}", gateway_source_sha256(&operation)?))
}

// Include unresolved reservations as well as acknowledged receipts. Ignore
// staged writes and lock files, which are not part of the committed image.
fn receiver_point(directory: &Path) -> Result<AcknowledgedImage, String> {
    let current: ReceiverCut = read(directory, "receiver")?;
    if current.scope.is_empty() {
        return Err("missing receiver scope".into());
    }
    let mut files = std::collections::BTreeMap::new();
    for entry in std::fs::read_dir(directory).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        let digest = name
            .strip_prefix("outcome-")
            .and_then(|part| part.strip_suffix(".json"));
        if name == "receiver.json" || is_digest(name) || digest.is_some_and(is_digest) {
            let contents = durable_contents(&entry.path())?;
            files.insert(name.to_owned(), gateway_source_sha256(&contents)?);
        }
    }
    if !files.contains_key("receiver.json") {
        return Err("missing committed receiver cut".into());
    }
    sync_directory(directory)?;
    AcknowledgedImage::capture("cedar-poo/disclosure-receiver-image/v1", &files)
}

fn is_digest(name: &str) -> bool {
    name.len() == 64
        && name
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}
