//! Independent witness precommit, signed checkpoint and public verification.
use super::wire::{sign, simulation_key};
use super::{EffectIdentity, FactBinding, ReviewBinding, Signed, Version, verify};
use crate::json_sha256;
use p256::ecdsa::{SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
/// Signed witness precommit binding exact effect, review and source digests.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Commit {
    pub current_world: String,
    pub version: Version,
    pub sequence: u64,
    pub previous: String,
    pub effect: EffectIdentity,
    pub review: ReviewBinding,
    pub facts: Vec<String>,
    pub publications: Vec<String>,
    /// Requires the composed current-use path at the durable receiver.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub oauth_target: Option<super::oauth::Target>,
}
/// Signed witness head; currentness requires an independent minimum size.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Checkpoint {
    pub version: Version,
    pub size: u64,
    pub root: String,
}
/// Public checkpoint and entries; contains no private signing material.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LogSnapshot {
    pub checkpoint: Signed,
    pub entries: Vec<Signed>,
}
/// Verify using public material and an independently retained minimum checkpoint.
pub fn verify_log(
    snapshot: &LogSnapshot,
    key: &VerifyingKey,
    minimum_size: u64,
) -> Result<Vec<Commit>, String> {
    Ok(verify_view(snapshot.view(), key, minimum_size)?.records)
}

/// Borrowed immutable bytes; verification does not clone a detached log.
#[derive(Clone, Copy)]
pub(super) struct LogView<'a> {
    pub(super) checkpoint: &'a Signed,
    pub(super) entries: &'a [Signed],
}
impl LogSnapshot {
    pub(super) fn view(&self) -> LogView<'_> {
        LogView {
            checkpoint: &self.checkpoint,
            entries: &self.entries,
        }
    }
}
/// One full verification owns typed metadata, bound to these exact borrowed bytes.
pub(super) struct VerifiedLog<'a> {
    view: LogView<'a>,
    records: Vec<Commit>,
    head: Checkpoint,
    key: VerifyingKey,
}
impl VerifiedLog<'_> {
    pub(super) fn view(&self) -> LogView<'_> {
        self.view
    }
    pub(super) fn records(&self) -> &[Commit] {
        &self.records
    }
    pub(super) fn key(&self) -> VerifyingKey {
        self.key
    }
    pub(super) fn frontier(&self) -> WitnessFrontier {
        WitnessFrontier {
            key: self.key,
            size: self.records.len(),
            root: self.head.root.clone(),
        }
    }
    pub(super) fn check_frontier(&self, prior: &WitnessFrontier) -> Result<(), String> {
        let root = if prior.size == 0 {
            ""
        } else if prior.size == self.records.len() {
            &self.head.root
        } else if let Some(next) = self.records.get(prior.size) {
            &next.previous
        } else {
            return Err("recovery witness frontier regressed".into());
        };
        if prior.key != self.key || prior.size > self.records.len() || prior.root != root {
            return Err("recovery witness frontier changed prefix or key".into());
        }
        Ok(())
    }
    pub(super) fn intent(&self, signed: &Signed) -> Option<&Commit> {
        self.view
            .entries
            .iter()
            .zip(&self.records)
            .find_map(|(entry, record)| {
                (entry.payload == signed.payload && entry.signature == signed.signature)
                    .then_some(record)
            })
    }
}
pub(super) fn verify_view<'a>(
    snapshot: LogView<'a>,
    key: &VerifyingKey,
    minimum_size: u64,
) -> Result<VerifiedLog<'a>, String> {
    let head: Checkpoint = verify(snapshot.checkpoint, key)?;
    if head.version != (Version { major: 1, minor: 0 })
        || head.size != snapshot.entries.len() as u64
        || head.size < minimum_size
    {
        return Err("invalid or rolled-back checkpoint".into());
    }
    let (previous, records) = snapshot.entries.iter().enumerate().try_fold(
        (String::new(), Vec::with_capacity(snapshot.entries.len())),
        |(previous, mut records), (index, signed)| {
            let entry: Commit = verify(signed, key)?;
            if entry.version != head.version
                || entry.sequence != index as u64
                || entry.previous != previous
            {
                return Err("broken public log history".into());
            }
            let previous = signed.source_sha256()?;
            records.push(entry);
            Ok::<_, String>((previous, records))
        },
    )?;
    if previous != head.root {
        return Err("public checkpoint root mismatch".into());
    }
    Ok(VerifiedLog {
        view: snapshot,
        records,
        head,
        key: *key,
    })
}
/// Compact trusted progress, retained only after a complete public-log check.
/// The boundary digest binds the prefix under the verified chain assumption.
#[derive(Clone, PartialEq, Eq)]
pub struct WitnessFrontier {
    key: VerifyingKey,
    size: usize,
    root: String,
}
impl WitnessFrontier {
    /// Check that a candidate extends the independently retained committed prefix.
    pub fn verify_extension(&self, candidate: &LogSnapshot) -> Result<(), String> {
        let verified = verify_view(candidate.view(), &self.key, self.size as u64)?;
        verified.check_frontier(self)
    }

    /// Bind a checkpoint read from independent durable authority. Signature
    /// verification does not establish freshness or consensus on its own.
    pub fn from_checkpoint(checkpoint: &Signed, key: &VerifyingKey) -> Result<Self, String> {
        let head: Checkpoint = verify(checkpoint, key)?;
        if head.version != (Version { major: 1, minor: 0 })
            || (head.size == 0 && !head.root.is_empty())
            || (head.size != 0
                && (head.root.len() != 64
                    || !head
                        .root
                        .bytes()
                        .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))))
        {
            return Err("invalid independent checkpoint".into());
        }
        Ok(Self {
            key: *key,
            size: usize::try_from(head.size).map_err(|_| "checkpoint size exceeds platform")?,
            root: head.root,
        })
    }

    pub(crate) fn check(&self, entries: &[Signed], key: &VerifyingKey) -> Result<(), String> {
        if self.key != *key || entries.len() < self.size {
            return Err("recovery witness frontier regressed or changed key".into());
        }
        let root = self
            .size
            .checked_sub(1)
            .map(|index| entries[index].source_sha256())
            .transpose()?
            .unwrap_or_default();
        if root != self.root {
            return Err("recovery witness frontier changed prefix".into());
        }
        Ok(())
    }
}

/// Independent simulated witness. Its records are not reconstructed from outcomes.
pub struct Witness {
    key: SigningKey,
    entries: Vec<Signed>,
    pub available: bool,
    head: Checkpoint,
    checkpoint: Signed,
}
impl Witness {
    pub fn simulation() -> Self {
        static EMPTY: std::sync::LazyLock<Signed> = std::sync::LazyLock::new(|| {
            sign(
                &Checkpoint {
                    version: Version { major: 1, minor: 0 },
                    size: 0,
                    root: String::new(),
                },
                &simulation_key(2),
            )
            .expect("fixed checkpoint")
        });
        Self {
            key: simulation_key(2),
            entries: vec![],
            available: true,
            head: Checkpoint {
                version: Version { major: 1, minor: 0 },
                size: 0,
                root: String::new(),
            },
            checkpoint: EMPTY.clone(),
        }
    }
    /// Borrow the append-only owned history; external bytes use the restore boundary.
    pub fn entries(&self) -> &[Signed] {
        &self.entries
    }
    /// Import untrusted historical bytes using the configured simulation witness
    /// key and an independently retained minimum size, before accepting ownership.
    pub fn restore(snapshot: &LogSnapshot, minimum_size: u64) -> Result<Self, String> {
        let mut witness = Self::simulation();
        let verified = verify_view(snapshot.view(), &witness.verifying_key(), minimum_size)?;
        witness.entries = snapshot.entries.clone();
        witness.head = verified.head;
        witness.checkpoint = snapshot.checkpoint.clone();
        Ok(witness)
    }
    pub fn snapshot(&self) -> LogSnapshot {
        LogSnapshot {
            checkpoint: self.checkpoint.clone(),
            entries: self.entries.clone(),
        }
    }
    pub(super) fn minimum_size(&self) -> u64 {
        self.head.size
    }
    pub(super) fn view(&self) -> LogView<'_> {
        LogView {
            checkpoint: &self.checkpoint,
            entries: &self.entries,
        }
    }
    pub(super) fn frontier(&self) -> WitnessFrontier {
        WitnessFrontier {
            key: self.verifying_key(),
            size: self.entries.len(),
            root: self.head.root.clone(),
        }
    }
    pub(super) fn check_frontier(&self, frontier: &WitnessFrontier) -> Result<(), String> {
        if frontier.key == self.verifying_key()
            && frontier.size == self.entries.len()
            && frontier.root == self.head.root
        {
            Ok(())
        } else {
            frontier.check(&self.entries, &self.verifying_key())
        }
    }
    pub fn verifying_key(&self) -> VerifyingKey {
        *self.key.verifying_key()
    }
    pub fn verify_history(&self) -> Result<(), String> {
        verify_view(self.view(), &self.verifying_key(), self.head.size).map(|_| ())
    }
    pub(super) fn append(&mut self, input: PrecommitInput<'_>) -> Result<Signed, String> {
        self.append_with_target(input, None)
    }
    pub(super) fn append_with_target(
        &mut self,
        input: PrecommitInput<'_>,
        oauth_target: Option<super::oauth::Target>,
    ) -> Result<Signed, String> {
        let PrecommitInput {
            current_world,
            effect,
            review,
            facts,
            publications,
        } = input;
        if !self.available {
            return Err("precommit unavailable".into());
        }
        // Only this owner can mutate the validated append-only prefix. Untrusted
        // restore verifies every record before ownership; append checks the
        // owned counter instead of verifying the whole prefix again.
        if self.entries.len() as u64 != self.head.size {
            return Err("witness size changed".into());
        }
        let entry = Commit {
            current_world: current_world.to_owned(),
            version: Version { major: 1, minor: 0 },
            sequence: self.entries.len() as u64,
            previous: self.head.root.clone(),
            effect: effect.clone(),
            review: review.clone(),
            facts: facts.iter().map(json_sha256).collect::<Result<_, _>>()?,
            publications: publications
                .iter()
                .map(Signed::source_sha256)
                .collect::<Result<_, _>>()?,
            oauth_target,
        };
        let signed = sign(&entry, &self.key)?;
        let committed_root = signed.source_sha256()?;
        let committed_size = self
            .head
            .size
            .checked_add(1)
            .ok_or("witness counter exhausted")?;
        let head = Checkpoint {
            version: Version { major: 1, minor: 0 },
            size: committed_size,
            root: committed_root,
        };
        let checkpoint = sign(&head, &self.key)?;
        self.head = head;
        self.checkpoint = checkpoint;
        self.entries.push(signed.clone());
        Ok(signed)
    }
}

pub(super) struct PrecommitInput<'a> {
    pub current_world: &'a str,
    pub(super) effect: &'a EffectIdentity,
    pub(super) review: &'a ReviewBinding,
    pub(super) facts: &'a [FactBinding],
    pub(super) publications: &'a [Signed],
}
