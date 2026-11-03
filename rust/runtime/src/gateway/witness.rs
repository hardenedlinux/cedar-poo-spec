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
    let head: Checkpoint = verify(&snapshot.checkpoint, key)?;
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
            let previous = json_sha256(signed)?;
            records.push(entry);
            Ok::<_, String>((previous, records))
        },
    )?;
    if previous != head.root {
        return Err("public checkpoint root mismatch".into());
    }
    Ok(records)
}
/// Independent simulated witness. Its records are not reconstructed from outcomes.
pub struct Witness {
    key: SigningKey,
    entries: Vec<Signed>,
    pub available: bool,
    committed_size: usize,
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
            committed_size: 0,
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
        verify_log(snapshot, &witness.verifying_key(), minimum_size)?;
        witness.entries = snapshot.entries.clone();
        witness.committed_size = snapshot.entries.len();
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
        self.committed_size as u64
    }
    pub fn verifying_key(&self) -> VerifyingKey {
        *self.key.verifying_key()
    }
    pub fn verify_history(&self) -> Result<(), String> {
        verify_log(
            &self.snapshot(),
            &self.verifying_key(),
            self.committed_size as u64,
        )
        .map(|_| ())
    }
    pub(super) fn append(&mut self, input: PrecommitInput<'_>) -> Result<Signed, String> {
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
        if self.entries.len() != self.committed_size {
            return Err("witness size changed".into());
        }
        let entry = Commit {
            current_world: current_world.to_owned(),
            version: Version { major: 1, minor: 0 },
            sequence: self.entries.len() as u64,
            previous: self
                .entries
                .last()
                .map(json_sha256)
                .transpose()?
                .unwrap_or_default(),
            effect: effect.clone(),
            review: review.clone(),
            facts: facts.iter().map(json_sha256).collect::<Result<_, _>>()?,
            publications: publications
                .iter()
                .map(json_sha256)
                .collect::<Result<_, _>>()?,
        };
        let signed = sign(&entry, &self.key)?;
        let committed_root = json_sha256(&signed)?;
        let committed_size = self
            .committed_size
            .checked_add(1)
            .ok_or("witness counter exhausted")?;
        let checkpoint = sign(
            &Checkpoint {
                version: Version { major: 1, minor: 0 },
                size: committed_size as u64,
                root: committed_root.clone(),
            },
            &self.key,
        )?;
        self.committed_size = committed_size;
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
