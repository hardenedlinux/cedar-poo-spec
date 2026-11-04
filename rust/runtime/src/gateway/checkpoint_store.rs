//! Independent checkpoint custody on a trusted local Unix filesystem.
use super::{LogSnapshot, Signed, WitnessFrontier};
use p256::ecdsa::VerifyingKey;
use serde::{Serialize, de::DeserializeOwned};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::Path;

/// A separate, trusted directory owned by the checkpoint authority.
/// All writers must use the same lock file and preserve it across restart.
pub struct CheckpointStore<'a> {
    directory: &'a Path,
    key: &'a VerifyingKey,
}

impl<'a> CheckpointStore<'a> {
    pub fn new(directory: &'a Path, key: &'a VerifyingKey) -> Self {
        Self { directory, key }
    }

    /// Explicit bootstrap with a checkpoint obtained from the trusted authority.
    /// A missing pin during recovery must never trigger automatic bootstrap.
    pub fn initialize(&self, trusted: &Signed) -> Result<(), String> {
        WitnessFrontier::from_checkpoint(trusted, self.key)?;
        let file = LockedCheckpoint::open(self.directory)?;
        file.initialize(trusted)
    }

    /// Reopen the pinned frontier after restart. Missing or invalid data refuses.
    pub fn load(&self) -> Result<WitnessFrontier, String> {
        let file = LockedCheckpoint::open(self.directory)?;
        WitnessFrontier::from_checkpoint(&file.read()?, self.key)
    }

    /// Advance under the same writer lock as the durable read. A competing
    /// writer must extend the winner's prefix even if it uses the same key.
    pub fn advance(&self, candidate: &LogSnapshot) -> Result<(), String> {
        let file = LockedCheckpoint::open(self.directory)?;
        WitnessFrontier::from_checkpoint(&file.read()?, self.key)?.verify_extension(candidate)?;
        file.persist(&candidate.checkpoint)
    }
}

/// A live lock over the checkpoint file in an independently trusted directory.
pub(super) struct LockedCheckpoint<'a> {
    directory: &'a Path,
    _lock: File,
}

impl<'a> LockedCheckpoint<'a> {
    pub(super) fn initialize(&self, value: &impl Serialize) -> Result<(), String> {
        match fs::symlink_metadata(self.directory.join("checkpoint.json")) {
            Ok(_) => Err("independent checkpoint already initialized".into()),
            Err(error) if error.kind() == io::ErrorKind::NotFound => self.persist(value),
            Err(error) => Err(error.to_string()),
        }
    }

    pub(super) fn read<T: DeserializeOwned>(&self) -> Result<T, String> {
        let file = File::open(self.directory.join("checkpoint.json")).map_err(|e| e.to_string())?;
        serde_json::from_reader(file).map_err(|e| e.to_string())
    }

    pub(super) fn open(directory: &'a Path) -> Result<Self, String> {
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(directory.join("checkpoint.lock"))
            .map_err(|e| e.to_string())?;
        lock.lock().map_err(|e| e.to_string())?;
        Ok(Self {
            directory,
            _lock: lock,
        })
    }

    pub(super) fn persist(&self, checkpoint: &impl Serialize) -> Result<(), String> {
        let staged = self.directory.join("checkpoint.staged");
        match fs::remove_file(&staged) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error.to_string()),
        }
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&staged)
            .map_err(|e| e.to_string())?;
        serde_json::to_writer(&mut file, checkpoint).map_err(|e| e.to_string())?;
        file.flush().map_err(|e| e.to_string())?;
        file.sync_all().map_err(|e| e.to_string())?;
        fs::rename(staged, self.directory.join("checkpoint.json")).map_err(|e| e.to_string())?;
        self.sync_directory()
    }

    pub(super) fn sync_directory(&self) -> Result<(), String> {
        File::open(self.directory)
            .and_then(|dir| dir.sync_all())
            .map_err(|e| e.to_string())
    }
}
