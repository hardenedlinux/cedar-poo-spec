//! Optional full-catalog stage observations; never admission inputs.
use serde::Serialize;
use std::collections::BTreeMap;
use std::time::Instant;
#[derive(Default, Serialize)]
pub(crate) struct CatalogObservation {
    pub decode_ns: u128,
    pub entries_ns: u128,
    pub finalization_ns: u128,
    pub cleanup_ns: u128,
    pub retained_manifests: usize,
    pub entries: BTreeMap<String, EntryObservation>,
}
#[derive(Serialize)]
pub(crate) struct EntryObservation {
    pub elapsed_ns: u128,
    pub kind: String,
    pub rows: usize,
}
pub(crate) fn record(
    observation: &mut Option<&mut CatalogObservation>,
    name: &str,
    started: Option<Instant>,
    kind: &str,
    rows: usize,
) {
    if let (Some(observation), Some(started)) = (observation.as_deref_mut(), started) {
        observation.entries.insert(
            name.to_owned(),
            EntryObservation {
                elapsed_ns: started.elapsed().as_nanos(),
                kind: kind.to_owned(),
                rows,
            },
        );
    }
}
