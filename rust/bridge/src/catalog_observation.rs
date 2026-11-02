//! Optional full-catalog stage observations; never admission inputs.
use serde::Serialize;
use std::collections::BTreeMap;
use std::time::Instant;
#[derive(Default, Serialize)]
pub(crate) struct CatalogObservation {
    pub decode_ns: u128,
    pub entries_ns: u128,
    pub shared_preparation_ns: u128,
    pub finalization_ns: u128,
    pub cleanup_ns: u128,
    pub retained_manifests: usize,
    pub entries: BTreeMap<String, EntryObservation>,
    pub memory: BTreeMap<String, crate::allocation::MemoryPhase>,
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

pub(crate) fn memory_start(observation: &Option<&mut CatalogObservation>) -> Option<[usize; 4]> {
    observation
        .as_ref()
        .and_then(|_| crate::allocation::begin_phase())
}
pub(crate) fn memory_end(
    observation: &mut Option<&mut CatalogObservation>,
    label: &str,
    before: Option<[usize; 4]>,
) {
    if let (Some(observation), Some(phase)) = (
        observation.as_deref_mut(),
        crate::allocation::end_phase(before),
    ) {
        observation.memory.insert(label.to_owned(), phase);
    }
}

pub(crate) fn memory_end_entry(
    observation: &mut Option<&mut CatalogObservation>,
    name: &str,
    before: Option<[usize; 4]>,
) {
    if before.is_some() {
        memory_end(observation, &format!("entry:{name}"), before);
    }
}
