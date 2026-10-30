//! Optional process-wide allocation observations, never used by admission.
#[cfg(feature = "allocation-observation")]
mod enabled;
mod snapshot;
pub(crate) use snapshot::snapshot;
