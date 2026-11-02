//! Optional process-wide allocation observations, never used by admission.
#[cfg(feature = "allocation-observation")]
mod enabled;
mod snapshot;
pub(crate) use snapshot::snapshot;

mod window;
pub(crate) use window::{MemoryPhase, begin_phase, end_phase};
mod system;
