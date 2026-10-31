//! Snapshot interface for the optional observer.
#[cfg(feature = "allocation-observation")]
use super::enabled;
pub(crate) fn snapshot() -> Option<[usize; 4]> {
    #[cfg(feature = "allocation-observation")]
    {
        Some(enabled::snapshot())
    }
    #[cfg(not(feature = "allocation-observation"))]
    {
        None
    }
}
