//! Phase-owned diagnostic counters; unavailable observations stay absent.
use serde::Serialize;

#[derive(Serialize)]
pub(crate) struct MemoryPhase {
    live_before_bytes: usize,
    live_after_bytes: usize,
    phase_peak_requested_bytes: usize,
    allocation_requests: usize,
    requested_bytes: usize,
    system: super::system::SystemMemory,
}

pub(crate) fn begin_phase() -> Option<[usize; 4]> {
    #[cfg(feature = "allocation-observation")]
    {
        Some(super::enabled::begin_window())
    }
    #[cfg(not(feature = "allocation-observation"))]
    {
        None
    }
}
pub(crate) fn end_phase(before: Option<[usize; 4]>) -> Option<MemoryPhase> {
    #[cfg(feature = "allocation-observation")]
    {
        let before = before?;
        let after = super::enabled::snapshot();
        Some(MemoryPhase {
            live_before_bytes: before[2],
            live_after_bytes: after[2],
            phase_peak_requested_bytes: super::enabled::window_peak(),
            allocation_requests: after[0] - before[0],
            requested_bytes: after[1] - before[1],
            system: super::system::snapshot(),
        })
    }
    #[cfg(not(feature = "allocation-observation"))]
    {
        let _ = before;
        None
    }
}
