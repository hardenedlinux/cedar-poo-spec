//! System allocator forwarding with optional nonallocating observation.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
static CALLS: AtomicUsize = AtomicUsize::new(0);
static REQUESTED: AtomicUsize = AtomicUsize::new(0);
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static WINDOW_PEAK: AtomicUsize = AtomicUsize::new(0);
struct Observed;
fn add(size: usize) {
    CALLS.fetch_add(1, Ordering::Relaxed);
    REQUESTED.fetch_add(size, Ordering::Relaxed);
    let live = LIVE.fetch_add(size, Ordering::Relaxed) + size;
    PEAK.fetch_max(live, Ordering::Relaxed);
    WINDOW_PEAK.fetch_max(live, Ordering::Relaxed);
}
// SAFETY: all allocation/layout/pointer contracts are forwarded unchanged to
// System. Observation uses only nonallocating atomics, including on failure.
unsafe impl GlobalAlloc for Observed {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller supplies the GlobalAlloc layout contract.
        let pointer = unsafe { System.alloc(layout) };
        if !pointer.is_null() {
            add(layout.size());
        }
        pointer
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller supplies the GlobalAlloc layout contract.
        let pointer = unsafe { System.alloc_zeroed(layout) };
        if !pointer.is_null() {
            add(layout.size());
        }
        pointer
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
        // SAFETY: pointer/layout are the original System allocation pair.
        unsafe { System.dealloc(pointer, layout) };
    }
    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        // SAFETY: pointer/layout/size satisfy the caller's GlobalAlloc contract.
        let next = unsafe { System.realloc(pointer, layout, size) };
        if !next.is_null() {
            LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
            add(size);
        }
        next
    }
}
#[global_allocator]
static ALLOCATOR: Observed = Observed;
pub(super) fn snapshot() -> [usize; 4] {
    [
        CALLS.load(Ordering::Relaxed),
        REQUESTED.load(Ordering::Relaxed),
        LIVE.load(Ordering::Relaxed),
        PEAK.load(Ordering::Relaxed),
    ]
}

// Sequential diagnostic phase windows; concurrent allocations remain process-wide.
pub(super) fn begin_window() -> [usize; 4] {
    let current = snapshot();
    WINDOW_PEAK.store(current[2], Ordering::Relaxed);
    current
}
pub(super) fn window_peak() -> usize {
    WINDOW_PEAK.load(Ordering::Relaxed)
}
