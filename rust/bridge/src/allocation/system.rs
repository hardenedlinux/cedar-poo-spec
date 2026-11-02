//! Read-only platform diagnostics; not application allocation or admission bounds.
use serde::Serialize;
#[derive(Default, Serialize)]
pub(crate) struct SystemMemory {
    pub resident_bytes: Option<u64>,
    pub heap_in_use_bytes: Option<u64>,
    pub heap_reserved_bytes: Option<u64>,
}

#[cfg(all(feature = "allocation-observation", target_os = "macos"))]
pub(super) fn snapshot() -> SystemMemory {
    let mut task = std::mem::MaybeUninit::<libc::proc_taskinfo>::zeroed();
    let length = std::mem::size_of::<libc::proc_taskinfo>() as libc::c_int;
    // SAFETY: own PID, documented PROC_PIDTASKINFO buffer type/size; initialized
    // data is read only after a complete write. No target process is modified.
    let written = unsafe {
        libc::proc_pidinfo(
            libc::getpid(),
            libc::PROC_PIDTASKINFO,
            0,
            task.as_mut_ptr().cast(),
            length,
        )
    };
    let resident = if written == length {
        // SAFETY: proc_pidinfo wrote the complete integer-only proc_taskinfo.
        Some(unsafe { task.assume_init() }.pti_resident_size)
    } else {
        None
    };
    let mut heap = std::mem::MaybeUninit::<libc::malloc_statistics_t>::zeroed();
    // SAFETY: malloc_zone_statistics fills the documented integer-only output;
    // a null zone requests the sum over all allocator zones (SDK malloc.h).
    let heap = unsafe {
        libc::malloc_zone_statistics(std::ptr::null_mut(), heap.as_mut_ptr());
        heap.assume_init()
    };
    SystemMemory {
        resident_bytes: resident,
        heap_in_use_bytes: Some(heap.size_in_use as u64),
        heap_reserved_bytes: Some(heap.size_allocated as u64),
    }
}

#[cfg(all(
    feature = "allocation-observation",
    target_os = "linux",
    target_env = "gnu"
))]
pub(super) fn snapshot() -> SystemMemory {
    // SAFETY: GNU mallinfo2 takes no pointers and returns allocator statistics.
    let heap = unsafe { libc::mallinfo2() };
    // SAFETY: sysconf's documented page-size query takes no pointers.
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    let resident = std::fs::read_to_string("/proc/self/statm")
        .ok()
        .and_then(|s| s.split_whitespace().nth(1)?.parse::<u64>().ok())
        .and_then(|n| u64::try_from(page).ok().and_then(|p| n.checked_mul(p)));
    SystemMemory {
        resident_bytes: resident,
        heap_in_use_bytes: Some((heap.uordblks + heap.hblkhd) as u64),
        heap_reserved_bytes: Some((heap.arena + heap.hblkhd) as u64),
    }
}

#[cfg(all(
    feature = "allocation-observation",
    not(any(target_os = "macos", all(target_os = "linux", target_env = "gnu")))
))]
pub(super) fn snapshot() -> SystemMemory {
    SystemMemory::default()
}
