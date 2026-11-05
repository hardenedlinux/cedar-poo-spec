"""Read-only Darwin clock anchors for diagnostic OS-log correlation, not admission."""
import ctypes
import sys
import time


class _Timebase(ctypes.Structure):
    # SDK mach/mach_time.h: two uint32_t fields, kern_return_t result.
    _fields_ = [("numer", ctypes.c_uint32), ("denom", ctypes.c_uint32)]


def clock_anchor() -> dict | None:
    """Bracket both Mach clocks with wall/monotonic samples; failures stay absent.

    Absolute and continuous clocks differ across sleep. Neither a formatted OS
    log timestamp nor its raw ticks are silently treated as Python wall time.
    """
    if sys.platform != "darwin":
        return None
    try:
        library = ctypes.CDLL(None)
        library.mach_timebase_info.argtypes = [ctypes.POINTER(_Timebase)]
        library.mach_timebase_info.restype = ctypes.c_int
        for name in ("mach_absolute_time", "mach_continuous_time"):
            getattr(library, name).argtypes = []
            getattr(library, name).restype = ctypes.c_uint64
        info = _Timebase()
        if ctypes.sizeof(info) != 8 or library.mach_timebase_info(ctypes.byref(info)) or not info.denom:
            return None
        unix_before = time.time_ns()
        mono_before = time.monotonic_ns()
        absolute = library.mach_absolute_time()
        continuous = library.mach_continuous_time()
        mono_after = time.monotonic_ns()
        unix_after = time.time_ns()
        return {"numer": info.numer, "denom": info.denom,
                "absolute_ticks": absolute, "continuous_ticks": continuous,
                "unix_before_ns": unix_before, "unix_after_ns": unix_after,
                "monotonic_before_ns": mono_before, "monotonic_after_ns": mono_after,
                "scope": "Read-only bracketed clock anchor; OS event clock domain requires independent verification"}
    except (AttributeError, OSError, ValueError):
        return None


def mach_event_interval(anchor: dict, ticks: int, domain: str) -> tuple[int, int]:
    """Map verified OS ticks to a monotonic interval, never a wall timestamp.

    The caller must independently establish the event's clock domain and boot.
    When both Mach domains fit the observed clock probe, retain the union of
    their intervals rather than silently choosing one. This is observation,
    not a resource bound, authorization input or causal waiting attribution.
    """
    if domain not in ("absolute", "continuous"):
        raise ValueError("explicit verified Mach clock domain required")
    fields = ("numer", "denom", "monotonic_before_ns", "monotonic_after_ns", domain + "_ticks")
    if type(ticks) is not int or ticks < 0 or any(type(anchor.get(k)) is not int for k in fields):
        raise ValueError("integer Mach ticks and complete integer anchor required")
    numer, denom = anchor["numer"], anchor["denom"]
    before, after = anchor["monotonic_before_ns"], anchor["monotonic_after_ns"]
    if numer <= 0 or denom <= 0 or before < 0 or after < before or anchor[domain + "_ticks"] < 0:
        raise ValueError("invalid timebase or reversed clock bracket")
    scaled = (ticks - anchor[domain + "_ticks"]) * numer
    return before + scaled // denom, after - (-scaled // denom)
