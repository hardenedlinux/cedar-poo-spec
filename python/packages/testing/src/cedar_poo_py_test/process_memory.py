"""Sample resident bytes of a caller-owned child; never a heap or RSS bound."""
import ctypes
import json
import os
from pathlib import Path
import platform
import threading
import time


SYSTEM = platform.system()
PAGE_SIZE = os.sysconf("SC_PAGE_SIZE")


class TaskInfo(ctypes.Structure):
    # Darwin SDK sys/proc_info.h: six uint64 fields, twelve int32 fields.
    _fields_ = [("virtual", ctypes.c_uint64), ("resident", ctypes.c_uint64),
                ("times", ctypes.c_uint64 * 4), ("statistics", ctypes.c_int32 * 12)]


if SYSTEM == "Darwin":
    LIBPROC = ctypes.CDLL("/usr/lib/libproc.dylib", use_errno=True)
    LIBPROC.proc_pidinfo.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_uint64,
                                   ctypes.c_void_p, ctypes.c_int]
    LIBPROC.proc_pidinfo.restype = ctypes.c_int


def resident_bytes(pid: int) -> int:
    if SYSTEM == "Darwin":
        value = TaskInfo()
        size = ctypes.sizeof(value)
        if LIBPROC.proc_pidinfo(pid, 4, 0, ctypes.byref(value), size) != size:
            raise OSError(ctypes.get_errno(), "proc_pidinfo did not return complete task info")
        return value.resident
    if SYSTEM == "Linux":
        return int(Path(f"/proc/{pid}/statm").read_text().split()[1]) * PAGE_SIZE
    raise OSError("unsupported resident-byte observation platform")


class ProcessMemory:
    """Fixed 5-ms diagnostic only. The launcher passes its own Popen child's PID."""
    def __init__(self, child):
        self.child = child
        self.pid = child.pid
        self.samples = []
        self.stop = threading.Event()
        self.thread = threading.Thread(target=self._sample, daemon=True)
        self.thread.start()

    def _sample(self):
        while not self.stop.is_set():
            if self.child.poll() is not None:
                break
            began = time.time_ns()
            try:
                value = {"resident_bytes": resident_bytes(self.pid)}
            except (OSError, ValueError, IndexError) as error:
                value = {"error": str(error)}
            # Discard a read if the owned child exited across the syscall.
            # A reused numeric PID cannot become an accepted observation.
            if self.child.poll() is not None:
                break
            self.samples.append({"unix_before_ns": began, "unix_after_ns": time.time_ns(), **value})
            self.stop.wait(0.005)

    def finish(self, path: Path) -> dict:
        self.stop.set()
        self.thread.join(timeout=1)
        samples = list(self.samples)
        values = [sample["resident_bytes"] for sample in samples if "resident_bytes" in sample]
        report = {"pid": self.pid, "interval_ns": 5_000_000, "stopped": not self.thread.is_alive(),
                  "scope": "Current resident bytes, sampled externally; can miss short peaks; not retained heap, OS high-water RSS, or a bound. Instrumented launch only.",
                  "samples": samples}
        path.write_text(json.dumps(report, indent=2) + "\n")
        return {"report": str(path.resolve()), "samples": len(values), "stopped": report["stopped"],
                "sampled_resident_peak_bytes": max(values) if values else None}
