"""Sample resident bytes of a caller-owned child; never a heap or RSS bound."""
import ctypes
import json
import os
from pathlib import Path
import platform
import threading
import time
import uuid


SYSTEM = platform.system()
PAGE_SIZE = os.sysconf("SC_PAGE_SIZE")


class TaskInfo(ctypes.Structure):
    # Darwin SDK sys/proc_info.h: six uint64 fields, twelve int32 fields.
    _fields_ = [("virtual", ctypes.c_uint64), ("resident", ctypes.c_uint64),
                ("times", ctypes.c_uint64 * 4), ("statistics", ctypes.c_int32 * 12)]


class ThreadInfo(ctypes.Structure):
    # Public Darwin SDK sys/proc_info.h, proc_threadinfo; no kernel addresses.
    _fields_ = [("user_time", ctypes.c_uint64), ("system_time", ctypes.c_uint64),
                ("cpu_usage", ctypes.c_int32), ("policy", ctypes.c_int32),
                ("run_state", ctypes.c_int32), ("flags", ctypes.c_int32),
                ("sleep_time", ctypes.c_int32), ("current_priority", ctypes.c_int32),
                ("priority", ctypes.c_int32), ("max_priority", ctypes.c_int32),
                ("name", ctypes.c_char * 64)]


class RUsageInfoV0(ctypes.Structure):
    # Public SDK sys/resource.h: executable UUID and ten uint64 counters.
    _fields_ = [("image_uuid", ctypes.c_uint8 * 16), ("values", ctypes.c_uint64 * 10)]


if SYSTEM == "Darwin":
    LIBPROC = ctypes.CDLL("/usr/lib/libproc.dylib", use_errno=True)
    LIBPROC.proc_pidinfo.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_uint64,
                                   ctypes.c_void_p, ctypes.c_int]
    LIBPROC.proc_pidinfo.restype = ctypes.c_int
    LIBPROC.proc_pid_rusage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]
    LIBPROC.proc_pid_rusage.restype = ctypes.c_int
    LIBPROC.proc_pidpath.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_uint32]
    LIBPROC.proc_pidpath.restype = ctypes.c_int


def process_identity(pid: int) -> dict | None:
    """Public Darwin kernel identity for a caller-owned process, not sample symbols."""
    if SYSTEM != "Darwin":
        return None
    observed_before = time.time_ns()
    info = RUsageInfoV0()
    if LIBPROC.proc_pid_rusage(pid, 0, ctypes.byref(info)) != 0:
        raise OSError(ctypes.get_errno(), "proc_pid_rusage identity unavailable")
    path = ctypes.create_string_buffer(4096)  # Public PROC_PIDPATHINFO_MAXSIZE.
    size = LIBPROC.proc_pidpath(pid, path, len(path))
    if size <= 0 or size > len(path):
        raise OSError(ctypes.get_errno(), "proc_pidpath identity unavailable")
    image = bytes(info.image_uuid)
    return {"pid": pid, "path": os.fsdecode(path.value),
            "image_uuid": str(uuid.UUID(bytes=image)).upper() if any(image) else None,
            "process_start_abstime": info.values[8],
            "unix_before_ns": observed_before, "unix_after_ns": time.time_ns(),
            "scope": "Darwin public proc_pid_rusage V0 + proc_pidpath; raw start clock, not sample image metadata"}


def process_snapshot(pid: int) -> dict:
    if SYSTEM == "Darwin":
        value = TaskInfo()
        size = ctypes.sizeof(value)
        if LIBPROC.proc_pidinfo(pid, 4, 0, ctypes.byref(value), size) != size:
            raise OSError(ctypes.get_errno(), "proc_pidinfo did not return complete task info")
        # Installed Darwin SDK proc_taskinfo layout. Raw task CPU counters
        # remain raw: they are neither wall time nor converted to nanoseconds.
        return {
            "resident_bytes": value.resident, "virtual_bytes": value.virtual,
            "total_user_time_raw": value.times[0], "total_system_time_raw": value.times[1],
            "faults": value.statistics[1], "pageins": value.statistics[2],
            "cow_faults": value.statistics[3], "context_switches": value.statistics[8],
            "threads": value.statistics[9], "running_threads": value.statistics[10],
        }
    if SYSTEM == "Linux":
        return {"resident_bytes": int(Path(f"/proc/{pid}/statm").read_text().split()[1]) * PAGE_SIZE}
    raise OSError("unsupported resident-byte observation platform")


def thread_snapshot(pid: int) -> dict:
    """Optional owned-child scheduler observation, not a kernel wait reason.

    Public PROC_PIDLISTTHREADS returns user-thread handles, not unique thread IDs.
    Each list is consumed immediately; thread exits remain explicit read errors.
    """
    if SYSTEM != "Darwin":
        raise OSError("thread-state observation requires Darwin")
    handles = (ctypes.c_uint64 * 64)()
    size = ctypes.sizeof(handles)
    returned = LIBPROC.proc_pidinfo(pid, 6, 0, handles, size)
    if returned <= 0 or returned > size or returned % 8:
        raise OSError(ctypes.get_errno(), "incomplete thread handle list")
    records = []
    for handle in handles[:returned // 8]:
        value = ThreadInfo()
        length = LIBPROC.proc_pidinfo(pid, 5, handle, ctypes.byref(value), ctypes.sizeof(value))
        if length != ctypes.sizeof(value):
            records.append({"handle": handle, "error": "incomplete thread info",
                            "returned_bytes": length, "errno": ctypes.get_errno()})
            continue
        records.append({"handle": handle, "run_state": value.run_state,
                        "user_time_raw": value.user_time, "system_time_raw": value.system_time,
                        "cpu_usage_raw": value.cpu_usage, "flags": value.flags,
                        "sleep_seconds": value.sleep_time})
    return {"records": records, "capacity": len(handles),
            "possibly_truncated": returned == size}


def resident_bytes(pid: int) -> int:
    return process_snapshot(pid)["resident_bytes"]


class ProcessMemory:
    """Fixed 5-ms diagnostic only. The launcher passes its own Popen child's PID."""
    def __init__(self, child, *, thread_states: bool = False):
        self.child = child
        self.thread_states = thread_states
        self.pid = child.pid
        self.samples = []
        self.identity, self.identity_error = None, None
        self.stop = threading.Event()
        self.thread = threading.Thread(target=self._sample, daemon=True)
        self.thread.start()

    def _sample(self):
        # Metadata reads share the bounded observer thread. A slow kernel read
        # must not block creation of the native process's deadline supervisor.
        if self.child.poll() is None and not self.stop.is_set():
            try:
                self.identity = process_identity(self.pid)
            except OSError as error:
                self.identity_error = str(error)
            if self.child.poll() is not None:
                self.identity = None
                self.identity_error = "owned child exited across identity observation"
        else:
            self.identity_error = "owned child exited or observation stopped before identity read"
        while not self.stop.is_set():
            if self.child.poll() is not None:
                break
            began = time.time_ns()
            try:
                value = process_snapshot(self.pid)
                if self.thread_states:
                    try:
                        value["thread_states"] = thread_snapshot(self.pid)
                    except OSError as error:
                        value["thread_states"] = {"error": str(error)}
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
                  "process_identity": self.identity, "identity_error": self.identity_error,
                  "thread_states_requested": self.thread_states,
                  "thread_states_scope": "Opt-in Darwin public thread scheduler states; handles are not unique IDs, samples can miss transitions; no wait reason or kernel stack attribution",
                  "task_counters_scope": "Darwin proc_taskinfo raw CPU/fault/thread counters, no wall-time conversion; omitted elsewhere",
                  "scope": "Current resident bytes, sampled externally; can miss short peaks; not retained heap, OS high-water RSS, or a bound. Instrumented launch only.",
                  "samples": samples}
        path.write_text(json.dumps(report, indent=2) + "\n")
        return {"report": str(path.resolve()), "samples": len(values), "stopped": report["stopped"],
                "sampled_resident_peak_bytes": max(values) if values else None}
