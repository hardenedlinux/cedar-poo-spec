import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from types import SimpleNamespace
import ctypes
import threading

from cedar_poo_py_test import process_memory

from cedar_poo_py_test.process_memory import ProcessMemory, TaskInfo, RUsageInfoV0, resident_bytes, process_snapshot, process_identity


class ProcessMemoryTests(unittest.TestCase):
    def test_native_layout_and_own_process(self):
        import ctypes
        self.assertEqual(ctypes.sizeof(TaskInfo), 96)
        self.assertEqual(ctypes.sizeof(RUsageInfoV0), 96)
        self.assertGreater(resident_bytes(os.getpid()), 0)

    def test_darwin_thread_states_use_public_handle_abi(self):
        self.assertEqual(ctypes.sizeof(process_memory.ThreadInfo), 112)
        def read(pid, flavor, handle, pointer, size):
            self.assertEqual(pid, 123)
            if flavor == 6:
                self.assertEqual((handle, size), (0, 512))
                ctypes.cast(pointer, ctypes.POINTER(ctypes.c_uint64))[0] = 456
                return 8
            self.assertEqual((flavor, handle, size), (5, 456, 112))
            value = ctypes.cast(pointer, ctypes.POINTER(process_memory.ThreadInfo)).contents
            value.run_state, value.user_time, value.system_time = 4, 17, 19
            return size
        with patch.object(process_memory, "SYSTEM", "Darwin"), patch.object(
                process_memory, "LIBPROC", SimpleNamespace(proc_pidinfo=read), create=True):
            result = process_memory.thread_snapshot(123)
        self.assertFalse(result["possibly_truncated"])
        self.assertEqual(result["records"][0]["run_state"], 4)
        self.assertEqual(result["records"][0]["system_time_raw"], 19)

    def test_full_thread_buffer_is_reported_as_possibly_truncated(self):
        def read(pid, flavor, handle, pointer, size):
            return size
        with patch.object(process_memory, "SYSTEM", "Darwin"), patch.object(
                process_memory, "LIBPROC", SimpleNamespace(proc_pidinfo=read), create=True):
            result = process_memory.thread_snapshot(123)
        self.assertTrue(result["possibly_truncated"])
        self.assertEqual(len(result["records"]), 64)

    def test_darwin_thread_short_list_and_exited_thread_are_explicit(self):
        for returned in (0, 7, 513):
            with patch.object(process_memory, "SYSTEM", "Darwin"), patch.object(
                    process_memory, "LIBPROC", SimpleNamespace(proc_pidinfo=lambda *args: returned), create=True):
                with self.assertRaisesRegex(OSError, "incomplete thread handle list"):
                    process_memory.thread_snapshot(123)
        def read(pid, flavor, handle, pointer, size):
            return 8 if flavor == 6 else 0
        with patch.object(process_memory, "SYSTEM", "Darwin"), patch.object(
                process_memory, "LIBPROC", SimpleNamespace(proc_pidinfo=read), create=True):
            result = process_memory.thread_snapshot(123)
        self.assertEqual(result["records"][0]["error"], "incomplete thread info")

    def test_darwin_complete_task_counters_keep_raw_units(self):
        def read(pid, flavor, offset, pointer, size):
            self.assertEqual((pid, flavor, offset, size), (123, 4, 0, 96))
            value = ctypes.cast(pointer, ctypes.POINTER(TaskInfo)).contents
            value.virtual, value.resident = 10000, 500
            value.times[0], value.times[1] = 17, 19
            for i in range(12):
                value.statistics[i] = 100 + i
            return size

        with patch.object(process_memory, "SYSTEM", "Darwin"), patch.object(
                process_memory, "LIBPROC", SimpleNamespace(proc_pidinfo=read), create=True):
            self.assertEqual(process_snapshot(123), {
                "resident_bytes": 500, "virtual_bytes": 10000,
                "total_user_time_raw": 17, "total_system_time_raw": 19,
                "faults": 101, "pageins": 102, "cow_faults": 103,
                "context_switches": 108, "threads": 109, "running_threads": 110,
            })

    def test_darwin_short_task_read_is_not_zero_counters(self):
        with patch.object(process_memory, "SYSTEM", "Darwin"), patch.object(
                process_memory, "LIBPROC", SimpleNamespace(proc_pidinfo=lambda *args: 48), create=True):
            with self.assertRaisesRegex(OSError, "complete task info"):
                process_snapshot(123)

    def test_darwin_kernel_identity_uses_public_uuid_and_start_fields(self):
        def usage(pid, version, pointer):
            self.assertEqual((pid, version), (123, 0))
            info = ctypes.cast(pointer, ctypes.POINTER(RUsageInfoV0)).contents
            info.image_uuid[:] = range(16)
            info.values[8] = 987654
            return 0

        def path(pid, pointer, size):
            self.assertEqual((pid, size), (123, 4096))
            data = b"/owned/native\0"
            ctypes.memmove(pointer, data, len(data))
            return len(data) - 1

        with patch.object(process_memory, "SYSTEM", "Darwin"), patch.object(
                process_memory, "LIBPROC", SimpleNamespace(proc_pid_rusage=usage, proc_pidpath=path), create=True):
            result = process_identity(123)
        self.assertEqual(result["image_uuid"], "00010203-0405-0607-0809-0A0B0C0D0E0F")
        self.assertEqual(result["path"], "/owned/native")
        self.assertEqual(result["process_start_abstime"], 987654)

    def test_darwin_identity_read_failure_stays_unavailable(self):
        with patch.object(process_memory, "SYSTEM", "Darwin"), patch.object(
                process_memory, "LIBPROC", SimpleNamespace(proc_pid_rusage=lambda *args: -1), create=True):
            with self.assertRaisesRegex(OSError, "identity unavailable"):
                process_identity(123)

    def test_owned_child_observer_stops_before_receipt(self):
        child = subprocess.Popen([sys.executable, "-c", "print('ready', flush=True); input()"],
                                 stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        try:
            self.assertEqual(child.stdout.readline().strip(), "ready")
            memory = ProcessMemory(child)
            deadline = time.monotonic() + 1
            while not memory.samples and time.monotonic() < deadline:
                time.sleep(0.005)
            with tempfile.TemporaryDirectory() as directory:
                receipt = memory.finish(Path(directory) / "memory.json")
            self.assertTrue(receipt["stopped"])
            self.assertGreater(receipt["samples"], 0)
        finally:
            child.communicate("\n", timeout=5)

    def test_identity_read_does_not_block_deadline_supervisor_creation(self):
        child = subprocess.Popen([sys.executable, "-c", "input()"], stdin=subprocess.PIPE, text=True)
        returned, entered, release = threading.Event(), threading.Event(), threading.Event()

        def identity(pid):
            entered.set()
            release.wait(timeout=1)
            return {"pid": pid, "constructor_returned": returned.is_set()}

        try:
            with patch.object(process_memory, "process_identity", identity):
                memory = ProcessMemory(child)
                returned.set()
                self.assertTrue(entered.wait(timeout=1))
                release.set()
                deadline = time.monotonic() + 1
                while memory.identity is None and time.monotonic() < deadline:
                    time.sleep(0.005)
                with tempfile.TemporaryDirectory() as directory:
                    receipt = memory.finish(Path(directory) / "memory.json")
                self.assertTrue(receipt["stopped"])
                self.assertTrue(memory.identity["constructor_returned"])
        finally:
            release.set()
            child.communicate("\n", timeout=5)

    def test_exited_child_is_not_a_zero_memory_success(self):
        child = subprocess.Popen([sys.executable, "-c", "pass"])
        child.wait(timeout=5)
        with self.assertRaises(OSError):
            resident_bytes(child.pid)
