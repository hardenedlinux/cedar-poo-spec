import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

from cedar_poo_py_test.process_memory import ProcessMemory, TaskInfo, resident_bytes


class ProcessMemoryTests(unittest.TestCase):
    def test_native_layout_and_own_process(self):
        import ctypes
        self.assertEqual(ctypes.sizeof(TaskInfo), 96)
        self.assertGreater(resident_bytes(os.getpid()), 0)

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

    def test_exited_child_is_not_a_zero_memory_success(self):
        child = subprocess.Popen([sys.executable, "-c", "pass"])
        child.wait(timeout=5)
        with self.assertRaises(OSError):
            resident_bytes(child.pid)
