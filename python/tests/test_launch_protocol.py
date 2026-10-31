"""Launch observations require actual entry/return/exit identity."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock
from cedar_poo_py_test.launch import events, StderrObservation, file_metadata


class LaunchProtocolTests(unittest.TestCase):
    def test_unavailable_xattrs_are_explicit_not_an_empty_success(self):
        with tempfile.NamedTemporaryFile() as source:
            with mock.patch("cedar_poo_py_test.launch.os.listxattr", create=True,
                            side_effect=AttributeError("unavailable platform API")):
                observed = file_metadata(Path(source.name))
            self.assertIn("xattrs_error", observed)
            self.assertNotIn("xattrs_sha256", observed)
            self.assertGreater(observed["inode"], 0)

    def test_stderr_arrival_before_exit_and_raw_final_fragment(self):
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / "stderr.txt"
            child = subprocess.Popen([sys.executable, "-c",
                "import os,sys; os.write(2,b'first\\n'); sys.stdin.read(1); os.write(2,b'\\xfflast')"],
                stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
            observer = StderrObservation(child.stderr, report)
            try:
                deadline = time.monotonic() + 2
                while not report.exists() or report.stat().st_size == 0:
                    if time.monotonic() >= deadline:
                        self.fail("stderr was not drained while the child awaited input")
                    time.sleep(0.005)
                self.assertIsNone(child.poll())
                self.assertEqual(report.read_bytes(), b"first\n")
                child.stdin.write(b"x")
                child.stdin.close()
                self.assertEqual(child.wait(timeout=2), 0)
            finally:
                if child.poll() is None:
                    child.kill()
                    child.wait()
                if not child.stdin.closed:
                    child.stdin.close()
                receipt = observer.finish()
            self.assertTrue(receipt["stopped"])
            self.assertEqual(report.read_bytes(), b"first\n\xfflast")
            data = json.loads(Path(receipt["report"]).read_text())
            self.assertLessEqual(data["reader_ready_unix_ns"], data["arrivals"][0]["unix_ns"])
            self.assertEqual([(r["offset"], r["bytes"]) for r in data["arrivals"]], [(0, 6), (6, 5)])
            self.assertLessEqual(data["arrivals"][0]["monotonic_ns"], data["arrivals"][1]["monotonic_ns"])

    def test_stderr_io_error_cannot_qualify_observation(self):
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / "invalid"
            report.mkdir()
            child = subprocess.Popen([sys.executable, "-c", "pass"], stderr=subprocess.PIPE)
            observer = StderrObservation(child.stderr, report)
            self.assertEqual(child.wait(timeout=2), 0)
            with self.assertRaisesRegex(RuntimeError, "incomplete stderr observation"):
                observer.finish()

    def packet(self, success=False, pid=7):
        return (json.dumps({"observation":"native-main-entry","pid":pid})+"\n"+
                json.dumps({"observation":"native-main-return","success":success})+"\nerror\n").encode()

    def test_expected_rejection_keeps_actual_exit(self):
        first, last = events(self.packet(), 7, 1)
        self.assertEqual(first["pid"], 7)
        self.assertFalse(last["success"])

    def test_missing_marker_cannot_qualify_a_launch(self):
        with self.assertRaises(ValueError):
            events(b"manifest error\n", 7, 1)

    def test_wrong_pid_or_exit_or_outcome_cannot_qualify(self):
        for packet, pid, code in ((self.packet(), 8, 1), (self.packet(), 7, 0), (self.packet(True), 7, 1)):
            with self.assertRaises(ValueError):
                events(packet, pid, code)

    def test_real_success_requires_explicit_success_protocol(self):
        events(self.packet(True), 7, 0, expected_exit=0)
        with self.assertRaises(ValueError):
            events(self.packet(False), 7, 0, expected_exit=0)
