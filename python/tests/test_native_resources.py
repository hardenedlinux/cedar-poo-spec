"""Native process receipts preserve execution identity and failed child exits."""
import json
import platform
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


@unittest.skipUnless(platform.system() in ("Darwin", "Linux"), "POSIX resource observer")
class NativeResourceTests(unittest.TestCase):
    def test_failed_child_remains_failed_with_an_observation_receipt(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "receipt.json"
            result = subprocess.run([
                sys.executable, "-m", "cedar_poo_py_test.resources", "--output", str(output),
                sys.executable, "-c", "print('CHILD-RAN'); raise SystemExit(7)",
            ], capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 7)
            self.assertIn("CHILD-RAN", result.stdout)
            receipt = json.loads(output.read_text())
            self.assertEqual(receipt["returncode"], 7)
            self.assertEqual(len(receipt["executable_sha256"]), 64)
            self.assertGreater(receipt["peak_rss_bytes"], 0)
            self.assertGreater(receipt["elapsed_ns"], 0)
            self.assertGreaterEqual(receipt["user_cpu_ns"], 0)
            self.assertGreaterEqual(receipt["system_cpu_ns"], 0)
            self.assertGreaterEqual(receipt["os_elapsed_ns"], 0)
            self.assertGreater(receipt["os_elapsed_resolution_ns"], 0)


class NativeStatsParsingTests(unittest.TestCase):
    def test_darwin_time_units_and_rounding(self):
        from cedar_poo_py_test.process_stats import parse_stats
        row = parse_stats("  0.42 real 0.31 user 0.10 sys\n  8192 maximum resident set size\n", "Darwin")
        self.assertEqual((row["os_elapsed_ns"], row["user_cpu_ns"], row["system_cpu_ns"]), (420_000_000, 310_000_000, 100_000_000))
        self.assertEqual(row["peak_rss_bytes"], 8192)
        self.assertEqual(row["os_elapsed_resolution_ns"], 10_000_000)

    def test_linux_time_units_and_minutes(self):
        from cedar_poo_py_test.process_stats import parse_stats
        row = parse_stats("User time (seconds): 0.31\nSystem time (seconds): 0.10\nElapsed (wall clock) time (h:mm:ss or m:ss): 1:02.53\nMaximum resident set size (kbytes): 8192\n", "Linux")
        self.assertEqual(row["os_elapsed_ns"], 62_530_000_000)
        self.assertEqual(row["peak_rss_bytes"], 8_388_608)
        self.assertEqual(row["os_elapsed_resolution_ns"], 10_000_000)

    def test_missing_os_evidence_does_not_become_zero(self):
        from cedar_poo_py_test.process_stats import parse_stats
        with self.assertRaises(ValueError):
            parse_stats("8192 maximum resident set size\n", "Darwin")
