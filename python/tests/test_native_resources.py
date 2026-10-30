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
