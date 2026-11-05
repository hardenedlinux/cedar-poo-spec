"""Boundary tests for the Rust process bridge."""

from pathlib import Path
import tempfile
import unittest

from cedar_poo_py_test.process import BridgeError, RustBridge


class RustBridgeTests(unittest.TestCase):
    def test_preserves_input_and_output_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "request.json"
            output = root / "receipt.json"
            payload = b'{"unicode":"\xe4\xb8\xad"}\n'
            source.write_bytes(payload)
            bridge = RustBridge(root, ("python", "-c", "import sys; sys.stdout.buffer.write(sys.stdin.buffer.read())"))
            self.assertEqual(bridge.run(input_file=source, output_file=output), payload)
            self.assertEqual(output.read_bytes(), payload)

    def test_failed_process_cannot_write_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "receipt.json"
            bridge = RustBridge(root, ("python", "-c", "import sys; sys.stderr.write('failed'); sys.exit(7)"))
            with self.assertRaisesRegex(BridgeError, r"failed \(7\): failed"):
                bridge.run("replay-validated-receipts", output_file=output)
            self.assertFalse(output.exists())
