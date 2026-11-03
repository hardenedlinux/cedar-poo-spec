"""Installed native-extension and wire parity checks; semantic decisions stay in Rust."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.machinery
import json
from pathlib import Path
import subprocess
import sys
import unittest

import cedar_poo_bridge
import cedar_poo_bridge._native as native

ROOT = Path(__file__).resolve().parents[2]
BRIDGE = ROOT / "rust/target/debug/cedar-poo-bridge"


class InstalledBindings(unittest.TestCase):
    def test_installed_module_is_a_binary_extension(self):
        path = Path(native.__file__).resolve()
        self.assertTrue(path.is_relative_to(Path(sys.prefix).resolve()))
        self.assertTrue(str(path).endswith(tuple(importlib.machinery.EXTENSION_SUFFIXES)))
        self.assertIs(cedar_poo_bridge.replay_receipts, native.replay_receipts)
        print("PYTHON-NATIVE-MODULE", sys.version.split()[0], hashlib.sha256(path.read_bytes()).hexdigest())

    def test_every_applicable_native_lean_entry_matches_original_rust_cli_bytes(self):
        catalog = json.loads((ROOT / ".lake/build/functional-catalog.json").read_bytes())["entries"]
        observed = {"raw": 0, "schema-bound": 0, "evolution": 0}
        for name, entry in catalog.items():
            if isinstance(entry, dict) and "manifest_kind" in entry:
                kind = entry["manifest_kind"]
                operation, function = {
                    "raw": ("replay-receipts", native.replay_receipts),
                    "schema-bound": ("replay-validated-receipts", native.replay_validated_receipts),
                }[kind]
            elif isinstance(entry, dict) and "before" in entry and "after" in entry:
                kind = "evolution"
                operation, function = "replay-schema-only-revision", native.replay_schema_only_revision
            else:
                # Artifact/data entries have no Python receipt API. Their original
                # full-catalog Rust conformance gate remains independent.
                continue
            with self.subTest(entry=name, kind=kind):
                payload = (ROOT / f".lake/build/{name}-manifest.json").read_bytes()
                expected = subprocess.run([str(BRIDGE), operation], input=payload,
                                          capture_output=True, check=True).stdout
                self.assertEqual(function(payload), expected)
                observed[kind] += 1
        self.assertTrue(all(observed.values()))
        print("PYTHON-NATIVE-PARITY", json.dumps(observed, sort_keys=True))

    def test_invalid_payloads_and_wrong_python_types_refuse(self):
        for function in (native.replay_receipts, native.replay_validated_receipts,
                         native.replay_schema_only_revision):
            for payload in (b"\xff", b"{}"):
                with self.subTest(function=function.__name__, payload=payload):
                    with self.assertRaises(ValueError):
                        function(payload)
            with self.assertRaises(TypeError):
                function("{}")

    def test_parallel_calls_preserve_receipt_bytes(self):
        payload = (ROOT / ".lake/build/agent-payment-manifest.json").read_bytes()
        expected = subprocess.run([str(BRIDGE), "replay-receipts"], input=payload,
                                  capture_output=True, check=True).stdout
        with ThreadPoolExecutor(max_workers=4) as pool:
            for result in pool.map(native.replay_receipts, [payload] * 4):
                self.assertEqual(result, expected)


if __name__ == "__main__":
    unittest.main(verbosity=2)
