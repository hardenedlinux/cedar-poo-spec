"""Run schema-bound manifest checks and Rust receipt replays."""

from pathlib import Path
import subprocess

from cedar_poo_py_test.process import RustBridge


SCENARIOS = (
    "scope-pattern-validated",
    "namespaced-enum-validated",
    "agent-data-flow-validated",
    "network-validated",
    "country-approval-validated",
)


def check_schema_bound(repository: Path) -> None:
    repository = repository.resolve()
    bridge = RustBridge(repository)
    for name in SCENARIOS:
        manifest = Path(".lake/build") / f"{name}-manifest.json"
        receipts = Path(".lake/build") / f"{name}-receipts.json"
        subprocess.run(
            ["jq", "-e", "-f", f"Tests/Conformance/{name}-manifest.jq", str(manifest)],
            cwd=repository, stdout=subprocess.DEVNULL, check=True,
        )
        bridge.run(
            "replay-validated-receipts",
            input_file=repository / manifest,
            output_file=repository / receipts,
        )
        subprocess.run(
            ["jq", "-e", "-f", f"Tests/Conformance/{name}-receipts.jq", str(receipts)],
            cwd=repository, stdout=subprocess.DEVNULL, check=True,
        )
    subprocess.run(
        ["jq", "-e", "-f", "Tests/Conformance/agent-data-flow-validated-receipts-dispatch.jq",
         ".lake/build/agent-data-flow-validated-receipts.json"],
        cwd=repository, stdout=subprocess.DEVNULL, check=True,
    )
