"""Observe a native child process; semantic acceptance belongs to Lean/Rust."""

import argparse
import hashlib
import json
import platform
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("executable", type=Path)
    parser.add_argument("arguments", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    executable = args.executable.resolve(strict=True)
    system = platform.system()
    if system not in ("Darwin", "Linux"):
        parser.error(f"unsupported resource observation platform: {system}")
    digest = hashlib.sha256()
    with executable.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    with tempfile.TemporaryFile(mode="w+") as report:
        started = time.monotonic_ns()
        child = subprocess.run(
            ["/usr/bin/time", "-l" if system == "Darwin" else "-v", str(executable), *args.arguments],
            stderr=report, check=False,
        )
        elapsed = time.monotonic_ns() - started
        report.seek(0)
        statistics = report.read()
    pattern = (r"^\s*(\d+)\s+maximum resident set size\s*$" if system == "Darwin"
               else r"^\s*Maximum resident set size \(kbytes\):\s*(\d+)\s*$")
    match = re.search(pattern, statistics, re.MULTILINE)
    if match is None:
        sys.stderr.write(statistics)
        raise SystemExit(child.returncode or "native process RSS observation unavailable")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    receipt = {
        "format": "cedar-poo-native-process-v1", "system": system,
        "architecture": platform.machine(), "executable": str(executable),
        "executable_sha256": digest.hexdigest(), "arguments": args.arguments,
        "elapsed_ns": elapsed, "peak_rss_bytes": int(match[1]) * (1 if system == "Darwin" else 1024),
        "returncode": child.returncode,
        "scope": "OS process high-water RSS including native startup; not retained heap or an RSS bound",
    }
    args.output.write_text(json.dumps(receipt, sort_keys=True) + "\n")
    print("NATIVE-RESOURCE " + json.dumps(receipt, sort_keys=True), file=sys.stderr)
    if child.returncode:
        sys.stderr.write(statistics)
    raise SystemExit(child.returncode)


if __name__ == "__main__":
    main()
