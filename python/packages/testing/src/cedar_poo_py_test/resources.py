"""Observe a native child process; semantic acceptance belongs to Lean/Rust."""

import argparse
import hashlib
import json
import math
import os
import platform
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from .process_stats import parse_stats


def _controlled_run(command, report, timeout_seconds):
    """Own one process session; drain it before a caller may restore build files."""
    interruption = None

    def interrupted(signum, _frame):
        nonlocal interruption
        if interruption is None:
            interruption = signum

    signals = (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)
    previous = {sig: signal.signal(sig, interrupted) for sig in signals}

    def group_states(pid):
        snapshot = subprocess.run(["ps", "-axo", "pgid=,stat="],
                                  capture_output=True, text=True, check=True)
        return [row.split()[1] for row in snapshot.stdout.splitlines()
                if len(row.split()) == 2 and row.split()[0] == str(pid)]

    started = time.monotonic()
    try:
        child = subprocess.Popen(command, stderr=report, start_new_session=True)
        while True:
            remaining = timeout_seconds - (time.monotonic() - started)
            # Inspect without reaping: even after natural parent exit its PID
            # remains reserved while we check/drain any background descendants.
            exited = os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
            leftover = exited is not None and any(not state.startswith("Z") for state in group_states(child.pid))
            if interruption is not None or remaining <= 0 or leftover:
                # Do not reap the session leader during the grace period: its
                # reserved PID prevents a recycled PID/group from being signalled.
                signal_events = []
                for sig in (signal.SIGTERM, signal.SIGKILL):
                    try:
                        os.killpg(child.pid, sig)
                        signal_events.append({"signal": sig.name, "outcome": "delivered"})
                    except ProcessLookupError:
                        signal_events.append({"signal": sig.name, "outcome": "group_absent"})
                    except PermissionError:
                        # Darwin may reject signalling a group containing only
                        # corpses. Confirm no live member rather than swallowing
                        # permission errors for a protected/running process.
                        states = group_states(child.pid)
                        if any(not state.startswith("Z") for state in states):
                            raise
                        signal_events.append({"signal": sig.name, "outcome": "no_live_member", "states": states})
                    if sig == signal.SIGTERM:
                        time.sleep(3)
                command_returncode = child.wait()
                if interruption is not None:
                    reason, status = f"signal:{signal.Signals(interruption).name}", 128 + interruption
                elif leftover:
                    reason, status = "leftover_group", 125
                else:
                    reason, status = "deadline", 124
                return subprocess.CompletedProcess(command, status), {
                    "termination_reason": reason, "command_returncode": command_returncode,
                    "resource_observation_complete": False, "owned_group_quiesced": True,
                    "timeout_seconds": timeout_seconds, "termination_signals": signal_events,
                }
            if exited is not None:
                child.wait()
                return child, {
                    "termination_reason": None, "resource_observation_complete": True,
                    "owned_group_quiesced": True, "timeout_seconds": timeout_seconds,
                }
            time.sleep(min(remaining, 0.05))
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=float, help="own a bounded process session, with a fixed 3-second termination grace")
    parser.add_argument("executable", type=Path)
    parser.add_argument("arguments", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.timeout_seconds is not None and (not math.isfinite(args.timeout_seconds) or args.timeout_seconds <= 0):
        parser.error("timeout-seconds must be finite and positive")
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
        command = ["/usr/bin/time", "-l" if system == "Darwin" else "-v", str(executable), *args.arguments]
        supervision = {}
        if args.timeout_seconds is None:
            # Keep the existing ordinary measurement path unchanged.
            child = subprocess.run(command, stderr=report, check=False)
        else:
            child, supervision = _controlled_run(command, report, args.timeout_seconds)
        elapsed = time.monotonic_ns() - started
        report.seek(0)
        statistics = report.read()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    report_path = args.output.with_suffix(".stderr.txt")
    report_path.write_text(statistics)
    try:
        observed = parse_stats(statistics, system)
    except ValueError as error:
        if not supervision:
            sys.stderr.write(statistics)
            raise SystemExit(child.returncode or str(error)) from error
        # A terminated time observer may have no final counters. Preserve unknown
        # data and a failed observation; never fabricate zero measurements.
        supervision["resource_observation_complete"] = False
        observed = {"resource_observation_error": str(error)}
        if child.returncode == 0:
            child = subprocess.CompletedProcess(command, 125)
    receipt = {
        "format": "cedar-poo-native-process-v1", "system": system,
        "architecture": platform.machine(), "executable": str(executable),
        "executable_sha256": digest.hexdigest(), "arguments": args.arguments,
        "elapsed_ns": elapsed, "stderr_report": str(report_path.resolve()), **observed,
        "returncode": child.returncode, **supervision,
        "scope": "OS process high-water RSS including native startup; not retained heap or an RSS bound",
    }
    args.output.write_text(json.dumps(receipt, sort_keys=True) + "\n")
    print("NATIVE-RESOURCE " + json.dumps(receipt, sort_keys=True), file=sys.stderr)
    if child.returncode:
        sys.stderr.write(statistics)
    raise SystemExit(child.returncode)


if __name__ == "__main__":
    main()
