"""Observe diagnostic Rust main markers; expected rejection is not admission."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


def events(stderr: bytes, pid: int, exit_code: int) -> tuple[dict, dict]:
    markers = []
    for line in stderr.splitlines():
        try:
            value = json.loads(line)
        except (ValueError, UnicodeError):
            continue
        if isinstance(value, dict) and value.get("observation") in ("native-main-entry", "native-main-return"):
            markers.append(value)
    if (len(markers) != 2 or markers[0].get("observation") != "native-main-entry"
            or markers[1].get("observation") != "native-main-return"
            or markers[0].get("pid") != pid or markers[1].get("success") is not False
            or exit_code != 1):
        raise ValueError("incomplete launch protocol or unexpected diagnostic exit")
    return markers[0], markers[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("executable", type=Path)
    parser.add_argument("--output-directory", type=Path, required=True)
    args = parser.parse_args()
    source = args.executable.resolve(strict=True)
    args.output_directory.mkdir(parents=True, exist_ok=True)
    records = []
    with tempfile.TemporaryDirectory(prefix="cedar-launch-", dir=args.output_directory) as cohort_root:
        for cohort in (1, 2):
            executable = Path(cohort_root) / f"probe-{cohort}"
            shutil.copyfile(source, executable)
            executable.chmod(0o755)
            digest = hashlib.sha256(executable.read_bytes()).hexdigest()
            for trial in (1, 2, 3):
                with tempfile.TemporaryFile() as input_file, tempfile.TemporaryFile() as output:
                    input_file.write(b"{}")
                    input_file.seek(0)
                    wall_start = time.time_ns()
                    mono_start = time.monotonic_ns()
                    child = subprocess.Popen([str(executable.resolve())], stdin=input_file,
                                             stdout=output, stderr=subprocess.PIPE)
                    created = time.monotonic_ns()
                    try:
                        _, stderr = child.communicate(timeout=120)
                    except subprocess.TimeoutExpired:
                        child.kill()
                        child.communicate()
                        raise
                    mono_end = time.monotonic_ns()
                    wall_end = time.time_ns()
                entry, returned = events(stderr, child.pid, child.returncode)
                record = {"observation": "native-launch-diagnostic", "cohort": cohort, "trial": trial,
                          "pid": child.pid, "executable_sha256": digest, "returncode": child.returncode,
                          "spawn_ns": created-mono_start, "before_main_ns": entry["unix_ns"]-wall_start,
                          "main_span_ns": returned["elapsed_ns"], "process_ns": mono_end-mono_start,
                          "clock_disagreement_ns": (wall_end-wall_start)-(mono_end-mono_start),
                          "clock_interval_valid": wall_start <= entry["unix_ns"] <= returned["unix_ns"] <= wall_end,
                          "scope": "diagnostic rejected empty manifest; instrumented cohort, not ordinary latency or admission"}
                records.append(record)
                print(json.dumps(record, sort_keys=True), flush=True)
    (args.output_directory / "main-entry.json").write_text(json.dumps(records, indent=2) + "\n")


if __name__ == "__main__":
    main()
