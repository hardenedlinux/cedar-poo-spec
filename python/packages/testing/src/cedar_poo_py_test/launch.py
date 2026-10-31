"""Observe real native main markers; diagnostic timing is not admission."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import resource
import subprocess
import tempfile
import time
from .clock_anchor import clock_anchor


def observations(stderr: bytes):
    for line in stderr.splitlines():
        try:
            value = json.loads(line)
        except (ValueError, UnicodeError):
            continue
        if isinstance(value, dict):
            yield value


def events(stderr: bytes, pid: int, exit_code: int, expected_exit: int = 1) -> tuple[dict, dict]:
    markers = [value for value in observations(stderr)
               if value.get("observation") in ("native-main-entry", "native-main-return")]
    if (len(markers) != 2 or markers[0].get("observation") != "native-main-entry"
            or markers[1].get("observation") != "native-main-return"
            or markers[0].get("pid") != pid or markers[1].get("success") is not (expected_exit == 0)
            or exit_code != expected_exit):
        raise ValueError("incomplete launch protocol or unexpected diagnostic exit")
    return markers[0], markers[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("executable", type=Path)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--materialization", choices=("copy", "hardlink"), default="copy",
                        help="Fresh inode control, or same-inode/new-path diagnostic")
    parser.add_argument("--input", type=Path)
    parser.add_argument("--expected-exit", type=int, choices=(0, 1), default=1)
    parser.add_argument("--child-arguments", nargs=argparse.REMAINDER, default=[])
    args = parser.parse_args()
    payload = args.input.read_bytes() if args.input else b"{}"
    source = args.executable.resolve(strict=True)
    args.output_directory.mkdir(parents=True, exist_ok=False)
    records = []
    with tempfile.TemporaryDirectory(prefix="cedar-launch-", dir=args.output_directory) as cohort_root:
        for cohort in (1, 2):
            executable = Path(cohort_root) / f"probe-{cohort}"
            if args.materialization == "copy":
                shutil.copyfile(source, executable)
                executable.chmod(0o755)
            else:
                os.link(source, executable)
            digest = hashlib.sha256(executable.read_bytes()).hexdigest()
            for trial in (1, 2, 3):
                stdout_path = args.output_directory / f"cohort-{cohort}-trial-{trial}.stdout"
                report_path = args.output_directory / f"cohort-{cohort}-trial-{trial}.stderr.txt"
                usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
                with tempfile.TemporaryFile() as input_file, stdout_path.open("wb") as output:
                    input_file.write(payload)
                    input_file.seek(0)
                    anchor = clock_anchor()
                    wall_start = time.time_ns()
                    mono_start = time.monotonic_ns()
                    child = subprocess.Popen([str(executable.resolve()), *args.child_arguments], stdin=input_file,
                                             stdout=output, stderr=subprocess.PIPE)
                    created = time.monotonic_ns()
                    try:
                        _, stderr = child.communicate(timeout=120)
                    except subprocess.TimeoutExpired:
                        child.kill()
                        _, stderr = child.communicate()
                        report_path.write_bytes(stderr)
                        raise
                    mono_end = time.monotonic_ns()
                    wall_end = time.time_ns()
                usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
                usage = {name: getattr(usage_after, name) - getattr(usage_before, name)
                         for name in ("ru_utime", "ru_stime", "ru_minflt", "ru_majflt", "ru_nvcsw", "ru_nivcsw", "ru_inblock", "ru_oublock")}
                report_path.write_bytes(stderr)
                entry, returned = events(stderr, child.pid, child.returncode, args.expected_exit)
                record = {"observation": "native-launch-diagnostic", "cohort": cohort, "trial": trial,
                          "materialization": args.materialization,
                          "source_file_identity": [source.stat().st_dev, source.stat().st_ino],
                          "execution_file_identity": [executable.stat().st_dev, executable.stat().st_ino],
                          "stderr_report": str(report_path.resolve()), "stdout": str(stdout_path.resolve()),
                          "stdout_sha256": hashlib.sha256(stdout_path.read_bytes()).hexdigest(),
                          "phases": [value for value in observations(stderr) if value.get("observation") == "native-phase"],
                          "child_rusage_delta": usage, "input_sha256": hashlib.sha256(payload).hexdigest(),
                          "arguments": args.child_arguments, "pid": child.pid, "executable_sha256": digest, "returncode": child.returncode,
                          "clock_anchor": anchor, "wall_start_ns": wall_start, "monotonic_start_ns": mono_start,
                          "spawn_ns": created-mono_start, "before_main_ns": entry["unix_ns"]-wall_start,
                          "import_initialization_ns": entry.get("import_initialization_ns"),
                          "main_span_ns": returned["elapsed_ns"], "process_ns": mono_end-mono_start,
                          "clock_disagreement_ns": (wall_end-wall_start)-(mono_end-mono_start),
                          "clock_interval_valid": wall_start <= entry["unix_ns"] <= returned["unix_ns"] <= wall_end,
                          "scope": "instrumented launch cohort; input and exit bound; not ordinary latency or admission"}
                records.append(record)
                (args.output_directory / "main-entry.json").write_text(json.dumps(records, indent=2) + "\n")
                print(json.dumps(record, sort_keys=True), flush=True)
    (args.output_directory / "main-entry.json").write_text(json.dumps(records, indent=2) + "\n")


if __name__ == "__main__":
    main()
