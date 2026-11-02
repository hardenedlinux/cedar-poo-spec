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
import threading
import time
from .clock_anchor import clock_anchor
from .process_memory import ProcessMemory


def file_metadata(path: Path):
    stat = path.stat()
    result = {"device": stat.st_dev, "inode": stat.st_ino, "size": stat.st_size,
              "mtime_ns": stat.st_mtime_ns, "ctime_ns": stat.st_ctime_ns, "links": stat.st_nlink}
    try:
        result["xattrs_sha256"] = {name: hashlib.sha256(os.getxattr(path, name)).hexdigest()
                                   for name in os.listxattr(path)}
    except (OSError, AttributeError) as error:
        result["xattrs_error"] = str(error)
    return result


class StderrObservation:
    """Drain only the owned child's stderr and timestamp complete line arrivals.

    Arrival is an observer upper bound, not the child's write or syscall time.
    Preserve raw bytes independently, including non-UTF8 and a partial final line.
    """
    def __init__(self, pipe, report: Path):
        self.pipe, self.report = pipe, report
        self.arrivals, self.error = [], None
        self.started_ns = time.time_ns()
        self.ready_ns = None
        self.thread = threading.Thread(target=self._drain, daemon=True)
        self.thread.start()

    def _drain(self):
        try:
            with self.pipe, self.report.open("wb") as output:
                self.ready_ns = time.time_ns()
                offset = 0
                for line in iter(self.pipe.readline, b""):
                    self.arrivals.append({"offset": offset, "bytes": len(line),
                                          "unix_ns": time.time_ns(), "monotonic_ns": time.monotonic_ns()})
                    output.write(line)
                    output.flush()
                    offset += len(line)
        except Exception as error:
            self.error = str(error)

    def finish(self):
        self.thread.join(timeout=1)
        path = self.report.with_suffix(".arrivals.json")
        stopped = not self.thread.is_alive()
        path.write_text(json.dumps({"scope": "Owned stderr line arrival upper bounds; not child write timestamps",
                                    "started_unix_ns": self.started_ns, "stopped": stopped,
                                    "reader_ready_unix_ns": self.ready_ns,
                                    "error": self.error, "arrivals": self.arrivals}, indent=2) + "\n")
        if not stopped or self.error:
            raise RuntimeError("incomplete stderr observation; raw report retained")
        return {"report": str(path.resolve()), "lines": len(self.arrivals), "stopped": stopped}


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
    parser.add_argument("--thread-states", action="store_true",
                        help="Opt-in Darwin scheduler observation; not ordinary latency or a wait reason")
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
                metadata_before = file_metadata(executable)
                with tempfile.TemporaryFile() as input_file, stdout_path.open("wb") as output:
                    input_file.write(payload)
                    input_file.seek(0)
                    anchor = clock_anchor()
                    wall_start = time.time_ns()
                    mono_start = time.monotonic_ns()
                    child = subprocess.Popen([str(executable.resolve()), *args.child_arguments], stdin=input_file,
                                             stdout=output, stderr=subprocess.PIPE)
                    created = time.monotonic_ns()
                    memory = ProcessMemory(child, thread_states=args.thread_states)
                    stderr_observer = StderrObservation(child.stderr, report_path)
                    try:
                        try:
                            deadline = time.monotonic() + 120
                            # EOF wakes promptly at native exit, avoiding wait(timeout)'s
                            # polling granularity in the ordinary diagnostic lifetime.
                            stderr_observer.thread.join(timeout=120)
                            child.wait(timeout=max(0, deadline - time.monotonic()))
                        except subprocess.TimeoutExpired:
                            child.kill()
                            child.wait()
                            raise
                        mono_end = time.monotonic_ns()
                        wall_end = time.time_ns()
                    finally:
                        try:
                            memory_receipt = memory.finish(stdout_path.with_suffix(".memory.json"))
                        finally:
                            stderr_receipt = stderr_observer.finish()
                usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
                usage = {name: getattr(usage_after, name) - getattr(usage_before, name)
                         for name in ("ru_utime", "ru_stime", "ru_minflt", "ru_majflt", "ru_nvcsw", "ru_nivcsw", "ru_inblock", "ru_oublock")}
                stderr = report_path.read_bytes()
                entry, returned = events(stderr, child.pid, child.returncode, args.expected_exit)
                record = {"observation": "native-launch-diagnostic", "cohort": cohort, "trial": trial,
                          "materialization": args.materialization,
                          "source_file_identity": [source.stat().st_dev, source.stat().st_ino],
                          "execution_file_identity": [executable.stat().st_dev, executable.stat().st_ino],
                          "file_before": metadata_before, "file_after": file_metadata(executable),
                          "stderr_report": str(report_path.resolve()), "stdout": str(stdout_path.resolve()),
                          "stderr_observation": stderr_receipt,
                          "stdout_sha256": hashlib.sha256(stdout_path.read_bytes()).hexdigest(),
                          "phases": [value for value in observations(stderr) if value.get("observation") == "native-phase"],
                          "child_rusage_delta": usage, "input_sha256": hashlib.sha256(payload).hexdigest(),
                          "resident_observation": memory_receipt,
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
