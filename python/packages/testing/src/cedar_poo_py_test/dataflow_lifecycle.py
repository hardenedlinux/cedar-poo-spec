"""Record fixed native process pairs; Lean/Rust and existing conformance gates own semantics.

This driver only launches bounded processes, records artifacts/OS receipts and
compares complete wire bytes. It does not implement policy, admission, or resource
thresholds. Run after all builds/tests have stopped; preserve every observation.
"""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import tomllib

ROOT = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
BASE_COMMIT = "5ce4bd2c92cc79609221a9cad3a4c3af3893ce7f"
ROLES = {"bridge": "bridge", "profiles": "object-profiles", "functional": "functional-reuse", "producer": "case-manifests"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-commit", default=BASE_COMMIT, help="Exact declared baseline commit; frozen hashes and dependency pin are verified")
    parser.add_argument("--artifacts", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    artifacts, output = args.artifacts.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    records, pipelines, comparisons, profiles = [], [], [], []
    binaries = {variant: {role: artifacts / f"{variant}-{name}" for role, name in ROLES.items()}
                for variant in ("before", "after")}
    identities = {v: {k: {"path": str(p), "sha256": digest(p)} for k, p in d.items()} for v, d in binaries.items()}
    tracked = subprocess.check_output(["git", "ls-files"], cwd=ROOT, text=True).splitlines()
    source_suffixes = {".lean", ".py", ".rs", ".just", ".toml", ".lock", ".json", ".jq", ".cedar", ".sha256", ".yml", ".yaml"}
    source_files = [ROOT / name for name in tracked if not name.startswith("docs/") and
                    (Path(name).suffix in source_suffixes or Path(name).name in {"Justfile", "lean-toolchain"})]
    baseline = json.loads((artifacts / "baseline-identities.json").read_text())
    if not re.fullmatch(r"[0-9a-f]{40}", args.baseline_commit) or baseline["cedar_commit"] != args.baseline_commit:
        parser.error("Frozen baseline must match the explicit full baseline commit")
    configuration = subprocess.check_output(
        ["git", "show", f"{args.baseline_commit}:lakefile.toml"], cwd=ROOT, text=True)
    baseline_poo = next(p["rev"] for p in tomllib.loads(configuration)["require"] if p["name"] == "LeanPoo")
    if baseline["poo_revision"] != baseline_poo:
        parser.error("Frozen baseline POO identity differs from its committed dependency pin")
    for role, identity in identities["before"].items():
        if identity["sha256"] != baseline["executables"]["before-" + ROLES[role]]:
            parser.error(f"Frozen baseline artifact changed: {role}")
    # Both variants begin with newly materialized execution files. Reusing the
    # baseline path while re-copying only the candidate confounds code changes
    # with OS per-file/path startup state, even when the bytes are identical.
    artifact_sources = identities
    execution = output / "paired-executables"
    for variant, roles in binaries.items():
        directory = execution / variant
        directory.mkdir(parents=True)
        for role, source in list(roles.items()):
            target = directory / role
            shutil.copy2(source, target)
            if digest(target) != artifact_sources[variant][role]["sha256"]:
                parser.error(f"Execution file differs from frozen artifact: {variant}/{role}")
            roles[role] = target
    identities = {v: {k: {"path": str(p), "sha256": digest(p)} for k, p in d.items()}
                  for v, d in binaries.items()}
    source_identity = {str(p.relative_to(ROOT)): digest(p) for p in source_files}
    snapshot = hashlib.sha256(json.dumps(source_identity, sort_keys=True).encode()).hexdigest()

    def save():
        report = {"format": "cedar-poo-dataflow-lifecycle-v1", "baseline_commit": args.baseline_commit, "baseline_provenance": baseline,
                  "poo_revision": next(p["rev"] for p in json.loads((ROOT / "lake-manifest.json").read_text())["packages"] if p["name"] == "LeanPoo"),
                  "source_snapshot_sha256": snapshot, "source_inputs": source_identity,
                  "binaries": identities, "artifact_sources": artifact_sources,
                  "paired_file_lifecycle": "Both variants copied once into new execution paths before any measured child; byte identities verified. Each variant then reuses its own files across the fixed pairs.",
                  "process_limit_seconds": 120, "kill_after_seconds": 3,
                  "scope": "Sequential native producer -> artifact -> Rust consumer; full child lifetime. No task-owned builds/tests overlap this cohort. Host scheduling and scan caches are not controlled.",
                  "measurement": "OS RSS is a process high-water mark. Pipeline CPU is the sum of sequential children; pipeline peak RSS is their maximum, not a sum or a proven memory bound. Lean heartbeat deltas count small allocations, not bytes.",
                  "records": records, "pipelines": pipelines, "wire_comparisons": comparisons}
        (output / "receipt.json").write_text(json.dumps(report, indent=2) + "\n")
        if profiles:
            with (output / "object-observations.csv").open("w", newline="") as target:
                writer = csv.DictWriter(target, fieldnames=list(profiles[0]))
                writer.writeheader()
                writer.writerows(profiles)

    def observe(tag, variant, role, argv=(), stdin=None, executable=None):
        stdout, stderr, resource = [output / f"{tag}.{suffix}" for suffix in ("stdout", "stderr", "resource.json")]
        executable = executable or binaries[variant][role]
        command = ["timeout", "--signal=TERM", "--kill-after=3s", "120s", sys.executable,
                   "-m", "cedar_poo_py_test.resources", "--output", str(resource), str(executable), *argv]
        started = time.monotonic_ns()
        with stdout.open("wb") as out, stderr.open("wb") as err:
            if stdin is None:
                run = subprocess.run(command, cwd=ROOT, stdout=out, stderr=err)
            else:
                with stdin.open("rb") as source:
                    run = subprocess.run(command, cwd=ROOT, stdin=source, stdout=out, stderr=err)
        record = {"tag": tag, "variant": variant, "role": role, "arguments": list(argv),
                  "supervised_elapsed_ns": time.monotonic_ns() - started, "returncode": run.returncode,
                  "stdout": str(stdout.relative_to(output)), "stdout_sha256": digest(stdout),
                  "stderr": str(stderr.relative_to(output)), "resource": json.loads(resource.read_text()) if resource.exists() else None}
        records.append(record)
        save()
        print(json.dumps({k: record[k] for k in ("tag", "returncode", "supervised_elapsed_ns")}), flush=True)
        if run.returncode:
            raise SystemExit(f"Native process failed; retained {stderr}")
        if role == "profiles":
            for line in stdout.read_text().splitlines():
                if line.startswith("PROFILE-PREP "):
                    profiles.append({"process": tag, "variant": variant, **dict(re.findall(r"(\w+)=([^ ]+)", line))})
        if role == "bridge" and argv == ("benchmark-catalog",):
            subprocess.run(["jq", "-e", "-f", "Tests/Conformance/native-catalog-benchmark.jq", str(stdout)],
                           cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
        save()
        return stdout, record

    def compare(name, first, second):
        run = subprocess.run(["cmp", str(first), str(second)], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        comparisons.append({"name": name, "first_sha256": digest(first), "second_sha256": digest(second), "returncode": run.returncode})
        save()
        if run.returncode:
            raise SystemExit(f"Wire bytes changed: {name}; semantic acceptance remains with Rust/Lean")

    expected = {"after": ROOT / ".lake/build/functional-catalog.json",
                "before": artifacts / "before-catalog.json"}
    if not expected["before"].exists():
        expected["before"] = expected["after"]
    if expected["before"] != expected["after"] and digest(expected["before"]) != baseline.get("catalog_sha256"):
        parser.error("Declared baseline wire golden changed")
    # Bulk wire changes are declared in the frozen baseline. Each producer must
    # match its own complete wire golden; full consumer receipts still compare.

    for pair in (1, 2, 3):
        order = ("after", "before") if pair == 2 else ("before", "after")
        receipts = {}
        for variant in order:
            tag = f"pair-{pair}-{variant}"
            observe(tag + "-objects", variant, "profiles")
            observe(tag + "-functional", variant, "functional", ("CrossAgentGoverned",))
            observe(tag + "-roots", variant, "functional", ("--root-scale",))
            catalog, producer = observe(tag + "-catalog", variant, "producer", ("catalog",))
            compare(tag + "-catalog-vs-declared-wire", catalog, expected[variant])
            replay, consumer = observe(tag + "-replay", variant, "bridge", ("replay-catalog",), catalog)
            receipts[variant] = replay
            children = [producer["resource"], consumer["resource"]]
            pipelines.append({"pair": pair, "variant": variant, "children": [producer["tag"], consumer["tag"]],
                              "child_elapsed_ns": sum(x["elapsed_ns"] for x in children),
                              "cpu_ns": sum(x["user_cpu_ns"] + x["system_cpu_ns"] for x in children),
                              "peak_child_rss_bytes": max(x["peak_rss_bytes"] for x in children)})
            observe(tag + "-benchmark", variant, "bridge", ("benchmark-catalog",), catalog)
        compare(f"pair-{pair}-complete-replay", receipts["before"], receipts["after"])
    for variant in ("before", "after"):
        fresh = output / f"fresh-{variant}"
        fresh.mkdir()
        producer, bridge = [fresh / x for x in ("producer", "bridge")]
        shutil.copy2(binaries[variant]["producer"], producer)
        shutil.copy2(binaries[variant]["bridge"], bridge)
        for stage in ("fresh", "repeated-1", "repeated-2"):
            tag = f"file-cohort-{variant}-{stage}"
            catalog, _ = observe(tag + "-catalog", variant, "producer", ("catalog",), executable=producer)
            compare(tag + "-catalog", catalog, expected[variant])
            observe(tag + "-benchmark", variant, "bridge", ("benchmark-catalog",), catalog, executable=bridge)
    save()
    print(f"DATAFLOW-LIFECYCLE-OK {len(records)} native child processes; all wire bytes retained; {output / 'receipt.json'}", flush=True)


if __name__ == "__main__":
    main()
