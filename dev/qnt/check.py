"""Check the POO-derived finite threat model; retain separate evidence receipts."""
from pathlib import Path
import hashlib
import json
import subprocess
import tempfile
import shutil

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / ".lake/build/wallet-threat"
QUINT = ROOT / "dev/node_modules/.bin/quint"
MODEL = "dev/qnt/financial/WalletSigning.qnt"
CASE = ".lake/build/wallet-attackers-case.qnt"
CONTAINMENT = "dev/qnt/financial/WalletContainment.qnt"
HOST = "dev/qnt/financial/WalletHost.qnt"


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    receipt = {"status": "running", "checks": []}
    receipt_path = OUT / "receipt.json"

    def save() -> None:
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")

    save()  # A failed rerun must never leave an earlier passing receipt current.
    if not QUINT.is_file():
        raise SystemExit("Install the declared dev dependencies with bun install --frozen-lockfile --ignore-scripts")
    version = subprocess.check_output([str(QUINT), "--version"], cwd=ROOT, text=True).strip()
    if version != "0.33.0":
        raise SystemExit(f"Expected pinned Quint 0.33.0, got {version}")
    receipt.update(checkout=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(), quint=version, apalache="0.62.1", seed=7, positive_depth=12, negative_depth=4)
    inputs = [MODEL, CONTAINMENT, HOST, "CedarPooSpec/Vertical/FinancialServices/PaymentHost.lean",
              "Tests/Enterprise/Payment/WalletHost.lean", "Examples/Scenarios/FinancialServices/Wallet/Binance2026Host.lean", "CedarPooSpec/Vertical/FinancialServices/PaymentContainment.lean",
              "Tests/Enterprise/Payment/WalletContainment.lean", ".lake/build/binance-2026-metadata.json",
              "CedarPooSpec/Scenarios/Metadata.lean", "CedarPooSpec/Scenarios/Functional.lean", "dev/qnt/attackers/Capabilities.qnt", CASE,
              "CedarPooSpec/Attackers/Trace.lean", "CedarPooSpec/Attackers/ProfileObject.lean",
              "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean",
              "CedarPooSpec/Vertical/FinancialServices/PaymentOperation.lean",
              "Examples/Scenarios/FinancialServices/Wallet/Base.lean",
              "Examples/Scenarios/FinancialServices/Wallet/Binance2026.lean",
              "Examples/Scenarios/FinancialServices/Wallet/Binance2026Export.lean",
              "Tests/Enterprise/Payment/WalletSigning.lean", "Tests/Attackers/ProfileObject.lean",
              "dev/qnt/check.py", "dev/package.json", "dev/bun.lock"]
    receipt["inputs"] = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in inputs}

    receipt["scenario"] = json.loads((ROOT / ".lake/build/binance-2026-metadata.json").read_text())

    def run(label: str, args: list[str], expected: int = 0) -> None:
        log = OUT / f"{label}.log"
        command_args = [str(ROOT / arg) if arg in (MODEL, CASE, CONTAINMENT, HOST) else arg for arg in args]
        command = ["timeout", "--signal=TERM", "--kill-after=3s", "120s", str(QUINT), *command_args]
        with log.open("w") as stream:
            result = subprocess.run(command, cwd=OUT, stdout=stream, stderr=subprocess.STDOUT, check=False)
        receipt["checks"].append({"name": label, "command": args, "exit": result.returncode,
                                  "expected_exit": expected, "log": str(log.relative_to(ROOT))})
        save()
        if result.returncode != expected:
            receipt["status"] = "failed"
            save()
            raise SystemExit(f"{label}: exit {result.returncode}, expected {expected}; see {log}")
        print(f"{label}: expected exit {expected}", flush=True)

    run("typecheck", ["typecheck", MODEL])
    with tempfile.TemporaryDirectory(prefix="source-only-", dir=OUT) as isolated:
        for source in (MODEL, CONTAINMENT, HOST, "dev/qnt/attackers/Capabilities.qnt"):
            target = Path(isolated) / source
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / source, target)
        run("source-only-typecheck", ["typecheck", str(Path(isolated) / MODEL)])
        run("containment-source-only-typecheck", ["typecheck", str(Path(isolated) / CONTAINMENT)])
        run("host-source-only-typecheck", ["typecheck", str(Path(isolated) / HOST)])
    run("case-typecheck", ["typecheck", CASE])
    run("traces", ["test", CASE, "--main=wallet_attackers_case", "--max-samples=1", "--seed=7", "--backend=typescript"])
    if "9 passing" not in (OUT / "traces.log").read_text():
        receipt["status"] = "failed"
        save()
        raise SystemExit("All nine required financial trace tests must run")
    receipt["trace_tests"] = 9
    common = ["verify", CASE, "--main=wallet_attackers_case", "--backend=apalache", "--apalache-version=0.62.1", "--invariant=safety"]
    run("hardened-depth-12", [*common, "--max-steps=12"])
    trace = OUT / "stale-authorization.itf.json"
    trace.unlink(missing_ok=True)
    run("stale-negative-depth-4", [*common, "--step=stepStale", "--max-steps=4", f"--out-itf={trace}"], expected=1)
    evidence = json.loads(trace.read_text())
    if evidence.get("vars") != ["wallet_attackers_case::wallet_signing::s"]:
        raise SystemExit("Unexpected negative trace state-variable binding")
    if not any(state.get("wallet_attackers_case::wallet_signing::s", {}).get("unsafe") is True for state in evidence.get("states", [])):
        receipt["status"] = "failed"
        save()
        raise SystemExit("Negative check did not retain the intended unsafe-signature counterexample")
    run("containment-typecheck", ["typecheck", CONTAINMENT])
    run("containment-traces", ["test", CONTAINMENT, "--main=wallet_containment", "--max-samples=1", "--seed=7", "--backend=typescript"])
    if "9 passing" not in (OUT / "containment-traces.log").read_text():
        raise SystemExit("All nine additional containment traces must run")
    receipt["containment_trace_tests"] = 9
    containment = ["verify", CONTAINMENT, "--main=wallet_containment", "--backend=apalache", "--apalache-version=0.62.1"]
    run("containment-depth-12", [*containment, "--invariant=safety", "--max-steps=12"])
    for label, step, invariant, intended in (
        ("recovery-negative-depth-4", "stepBrokenRecovery", "signatureSafety", "unsafe"),
        ("clearing-negative-depth-4", "stepFalseClear", "clearingTruth", "cleared"),
    ):
        negative = OUT / (label + ".itf.json")
        negative.unlink(missing_ok=True)
        run(label, [*containment, "--invariant=" + invariant, "--step=" + step,
            "--max-steps=4", "--out-itf=" + str(negative)], expected=1)
        counterexample = json.loads(negative.read_text())
        variable = "c"  # Top-level module fields are unqualified in native ITF.
        if counterexample.get("vars") != [variable]:
            raise SystemExit("Unexpected containment counterexample binding")
        states = [state.get(variable, {}) for state in counterexample.get("states", [])]
        if not any(state.get(intended) is True and
                (intended == "unsafe" or state.get("witness") is False) for state in states):
            raise SystemExit("Containment counterexample does not demonstrate the intended failure")
    run("host-typecheck", ["typecheck", HOST])
    run("host-traces", ["test", HOST, "--main=wallet_host", "--max-samples=1", "--seed=7", "--backend=typescript"])
    if "9 passing" not in (OUT / "host-traces.log").read_text():
        raise SystemExit("All nine Host-boundary traces must run")
    receipt["host_trace_tests"] = 9
    host = ["verify", HOST, "--main=wallet_host", "--backend=apalache", "--apalache-version=0.62.1", "--invariant=safety"]
    run("host-depth-12", [*host, "--max-steps=12"])
    for label, step in (("durability-negative-depth-4", "stepNoDurability"),
                        ("rollback-negative-depth-4", "stepRollback")):
        negative = OUT / (label + ".itf.json")
        negative.unlink(missing_ok=True)
        run(label, [*host, "--step=" + step, "--max-steps=4", "--out-itf=" + str(negative)], expected=1)
        counterexample = json.loads(negative.read_text())
        if counterexample.get("vars") != ["h"]:
            raise SystemExit("Unexpected Host counterexample binding")
        states = [state.get("h", {}) for state in counterexample.get("states", [])]
        if not any(state.get("unsafe") is True and
                (state.get("durable") is False if step == "stepNoDurability" else
                 state.get("sent") == {"#bigint": "2"}) for state in states):
            raise SystemExit("Host counterexample does not retain the intended native-boundary failure")
    if any(hashlib.sha256((ROOT / p).read_bytes()).hexdigest() != digest
           for p, digest in receipt["inputs"].items()):
        receipt["status"] = "failed"
        save()
        raise SystemExit("Threat model inputs changed during verification; rerun the gate")
    receipt["status"] = "passed"
    receipt["scope"] = "bounded model checks and deterministic traces; no deployed Host or Lean/Quint refinement claim"
    save()
    print(f"Receipt: {receipt_path}")


if __name__ == "__main__":
    main()
