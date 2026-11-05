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
    inputs = [MODEL, ".lake/build/binance-2026-metadata.json",
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
        command_args = [str(ROOT / arg) if arg in (MODEL, CASE) else arg for arg in args]
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
        for source in (MODEL, "dev/qnt/attackers/Capabilities.qnt"):
            target = Path(isolated) / source
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / source, target)
        run("source-only-typecheck", ["typecheck", str(Path(isolated) / MODEL)])
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
