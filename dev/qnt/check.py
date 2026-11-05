"""Check the POO-derived finite threat model; retain separate evidence receipts."""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / ".lake/build/wallet-threat"
QUINT = ROOT / "dev/node_modules/.bin/quint"
MODEL = "dev/qnt/financial/WalletSigning.qnt"


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
    inputs = [MODEL, "dev/qnt/attackers/Capabilities.qnt", ".lake/build/wallet-attackers-profile.qnt",
              "CedarPooSpec/Attackers/Trace.lean", "CedarPooSpec/Attackers/ProfileObject.lean",
              "CedarPooSpec/Vertical/FinancialServices/PaymentSigning.lean",
              "CedarPooSpec/Vertical/FinancialServices/PaymentOperation.lean",
              "Examples/Enterprise/Payment/WalletSigning.lean",
              "Examples/Enterprise/Payment/WalletAttack.lean",
              "Examples/Enterprise/Payment/WalletAttackExport.lean",
              "Tests/Enterprise/Payment/WalletSigning.lean", "Tests/Attackers/ProfileObject.lean",
              "dev/qnt/check.py", "dev/package.json", "dev/bun.lock"]
    receipt["inputs"] = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in inputs}

    def run(label: str, args: list[str], expected: int = 0) -> None:
        log = OUT / f"{label}.log"
        command_args = [str(ROOT / arg) if arg == MODEL else arg for arg in args]
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
    run("traces", ["test", MODEL, "--main=wallet_signing", "--max-samples=1", "--seed=7", "--backend=typescript"])
    common = ["verify", MODEL, "--main=wallet_signing", "--backend=apalache", "--apalache-version=0.62.1", "--invariant=safety"]
    run("hardened-depth-12", [*common, "--max-steps=12"])
    trace = OUT / "stale-authorization.itf.json"
    trace.unlink(missing_ok=True)
    run("stale-negative-depth-4", [*common, "--step=stepStale", "--max-steps=4", f"--out-itf={trace}"], expected=1)
    evidence = json.loads(trace.read_text())
    if not any(state.get("s", {}).get("unsafe") is True for state in evidence.get("states", [])):
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
