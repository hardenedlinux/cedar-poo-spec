"""Workspace dependency boundaries, isolated profile builds and consumer gates."""

import json
from pathlib import Path
import subprocess


COMMERCE = (None, "projection", "admission", "acceptance", "ap2-receipt", "ap2-coordination")


def dependency_names(flat_tree: str) -> set[str]:
    """Package names from `cargo tree --prefix none --format {p}`.

    Cargo package names cannot contain whitespace. Source paths are diagnostic
    suffixes, never dependency identities.
    """
    return {line.split()[0] for line in flat_tree.splitlines() if line.strip()}


def run(repository: Path) -> None:
    repository = repository.resolve()
    base = ["--locked", "--manifest-path", "Cargo.toml"]

    def cargo(command: str, *args: str) -> None:
        print(f"workspace gate: cargo {command} {' '.join(args)}", flush=True)
        subprocess.run(["cargo", command, *base, *args], cwd=repository, check=True)

    metadata = json.loads(subprocess.check_output(
        ["cargo", "metadata", *base, "--all-features", "--format-version", "1"],
        cwd=repository, text=True,
    ))
    if any(p["name"].startswith("mrr-data") for p in metadata["packages"]):
        raise ValueError("Cedar workspace resolves an MRR Data dependency")
    members = [p for p in metadata["packages"] if p["id"] in metadata["workspace_members"]]
    for package in members:
        if any(
            d["name"].startswith("mrr-") or "github.com/tao3k/mrr-data" in (d.get("source") or "")
            for d in package["dependencies"]
        ):
            raise ValueError(f"Cedar package {package['name']} imports MRR")
        if package["name"] != "cedar-poo-bridge" and not package["name"].endswith("-case"):
            if any(d["name"].endswith("-case") or d["name"] == "cedar-poo-bridge"
                   for d in package["dependencies"]):
                raise ValueError(f"library {package['name']} imports an application Case")

    build = repository / ".lake/build"
    build.mkdir(parents=True, exist_ok=True)
    # Inspect one package at a time: a workspace all-features build unifies dependencies
    # and cannot demonstrate isolation of a production consumer's selected profile.
    profiles = [(p, None) for p in ("cedar-poo-core", "cedar-poo-agentic",
                                  "cedar-poo-pseudonymization")]
    profiles += [("cedar-poo-pseudonymization", "google-sdp")]
    profiles += [("cedar-poo-commerce", f) for f in COMMERCE]
    profiles += [("cedar-poo-commerce-case", f) for f in COMMERCE]
    profiles += [("cedar-poo-commerce-mandate", None),
                 ("cedar-poo-commerce-mandate", "ap2-checkout"),
                 ("cedar-poo-commerce-case", "ap2-checkout")]
    profiles += [("cedar-poo-pseudonymization-case", "google-contract")]
    for package, feature in profiles:
        args = ["-p", package, "--no-default-features"]
        if feature:
            args += ["--features", feature]
        print(f"dependency boundary: {package}/{feature or 'default'}", flush=True)
        tree = subprocess.check_output(
            ["cargo", "tree", *base, *args, "-e", "normal", "--prefix", "none", "--format", "{p}"], cwd=repository, text=True,
        )
        (build / f"{package}-{feature or 'default'}-tree.txt").write_text(tree)
        dependencies = dependency_names(tree)
        if any(name.startswith("cedar-policy") for name in dependencies):
            raise ValueError(f"{package}/{feature} unexpectedly depends on Cedar runtime")
        expects_p256 = package.startswith("cedar-poo-commerce") and (
            package != "cedar-poo-commerce-mandate" or feature == "ap2-checkout"
        )
        if ("p256" in dependencies) != expects_p256:
            raise ValueError(f"{package}/{feature} has an unexpected P-256 dependency")
        if any(name.startswith("mrr-data") for name in dependencies):
            raise ValueError(f"{package}/{feature} imports MRR")
        cargo("clippy", *args, "--all-targets", "--", "-D", "warnings")

    subprocess.run(["cargo", "fmt", "--all", "--check"], cwd=repository, check=True)
    cargo("clippy", "--workspace", "--all-targets", "--all-features", "--", "-D", "warnings")
    cargo("test", "--workspace", "--all-features", "--exclude", "cedar-poo-commerce-case")
    cargo("test", "-p", "cedar-poo-commerce-case", "--no-default-features")
    cargo("test", "-p", "cedar-poo-commerce-case", "--no-default-features",
          "--features", "ap2-checkout", "--test", "agentic_ai_commerce_mandate_consumer")
    cargo("test", "-p", "cedar-poo-commerce-case", "--no-default-features",
          "--features", "ap2-coordination", "--test", "agentic_ai_commerce_coordination_consumer")
    # Fixture-dependent consumers execute in cedar-conformance after Lean exports.
    cargo("test", "-p", "cedar-poo-commerce-case", "--features", "admission",
          "--test", "agentic_ai_commerce_admission_consumer")
    for feature in ("local", "google-contract", "google-admission"):
        cargo("clippy", "-p", "cedar-poo-pseudonymization-case", "--no-default-features",
              "--features", feature, "--all-targets", "--", "-D", "warnings")
    # Also compile every package's defaults independently, preventing rich workspace
    # feature unification from hiding an omitted dependency or cfg declaration.
    for package in sorted(p["name"] for p in members):
        cargo("check", "-p", package, "--all-targets", "--no-default-features")
