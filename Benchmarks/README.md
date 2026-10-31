# Benchmark ownership and results

Lean owns algorithm workloads, checksums, types, Contracts and proofs. Native
executables are declared in `lakefile.toml`; use `just bench-functional-native`
for the existing nine-family native probes. Their internal timers use the
standard `IO.monoNanosNow`. The upstream POO `just benchmark-c4` likewise runs a
Lake-built native executable. Rust owns SDK replay and allocation counters.

The official [Lean benchmark suite](https://github.com/leanprover/lean4/blob/master/tests/README.md)
distinguishes `compile_bench` (compiled execution), `elab_bench` (elaboration)
and `lake_bench` (Lake). It is Lean's own source-tree test infrastructure,
rather than a required dependency of consumer libraries. Follow its separation
of workloads and generated measurements; do not import its compiler test suite
into this library. Its measurement format is JSONL, not a requirement to commit
CSV. The standard [monotonic timer](https://github.com/leanprover/lean4/blob/v4.34.1/src/Init/System/IO.lean)
is already used by our Lean probes.

Python in `cedar_poo_py_test` and `DataflowLifecycle.py` is external testing
orchestration: launching fixed native processes, comparing complete output bytes,
recording identities and observing OS clocks / process RSS. It implements no
Cedar policy or POO algorithm. Building and consuming the Lean library requires
no Python. In-process timers cannot observe the interval before their executable's
`main`; OS observation remains separate from algorithm benchmarks. Instrumented
launch samples never replace ordinary native performance receipts.

## Generated results

Write measurements, raw stdout/stderr, CSV and resource receipts under ignored
`.lake/build/` or `$RUNNER_TEMP`. Keep workloads, expected test fixtures and
concise audit conclusions in Git. Do not add generated result tables to `docs/`.
The existing CI uploads these observations even when an earlier check fails;
download them from the run's **Artifacts** section or:

```sh
gh run download RUN_ID --repo hardenedlinux/cedar-poo-spec --name native-evidence-cedar-conformance
gh run download RUN_ID --repo hardenedlinux/cedar-poo-spec --name native-evidence-lean
```

Artifact availability follows the repository's configured retention. Download
receipts needed for longer term comparisons before they expire. Run identity,
source/executable hashes, failed controls and ordinary versus instrumented scope
must remain attached to the data; an absent artifact is unavailable evidence.

## Previously committed measurements

The 62 generated CSV/JSON files previously in `docs/` were removed from the
current source tree. The final historical snapshot is commit
`d182c73f1aefc39811a4694b06a5a69cb45ef388`; audit links to those historical
observations are pinned to that commit. History was not rewritten. Retrieve an
old receipt without restoring generated files into the source tree, for example:

```sh
mkdir -p .lake/build/historical-evidence
git show d182c73f1aefc39811a4694b06a5a69cb45ef388:docs/native-c4-preparation-lifecycle.json > .lake/build/historical-evidence/native-c4-preparation-lifecycle.json
```

These are historical macOS measurements, not artifacts of a newer Ubuntu run.
Packaging changes do not turn them into newly measured performance evidence.
