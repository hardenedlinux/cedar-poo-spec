# Generate Lean inputs, replay Cedar decisions, then run Tests/Conformance.
check-conformance: check-replay-receipts check-schema-bound-receipts check-schema-bound-scenarios check-attested-schema-evolution check-authorization-delta check-authorization-delta-operational check-authorization-delta-reasons check-authorization-delta-effective-reasons check-payment-delta check-payment-interaction check-payment-audit check-agent-trace-delta check-health-authorization-impact check-personnel-governance check-agentic-ai-commerce-admission check-agentic-ai-commerce-acceptance check-agentic-ai-commerce-presentation check-agentic-ai-commerce-wire-corpus

check-agentic-ai-commerce-admission: check-agentic-ai-commerce-projection
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check agentic-ai-commerce-admission

check-agentic-ai-commerce-projection:
    mkdir -p .lake/build
    lake build Tests.AgenticAI.Commerce.Projection
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check agentic-ai-commerce-projection

check-personnel-governance:
    lake build Examples.Manifests Tests.Enterprise.Personnel.SourceCustody
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Examples/Manifests.lean source-custody-validated > .lake/build/source-custody-validated-manifest.json
    cargo run --locked --quiet -p cedar-poo-bridge --manifest-path Cargo.toml -- replay-validated-receipts < .lake/build/source-custody-validated-manifest.json > .lake/build/source-custody-validated-receipts.json
    jq -e -f Tests/Conformance/personnel-governance-receipts.jq .lake/build/source-custody-validated-receipts.json > /dev/null

check-tests: build-productions check-storage-effect-v1 check-protected-storage-v1 check-storage-profiles-v1 check-google-table-batch-v1
    lake build Tests

check-storage-effect-v1:
    lake env lean --run Productions/Data/StorageEffectFixtureMain.lean | diff -u Tests/Conformance/storage-effect-v1.json -

check-protected-storage-v1:
    lake env lean --run Productions/Data/ProtectedStorageFixtureMain.lean | diff -u Tests/Conformance/protected-storage-v1.json -

check-storage-profiles-v1:
    lake env lean --run Productions/Data/StorageProfileMatrixMain.lean | diff -u Tests/Conformance/storage-profiles-v1.json -

check-google-table-batch-v1:
    lake env lean --run Productions/Pseudonymization/TableBatchFixtureMain.lean | diff -u Tests/Conformance/google-table-batch-v1.json -

check-delta: check-gateway-delta check-authorization-delta check-authorization-delta-operational check-authorization-delta-reasons check-authorization-delta-effective-reasons check-payment-delta check-payment-interaction check-agent-trace-delta check-health-authorization-impact

check-gateway:
    lake build CedarPooSpec.Gateway Tests.Gateway.Contracts Tests.Gateway.OAuth Tests.Gateway.Counterexamples Tests.Gateway.Objects Tests.Gateway.Publication Tests.Gateway.Delta Tests.Gateway.ZeroTrust Tests.Gateway.PublicationReview Tests.ZeroTrust.UsageControl Tests.ZeroTrust.ImportBoundary Tests.ZeroTrust.Functional
    cargo test --locked -p cedar-poo-runtime --features gateway --lib gateway::oauth

check-gateway-delta: check-gateway
    lake build Productions.Gateway.CurrentUseMain
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Productions/Gateway/CurrentUseMain.lean
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Tests/Gateway/Delta.lean
    cargo run --locked -p cedar-poo-bridge --manifest-path Cargo.toml -- replay-receipts < .lake/build/gateway-current-review-manifest.json > .lake/build/gateway-current-review-receipts.json
    jq -e 'length == 10' .lake/build/gateway-current-review-receipts.json > /dev/null
    cargo test --locked -p cedar-poo-runtime --lib publication_review -- --include-ignored

check-replay-receipts: prepare-agent-payment-manifest
    cargo run --locked --quiet -p cedar-poo-bridge --manifest-path Cargo.toml -- replay-receipts < .lake/build/agent-payment-manifest.json > .lake/build/agent-payment-replay-receipts.json
    jq -e --slurpfile manifest .lake/build/agent-payment-manifest.json -f Tests/Conformance/agent-payment-replay-receipts.jq .lake/build/agent-payment-replay-receipts.json > /dev/null

prepare-agent-payment-validated-manifest: build-examples
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test prepare prepare-agent-payment-validated-manifest

check-schema-bound-receipts: prepare-agent-payment-validated-manifest
    cargo run --locked --quiet -p cedar-poo-bridge --manifest-path Cargo.toml -- replay-validated-receipts < .lake/build/agent-payment-validated-manifest.json > .lake/build/agent-payment-validated-receipts.json
    jq -e --slurpfile manifest .lake/build/agent-payment-validated-manifest.json -f Tests/Conformance/agent-payment-validated-receipts.jq .lake/build/agent-payment-validated-receipts.json > /dev/null

prepare-schema-bound-scenarios: build-examples
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test prepare prepare-schema-bound-scenarios

check-schema-bound-scenarios: prepare-schema-bound-scenarios
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test schema-bound

prepare-attested-schema-evolution: build-examples
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test prepare prepare-attested-schema-evolution

check-attested-schema-evolution: prepare-attested-schema-evolution
    jq -e -f Tests/Conformance/attested-schema-evolution.jq .lake/build/attested-schema-evolution.json > /dev/null
    cargo run --locked --quiet -p cedar-poo-bridge --manifest-path Cargo.toml -- replay-schema-only-revision < .lake/build/attested-schema-evolution.json > .lake/build/attested-schema-evolution-receipt.json
    jq -e -f Tests/Conformance/attested-schema-evolution-receipt.jq .lake/build/attested-schema-evolution-receipt.json > /dev/null

check-authorization-delta: build-examples
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check authorization-delta

check-authorization-delta-operational:
    lake build CedarPooSpec.Authorization.Delta.OperationalExactProof Tests.Governance.AuthorizationDeltaOperational Tests.Governance.AuthorizationDeltaFormula
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check authorization-delta-operational

# Research artifact only: emits the exact query and cvc5's CPC output.
# The fixture's UNSAT theorem is separate and uses native computation certificates.
probe-authorization-delta-proof:
    lake build CedarPooSpec.Authorization.Delta.OperationalExactProof Examples.Governance.TicketSharing
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Tests/Governance/AuthorizationDeltaProofProbe.lean > .lake/build/authorization-delta-exact.smt2
    timeout --signal=TERM --kill-after=3s 120s "$CVC5" --lang=smt --produce-proofs --proof-check=lazy --dump-proofs --proof-format-mode=cpc .lake/build/authorization-delta-exact.smt2 > .lake/build/authorization-delta-exact.cpc
    rg -q '^\(check-sat\)$' .lake/build/authorization-delta-exact.smt2
    test "$(head -n 1 .lake/build/authorization-delta-exact.cpc)" = unsat
    rg -q '^\(step ' .lake/build/authorization-delta-exact.cpc

# Optional pinned research check: Ethos validates a renamed reference query.
# The constructor-name translation is still outside the Lean proof boundary.
probe-authorization-delta-proof-ethos: probe-authorization-delta-proof
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check-cpc --input .lake/build/authorization-delta-exact.smt2 --output-dir .lake/build --cvc5 "$CVC5" --ethos "$ETHOS" --signature-root "$CPC_SIGNATURE_ROOT"

check-authorization-delta-reasons:
    lake build Tests.Governance.AuthorizationDeltaReasons
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check authorization-delta-reasons

check-authorization-delta-effective-reasons:
    lake build CedarPooSpec.Authorization.Delta.EffectiveReasonsProof Tests.Governance.AuthorizationDeltaEffectiveReasons
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check authorization-delta-effective-reasons

check-payment-interaction:
    lake build Examples.Enterprise.Agent.Payment.JointRelease
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check payment-interaction

# Public payment operation, selectable audit stages, and concrete Cedar adapter.
check-payment-audit:
    lake build CedarPooSpec.Vertical.FinancialServices.PaymentLedger Tests.Enterprise.Agent.Payment.PaymentAudit

# Agent identity, delegated purchase scope, exact merchant offer, and cumulative budget.
check-agentic-ai-commerce:
    lake build CedarPooSpec.Vertical.FinancialServices.AgenticCommercePayment Tests.AgenticAI.Commerce.Admission

check-agent-trace-delta:
    lake build Examples.Enterprise.Agent.Session.HostSafety
    just example enterprise agent session-trace-delta

check-health-authorization-impact:
    lake build Examples.Health.Pseudonymization.AuthorizationImpact
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check health-authorization-impact

check-authorization-delta-proof:
    just check-gateway
    lake build CedarPooSpec.Authorization.Delta.Proof CedarPooSpec.Authorization.Delta.BooleanCore Tests.Governance.AuthorizationDeltaFormula Tests.Governance.AuthorizationDeltaDirect Tests.Governance.AuthorizationDeltaAxiomAudit

check-payment-delta: build-examples
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check payment-delta

check-agentic-ai-commerce-acceptance:
    lake build Tests.AgenticAI.Commerce.Acceptance
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check agentic-ai-commerce-acceptance

check-agentic-ai-commerce-presentation:
    lake build Tests.AgenticAI.Commerce.Presentation
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check agentic-ai-commerce-presentation

# Regular CI checks frozen bytes; explicit SDK replay needs its pinned source checkout.
check-agentic-ai-commerce-wire-corpus:
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test ap2-wire --check-frozen
    cargo test --locked -p cedar-poo-commerce-case --no-default-features --features ap2-checkout --test agentic_ai_commerce_mandate_consumer

check-agentic-ai-commerce-wire-sdk sdk_root:
    uv run --project python --package cedar-poo-py-test --extra ap2-sdk --locked cedar-poo-py-test ap2-wire --sdk-root {{quote(sdk_root)}}

check-agentic-ai-commerce-constraint-sdk sdk_root:
    uv run --project python --package cedar-poo-py-test --extra ap2-sdk --locked cedar-poo-py-test ap2-constraints --sdk-root {{quote(sdk_root)}}

# Compile the existing manifest entrypoint; its output must match Lean execution byte for byte.
check-native-catalog: build-examples
    sha256sum .lake/build/lib/lean/Examples/Governance/AttestedDataAccess.olean .lake/build/lib/lean/Examples/Enterprise/Procurement/PurchaseApproval.olean .lake/build/lib/lean/Examples/Enterprise/Agent/Delegation/AgentDelegation.olean > .lake/build/native-artifact-owner.sha256
    just check-policy-reuse
    just example governance trusted-network
    just example enterprise procurement delegated-approval
    just example enterprise agent chain
    sha256sum -c .lake/build/native-artifact-owner.sha256
    lake build caseManifestsNative
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Examples/Manifests.lean catalog > .lake/build/functional-catalog-lean.json
    timeout --signal=TERM --kill-after=3s 120s .lake/build/bin/caseManifestsNative catalog > .lake/build/functional-catalog-native.json
    cmp .lake/build/functional-catalog-lean.json .lake/build/functional-catalog-native.json

# Complete catalog replay; preserve all pre-migration wire artifacts exactly.
check-functional-catalog: check-native-catalog
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Examples/Manifests.lean all
    sha256sum -c Tests/Conformance/functional-manifests.sha256
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Examples/Manifests.lean catalog > .lake/build/functional-catalog.json
    cargo run --locked --quiet -p cedar-poo-bridge --manifest-path Cargo.toml -- replay-catalog < .lake/build/functional-catalog.json > .lake/build/functional-catalog-receipts.json
    jq -e 'length == 51 and (."claim-settlement-handoff".scenarios | length) == 14 and ([."claim-settlement-handoff".scenarios[] | select(.admitted) | .name] == ["ready"])' .lake/build/functional-catalog-receipts.json > /dev/null
    cargo test --locked -p cedar-poo-bridge --lib emitted_catalog_rejects_cross_artifact_tampering -- --ignored
    cargo test --locked -p cedar-poo-runtime --lib prepared_catalog_matches_original_workflows -- --ignored

# Consumer migration is an enforced boundary; primitives retain compatibility APIs.
check-functional-consumers:
    status=0; rg -U -n 'def (policy\?|owner\?|control\?|channel\?|boundary\?|intent\?|scope\?|artifact\?)[^\n]*\n[ \t]+profile\.read' CedarPooSpec --glob '*.lean' || status=$?; test "$status" -eq 1
    status=0; rg -n 'PolicyJson\.(authorizationCase|publish|compiled)\b|CompoundAuthorization\.authorize(All|Layers)\b' Examples Productions --glob '*.lean' || status=$?; test "$status" -eq 1
    status=0; rg -n 'PolicyJson\.authorizationCase\b|CompoundAuthorization\.authorize(All|Layers)\b' CedarPooSpec --glob '*.lean' --glob '!Compilation.lean' --glob '!CompilationJson.lean' || status=$?; test "$status" -eq 1

check-claim-settlement-replay: build-examples
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Examples/Manifests.lean catalog claim-settlement-claims claim-settlement-banking claim-settlement-handoff > .lake/build/claim-settlement-catalog.json
    cargo run --locked --quiet -p cedar-poo-bridge --manifest-path Cargo.toml -- replay-catalog < .lake/build/claim-settlement-catalog.json > .lake/build/claim-settlement-receipts.json
    jq -e 'length == 3 and (."claim-settlement-handoff".scenarios | length) == 14 and ([."claim-settlement-handoff".scenarios[] | select(.admitted) | .name] == ["ready"])' .lake/build/claim-settlement-receipts.json > /dev/null

# Build one native wheel, install it in isolated interpreters, and compare actual
# extension receipts with the existing Rust CLI for every applicable Lean entry.
[script("bash")]
check-python-bindings versions="3.11 3.14":
    set -euo pipefail
    lake build caseManifestsNative
    .lake/build/bin/caseManifestsNative all
    .lake/build/bin/caseManifestsNative catalog > .lake/build/functional-catalog.json
    cargo build --locked -p cedar-poo-bridge
    mkdir -p .lake/build/python-bindings
    evidence=$(mktemp -d .lake/build/python-bindings/run.XXXXXX)
    evidence=$(cd "$evidence" && pwd)
    { git rev-parse HEAD; git status --porcelain=v1; sha256sum Cargo.lock python/uv.lock python/packages/bridge/pyproject.toml rust/python/Cargo.toml rust/python/src/lib.rs rust/python/src/bindings.rs; } > "$evidence/provenance.txt"
    uv build --project python/packages/bridge --wheel --out-dir "$evidence/wheels"
    wheels=("$evidence"/wheels/*.whl)
    test "${#wheels[@]}" -eq 1
    sha256sum "${wheels[0]}" > "$evidence/wheel.sha256"
    native_venvs=$(mktemp -d)
    trap 'rm -rf "$native_venvs"' EXIT
    read -r -a requested_versions <<< {{quote(versions)}}
    for version in "${requested_versions[@]}"; do
        uv venv --python "$version" "$native_venvs/python$version"
        interpreter="$native_venvs/python$version/bin/python"
        uv pip install --python "$interpreter" "${wheels[0]}"
        uv run --project python --package cedar-poo-py-test --locked python -m cedar_poo_py_test.resources --timeout-seconds 120 --output "$evidence/python$version.resource.json" "$interpreter" -I python/native_tests/test_bindings.py 2>&1 | tee "$evidence/python$version.log"
        jq -e ' .returncode == 0 and .termination_reason == null and .owned_group_quiesced and .resource_observation_complete and .timeout_seconds == 120 ' "$evidence/python$version.resource.json" > /dev/null
    done

# Shared model, native effects and independent public audit across every case domain.
check-effect-protocol: check-functional-catalog
    lake build Tests.Gateway.EffectProtocol Productions.Gateway.EffectProtocolMain Productions.Gateway.CurrentUseMain
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Productions/Gateway/EffectProtocolMain.lean
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Productions/Gateway/CurrentUseMain.lean
    cargo test --locked -p cedar-poo-runtime --features gateway --lib gateway::
    timeout --signal=TERM --kill-after=3s 120s cargo test --locked -p cedar-poo-bridge --features gateway --test gateway gateway:: -- --include-ignored
    cargo build --locked --release -p cedar-poo-bridge --features gateway
    mkdir -p .lake/build/resources
    timeout --signal=TERM --kill-after=3s 120s uv run --project python --package cedar-poo-py-test --locked python -m cedar_poo_py_test.resources --timeout-seconds 120 --output .lake/build/resources/gateway-effect.json rust/target/release/cedar-poo-bridge gateway-replay-catalog .lake/build/gateway-effect-protocol.json < .lake/build/functional-catalog.json > .lake/build/gateway-effect-results.json
    jq -e '.returncode == 0 and .termination_reason == null and .owned_group_quiesced and .resource_observation_complete and .timeout_seconds == 120' .lake/build/resources/gateway-effect.json > /dev/null
    jq -c '{format_version,catalogue_entries,outcome_count,applicable_entries:(.covered_entries|length),data_or_artifact_entries}' .lake/build/gateway-effect-results.json

# Actual C4 nonidentity review -> publication -> current SDK effect, all domains.
[script("bash")]
check-reviewed-effects: check-functional-catalog
    set -euo pipefail
    lake build Tests.Gateway.ReviewedEffect Tests.Gateway.Lifecycle reviewedEffectsNative
    mkdir -p .lake/build/reviewed-effects .lake/build/resources
    jq -r '.entries | keys[]' .lake/build/functional-catalog.json > .lake/build/reviewed-effects/entries.txt
    status=0
    while IFS= read -r entry; do
        if timeout --signal=TERM --kill-after=3s 120s .lake/build/bin/reviewedEffectsNative "$entry" > ".lake/build/reviewed-effects/$entry.json" 2> ".lake/build/reviewed-effects/$entry.log"; then
            echo "REVIEWED-PRODUCER-OK: $entry"
        else
            code=$?
            echo "REVIEWED-PRODUCER-FAILED: $entry; status=$code" >&2
            cat ".lake/build/reviewed-effects/$entry.log" >&2
            status=1
        fi
    done < .lake/build/reviewed-effects/entries.txt
    test "$status" -eq 0
    cargo test --locked -p cedar-poo-bridge --features gateway --lib reviewed -- --include-ignored
    timeout --signal=TERM --kill-after=3s 120s cargo test --locked -p cedar-poo-bridge --features gateway --test gateway reviewed:: -- --include-ignored
    cargo build --locked --release -p cedar-poo-bridge --features gateway
    timeout --signal=TERM --kill-after=3s 120s uv run --project python --package cedar-poo-py-test --locked python -m cedar_poo_py_test.resources --timeout-seconds 120 --output .lake/build/resources/gateway-reviewed-effects.json rust/target/release/cedar-poo-bridge gateway-reviewed-catalog .lake/build/reviewed-effects < .lake/build/functional-catalog.json > .lake/build/gateway-reviewed-effects.jsonl
    jq -e '.returncode == 0 and .termination_reason == null and .owned_group_quiesced and .resource_observation_complete and .timeout_seconds == 120' .lake/build/resources/gateway-reviewed-effects.json > /dev/null
    tail -n 1 .lake/build/gateway-reviewed-effects.jsonl | jq -c .
    timeout --signal=TERM --kill-after=3s 120s uv run --project python --package cedar-poo-py-test --locked python -m cedar_poo_py_test.resources --timeout-seconds 120 --output .lake/build/resources/gateway-lifecycle.json rust/target/release/cedar-poo-bridge gateway-lifecycle-catalog .lake/build/reviewed-effects < .lake/build/functional-catalog.json > .lake/build/gateway-lifecycle.jsonl
    jq -e '.returncode == 0 and .termination_reason == null and .owned_group_quiesced and .resource_observation_complete and .timeout_seconds == 120' .lake/build/resources/gateway-lifecycle.json > /dev/null
    tail -n 1 .lake/build/gateway-lifecycle.jsonl | jq -c .

# Native API percentiles are distinct from complete regression process wall time.
bench-gateway-runtime:
    cargo build --locked --release -p cedar-poo-bridge --features gateway
    timeout --signal=TERM --kill-after=3s 120s uv run --project python --package cedar-poo-py-test --locked python -m cedar_poo_py_test.resources --timeout-seconds 120 --output .lake/build/resources/gateway-runtime-api.json rust/target/release/cedar-poo-bridge benchmark-gateway-runtime .lake/build/reviewed-effects < .lake/build/functional-catalog.json > .lake/build/gateway-runtime-api.jsonl
    jq -e '.returncode == 0 and .termination_reason == null and .owned_group_quiesced and .resource_observation_complete and .timeout_seconds == 120' .lake/build/resources/gateway-runtime-api.json > /dev/null
    tail -n 1 .lake/build/gateway-runtime-api.jsonl > .lake/build/gateway-runtime-api.json
    jq -c 'del(.samples,.program_samples)' .lake/build/gateway-runtime-api.json
    jq -c '.program_samples[] | {kind:"native-program-setup", observation:.}' .lake/build/gateway-runtime-api.json
    jq -c '.samples[] | {kind:"native-api-samples", observation:.}' .lake/build/gateway-runtime-api.json
    timeout --signal=TERM --kill-after=3s 120s uv run --project python --package cedar-poo-py-test --locked python -m cedar_poo_py_test.resources --timeout-seconds 120 --output .lake/build/resources/gateway-append-scale.json rust/target/release/cedar-poo-bridge benchmark-gateway-append .lake/build/reviewed-effects < .lake/build/functional-catalog.json > .lake/build/gateway-append-scale.json
    jq -e '.returncode == 0 and .termination_reason == null and .owned_group_quiesced and .resource_observation_complete and .timeout_seconds == 120' .lake/build/resources/gateway-append-scale.json > /dev/null
    jq -c 'del(.samples_ns)' .lake/build/gateway-append-scale.json
    jq -c '.samples_ns | to_entries[] | {kind:"native-append-samples",phase:.key,samples_ns:.value}' .lake/build/gateway-append-scale.json
