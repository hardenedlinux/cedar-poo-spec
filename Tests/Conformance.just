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

check-delta: check-authorization-delta check-authorization-delta-operational check-authorization-delta-reasons check-authorization-delta-effective-reasons check-payment-delta check-payment-interaction check-agent-trace-delta check-health-authorization-impact

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
    lake build CedarPooSpec.AuthorizationDeltaOperationalExactProof Tests.Governance.AuthorizationDeltaOperational Tests.Governance.AuthorizationDeltaFormula
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check authorization-delta-operational

# Research artifact only: emits the exact query and cvc5's CPC output.
# The fixture's UNSAT theorem is separate and uses native computation certificates.
probe-authorization-delta-proof:
    lake build CedarPooSpec.AuthorizationDeltaOperationalExactProof Examples.Governance.TicketSharing
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
    lake build CedarPooSpec.AuthorizationDeltaEffectiveReasonsProof Tests.Governance.AuthorizationDeltaEffectiveReasons
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
    lake build CedarPooSpec.AuthorizationDeltaProof CedarPooSpec.AuthorizationDeltaBooleanCore Tests.Governance.AuthorizationDeltaFormula Tests.Governance.AuthorizationDeltaDirect Tests.Governance.AuthorizationDeltaAxiomAudit

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

# Complete catalog replay; preserve all pre-migration wire artifacts exactly.
check-functional-catalog: build-examples
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Examples/Manifests.lean all
    sha256sum -c Tests/Conformance/functional-manifests.sha256
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Examples/Manifests.lean catalog > .lake/build/functional-catalog.json
    cargo run --locked --quiet -p cedar-poo-bridge --manifest-path Cargo.toml -- replay-catalog < .lake/build/functional-catalog.json > .lake/build/functional-catalog-receipts.json
    jq -e 'length == 51 and (."claim-settlement-handoff".scenarios | length) == 14 and ([."claim-settlement-handoff".scenarios[] | select(.admitted) | .name] == ["ready"])' .lake/build/functional-catalog-receipts.json > /dev/null
    cargo test --locked -p cedar-poo-bridge --lib emitted_catalog_rejects_cross_artifact_tampering -- --ignored
    cargo test --locked -p cedar-poo-runtime --lib prepared_catalog_matches_original_schema_workflow -- --ignored

# Consumer migration is an enforced boundary; primitives retain compatibility APIs.
check-functional-consumers:
    if rg -U -n 'def (policy\?|owner\?|control\?|channel\?|boundary\?|intent\?|scope\?|artifact\?)[^\n]*\n[ \t]+profile\.read' CedarPooSpec --glob '*.lean'; then exit 1; fi
    if rg -n 'PolicyJson\.(authorizationCase|publish|compiled)\b|CompoundAuthorization\.authorize(All|Layers)\b' Examples Productions --glob '*.lean'; then exit 1; fi
    if rg -n 'PolicyJson\.authorizationCase\b|CompoundAuthorization\.authorize(All|Layers)\b' CedarPooSpec --glob '*.lean' --glob '!Compilation.lean' --glob '!CompilationJson.lean'; then exit 1; fi

check-claim-settlement-replay: build-examples
    timeout --signal=TERM --kill-after=3s 120s lake env lean -M 2048 -T 10000000 --run Examples/Manifests.lean catalog claim-settlement-claims claim-settlement-banking claim-settlement-handoff > .lake/build/claim-settlement-catalog.json
    cargo run --locked --quiet -p cedar-poo-bridge --manifest-path Cargo.toml -- replay-catalog < .lake/build/claim-settlement-catalog.json > .lake/build/claim-settlement-receipts.json
    jq -e 'length == 3 and (."claim-settlement-handoff".scenarios | length) == 14 and ([."claim-settlement-handoff".scenarios[] | select(.admitted) | .name] == ["ready"])' .lake/build/claim-settlement-receipts.json > /dev/null
