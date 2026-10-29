set shell := ["sh", "-eu", "-c"]
export CARGO_TARGET_DIR := "rust/target"

# Example recipes follow the source publisher or project area.
mod example 'Examples/Justfile'
import 'Tests/Conformance.just'
import 'Tests/Manifests.just'
import 'Tests/Artifacts.just'
import 'Benchmarks/Justfile'

default:
    @just --list

update:
    lake update

sync: update
    just check

# Inspect the public module inventory of the exact LeanPOO revision in Lake.
lean-poo-api:
    @rg -n '^import LeanPoo\.' .lake/packages/LeanPoo/LeanPoo.lean

# Search that same revision by declaration name or API term.
lean-poo-api-find query:
    @rg -n -i --glob '*.lean' -e {{quote(query)}} .lake/packages/LeanPoo/LeanPoo

build:
    lake build CedarPooSpec

build-examples: build
    lake build Examples

build-productions: check-lean-layers build
    lake build Productions

check-docs:
    emacs --batch -Q --eval '(progn (require (quote org-element)) (dolist (file (append (list "README.org") (directory-files-recursively "CedarPooSpec" "\\.org$") (directory-files-recursively "docs" "\\.org$") (directory-files-recursively "Examples" "\\.org$") (directory-files-recursively "Productions" "\\.org$") (directory-files-recursively "rust" "\\.org$") (directory-files-recursively "Tests" "\\.org$") (directory-files-recursively "Benchmarks" "\\.org$"))) (with-temp-buffer (insert-file-contents file) (org-mode) (org-element-parse-buffer))) (princ "ORG-OK"))'

check: check-functional-consumers check-tests check-docs
    just check-conformance
    just bench-functional-catalog
    just bench-functional-native
    just check-policy-reuse
    just example governance attested-views
    just check-cedar-language
    just check-mission-comparison
    just example aws financial-services lakehouse
    just example aws financial-services multi-account-banking
    just example aws financial-services claim-settlement
    just example aws financial-services reconciliation
    just example aws agentic-platform expense
    just example enterprise agent cross-agent-egress
    just example enterprise agent department-synthesis
    just example health prior-authorization
    just example health prior-authorization-internal-channels
    just example health pseudonymization
    just example health multi-hospital-ai
    just example health model-stewardship
    just example cloud pipeline-google-threat
    just example cloud pipeline-google-deployment
    just example cloud data-protection-google-sdp
    just example health my-health-record
    just example health australian-emr
    just example health united-states-payer
    just check-authorization-delta-proof

# Lean feedback without running every Cedar/Rust scenario.
check-quick:
    lake build CedarPooSpec Tests

check-lean: check-functional-consumers check-tests check-authorization-delta-proof check-policy-reuse

check-lean-layers:
    uv run --project python --package cedar-poo-py-test --locked cedar-poo-py-test check-lean-layers
