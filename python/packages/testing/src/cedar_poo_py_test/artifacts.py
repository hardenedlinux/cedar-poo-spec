"""Shared manifest-to-artifact plan for generation and conformance."""

from pathlib import Path

from cedar_poo_py_test.process import RustBridge


ARTIFACTS = (
    ('Examples/Governance/Policies', 'ticket-sharing-manifest.json'),
    ('Examples/Governance/AttestedPolicies', 'attested-manifest.json'),
    ('Examples/Health/Policies', 'clinical-manifest.json'),
    ('Examples/Health/WearablePolicies', 'wearable-triage-manifest.json'),
    ('Examples/Language/Policies', 'scope-pattern-manifest.json'),
    ('Examples/Governance/NetworkPolicies', 'network-manifest.json'),
    ('Examples/Governance/CountryPolicies', 'country-approval-manifest.json'),
    ('Examples/Enterprise/Procurement/Policies', 'purchase-approval-manifest.json'),
    ('Examples/Enterprise/Procurement/DelegatedPolicies', 'delegated-approval-manifest.json'),
    ('Examples/Enterprise/Payment/PaymentPolicies', 'payment-release-manifest.json'),
    ('Examples/Enterprise/Agent/Delegation/AgentPolicies', 'agent-delegation-manifest.json'),
    ('Examples/Enterprise/Agent/Chain/AgentChainPolicies', 'agent-chain-manifest.json'),
    ('Examples/Enterprise/Agent/Payment/AgentPaymentPolicies', 'agent-payment-manifest.json'),
    ('Examples/Enterprise/Agent/DataFlow/AgentDataFlowPolicies', 'agent-data-flow-manifest.json'),
    ('Examples/Enterprise/Agent/Session/SessionPolicies', 'bounded-session-manifest.json'),
    ('Examples/Enterprise/Agent/Fanout/FanoutPolicies', 'shared-budget-manifest.json'),
    ('Examples/Enterprise/Vehicle/Uptane/SupplierTransitionPolicies', 'supplier-transition-manifest.json'),
    ('Examples/Enterprise/Vehicle/VLA/CommandPolicies', 'vla-command-manifest.json'),
    ('Examples/Enterprise/Vehicle/Mission/MissionPolicies', 'mission-successor-manifest.json'),
    ('Examples/Language/ExtensionPolicies', 'extension-coverage-manifest.json'),
    ('Examples/Scenarios/TenantDevicePolicies', 'tenant-device-manifest.json'),
)


def run(repository: Path, operation: str) -> None:
    if operation not in {"emit", "check-artifacts"}:
        raise ValueError(f"unsupported artifact operation: {operation}")
    repository = repository.resolve()
    bridge = RustBridge(repository)
    for directory, manifest in ARTIFACTS:
        bridge.run(
            operation,
            arguments=(directory,),
            input_file=repository / ".lake/build" / manifest,
        )
    print(f"{operation}: {len(ARTIFACTS)} artifact sets")
