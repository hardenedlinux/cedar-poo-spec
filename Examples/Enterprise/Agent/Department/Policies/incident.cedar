// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: agent-read
permit(
  principal,
  action == Action::"read",
  resource
) when {
  true
};

// POO policy ID: cross-department-aggregate-egress
forbid(
  principal,
  action == Action::"send",
  resource == Endpoint::"external-report"
) when {
  context.salesSeen && context.financeSeen
};

// POO policy ID: delegated-intent
forbid(
  principal,
  action == Action::"send",
  resource
) when {
  !(context.intent == context.delegatedIntent)
};

// POO policy ID: delegated-send
permit(
  principal,
  action == Action::"send",
  resource == Endpoint::"external-report"
) when {
  (context.localUsed < context.localMax) && (context.sharedUsed < context.sharedMax)
};

// POO policy ID: delegation-egress-freeze
forbid(
  principal,
  action == Action::"send",
  resource == Endpoint::"external-report"
) when {
  true
};

// POO policy ID: delegation-shared-budget
forbid(
  principal,
  action == Action::"send",
  resource == Endpoint::"external-report"
) when {
  !(context.sharedUsed < context.sharedMax)
};

// POO policy ID: expired-delegation
forbid(
  principal,
  action in [Action::"read",Action::"send"],
  resource
) when {
  !context.delegationActive
};

// POO policy ID: finance-owner-boundary
forbid(
  principal,
  action == Action::"read",
  resource == Document::"finance-invoice"
) when {
  (!(context.originDept == "Finance")) && (!(context.originDept == "Joint"))
};

// POO policy ID: read-then-egress
forbid(
  principal,
  action == Action::"send",
  resource
) when {
  context.sensitiveSeen && resource.external
};

// POO policy ID: sales-owner-boundary
forbid(
  principal,
  action == Action::"read",
  resource == Document::"sales-contract"
) when {
  (!(context.originDept == "Sales")) && (!(context.originDept == "Joint"))
};

// POO policy ID: worker-local-budget
forbid(
  principal,
  action == Action::"send",
  resource == Endpoint::"external-report"
) when {
  !(context.localUsed < context.localMax)
};
