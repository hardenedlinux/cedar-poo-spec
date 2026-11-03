// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: delegated-send
permit(
  principal,
  action == Action::"send",
  resource == Endpoint::"external-report"
) when {
  (context.localUsed < context.localMax) && (context.sharedUsed < context.sharedMax)
};

// POO policy ID: delegation-shared-budget
forbid(
  principal,
  action == Action::"send",
  resource == Endpoint::"external-report"
) when {
  !(context.sharedUsed < context.sharedMax)
};

// POO policy ID: worker-local-budget
forbid(
  principal,
  action == Action::"send",
  resource == Endpoint::"external-report"
) when {
  !(context.localUsed < context.localMax)
};
