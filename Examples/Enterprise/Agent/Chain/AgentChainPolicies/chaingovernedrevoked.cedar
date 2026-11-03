// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: agent-delegation
permit(
  principal,
  action == Action::"delegate",
  resource
) when {
  (context.depth <= 3) && resource.capabilities.containsAll(context.requestedCaps) && ((3 <= principal.trust) && principal.capabilities.contains("delegate"))
};

// POO policy ID: origin-user
permit(
  principal == Agent::"data-bot",
  action == Action::"verify-origin",
  resource == Tool::"delete-records"
) when {
  (context.origin in Role::"Admin") && context.origin.mfa && (context.depth <= 3)
};

// POO policy ID: revoke-routing-to-compliance
forbid(
  principal == Agent::"routing-bot",
  action == Action::"delegate",
  resource == Agent::"compliance-bot"
) when {
  true
};
