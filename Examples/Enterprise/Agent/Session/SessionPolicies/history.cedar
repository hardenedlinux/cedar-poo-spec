// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: agent-read
permit(
  principal == Agent::"research-agent",
  action == Action::"read",
  resource
) when {
  true
};

// POO policy ID: agent-send
permit(
  principal == Agent::"research-agent",
  action == Action::"send",
  resource
) when {
  true
};

// POO policy ID: read-then-egress
forbid(
  principal == Agent::"research-agent",
  action == Action::"send",
  resource
) when {
  context.sensitiveSeen && resource.external
};
