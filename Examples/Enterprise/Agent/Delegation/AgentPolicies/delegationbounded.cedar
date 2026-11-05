// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: agent-delegation
permit(
  principal == Agent::"orchestrator",
  action == Action::"delegate",
  resource == Agent::"data-bot"
) when {
  (context.depth <= 3) && resource.capabilities.containsAll(context.requestedCaps)
};
