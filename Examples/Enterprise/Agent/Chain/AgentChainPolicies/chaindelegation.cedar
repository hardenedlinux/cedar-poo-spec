// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: agent-delegation
permit(
  principal,
  action == Action::"delegate",
  resource
) when {
  (context.depth <= 3) && resource.capabilities.containsAll(context.requestedCaps) && ((3 <= principal.trust) && principal.capabilities.contains("delegate"))
};
