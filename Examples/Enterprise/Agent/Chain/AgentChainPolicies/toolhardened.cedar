// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: agent-tool
permit(
  principal == Agent::"data-bot",
  action == Action::"invoke",
  resource == Tool::"delete-records"
) when {
  (3 <= principal.trust) && ((principal.namespace == "data") && (principal.stage == "production"))
};
