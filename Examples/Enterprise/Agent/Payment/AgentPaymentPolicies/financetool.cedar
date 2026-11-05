// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: finance-agent-tool
permit(
  principal == Agent::"finance-bot",
  action == Action::"invoke",
  resource == Tool::"process-payment"
) when {
  (3 <= principal.trust) && ((principal.namespace == "payments") && (principal.stage == "production"))
};
