// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: agent-document-read
permit(
  principal == Agent::"knowledge-bot",
  action == Action::"read-document",
  resource
) when {
  (resource.tenant == "acme") && (context.origin in Role::"Admin")
};
