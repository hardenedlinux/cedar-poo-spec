// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: origin-user
permit(
  principal == Agent::"data-bot",
  action == Action::"verify-origin",
  resource == Tool::"delete-records"
) when {
  (context.origin in Role::"Admin") && (context.origin.mfa && (context.depth <= 2))
};

// POO policy ID: revoke-admin-origin
forbid(
  principal == Agent::"data-bot",
  action == Action::"verify-origin",
  resource == Tool::"delete-records"
) when {
  context.origin == User::"admin"
};
