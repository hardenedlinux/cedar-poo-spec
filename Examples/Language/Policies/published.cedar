// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: document-view
permit(
  principal is User,
  action == Action::"view",
  resource is Document
) when {
  (principal.email like "*@example.org") && (principal is User)
};
