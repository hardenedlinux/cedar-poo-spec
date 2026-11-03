// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: document-view
permit(
  principal is User in Group::"staff",
  action == Action::"view",
  resource is Document in Folder::"public"
) when {
  (principal.email like "*@example.org") && (resource has meta.tag)
};
