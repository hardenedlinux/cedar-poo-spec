// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: legacy-read
permit(
  principal,
  action == Action::"read",
  resource
);

// POO policy ID: tenant-read
permit(
  principal,
  action == Action::"read",
  resource
) when {
  (principal.tenant == resource.tenant) && context.deviceTrusted
};
