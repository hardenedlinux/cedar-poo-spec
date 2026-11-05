// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: tenant-read
permit(
  principal,
  action == Action::"read",
  resource
) when {
  principal.tenant == resource.tenant
};

// POO policy ID: unrestricted-read
permit(
  principal,
  action == Action::"read",
  resource
);
