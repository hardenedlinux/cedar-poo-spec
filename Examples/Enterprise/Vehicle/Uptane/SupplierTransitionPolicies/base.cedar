// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: old-director-assignment
permit(
  principal == DirectorService::"oem-director",
  action == Action::"assign-target",
  resource
) when {
  context.metadataAuthenticated && (resource.retiredSupplier && resource.compatible)
};

// POO policy ID: old-image-delegation
permit(
  principal == Supplier::"retired-tier-1",
  action == Action::"publish-image",
  resource
) when {
  context.delegationValid && (context.metadataAuthenticated && (resource.retiredSupplier && resource.compatible))
};

// POO policy ID: primary-version-manifest
permit(
  principal == PrimaryECU::"vehicle-primary",
  action == Action::"submit-manifest",
  resource
) when {
  context.manifestSignatureValid
};
