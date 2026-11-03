// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: new-director-assignment
permit(
  principal == DirectorService::"oem-director",
  action == Action::"assign-target",
  resource
) when {
  context.snapshotRetainsRevocation && (context.metadataAuthenticated && ((!resource.retiredSupplier) && resource.compatible))
};

// POO policy ID: new-image-delegation
permit(
  principal == Supplier::"replacement-tier-1",
  action == Action::"publish-image",
  resource
) when {
  context.delegationValid && (context.metadataAuthenticated && ((!resource.retiredSupplier) && resource.compatible))
};

// POO policy ID: primary-version-manifest
permit(
  principal == PrimaryECU::"vehicle-primary",
  action == Action::"submit-manifest",
  resource
) when {
  context.manifestSignatureValid
};
