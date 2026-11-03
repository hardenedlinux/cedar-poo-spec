// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: analyze-vitals
permit(
  principal,
  action == Action::"analyze",
  resource
) when {
  (resource.category == "vital-signs") && context.treatmentPurpose
};

// POO policy ID: release-alert
permit(
  principal,
  action == Action::"release-alert",
  resource
) when {
  (principal.facility == resource.facility) && context.treatmentPurpose
};
