// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: analyze-vitals
permit(
  principal,
  action == Action::"analyze",
  resource
) when {
  (resource.category == "vital-signs") && context.treatmentPurpose && context.modelApproved
};

// POO policy ID: consent-withdrawn
forbid(
  principal,
  action,
  resource
) when {
  !resource.consentActive
};

// POO policy ID: quarantine-monitor-q
forbid(
  principal,
  action,
  resource
) when {
  resource.source == "monitor-q"
};

// POO policy ID: release-alert
permit(
  principal,
  action == Action::"release-alert",
  resource
) when {
  (principal.facility == resource.facility) && context.treatmentPurpose && context.clinicianReviewed
};

// POO policy ID: untrusted-monitor
forbid(
  principal,
  action,
  resource
) when {
  !context.deviceTrusted
};
