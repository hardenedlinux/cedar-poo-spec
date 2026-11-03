// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: break-glass
permit(
  principal,
  action == Action::"read",
  resource
) when {
  context.breakGlassGranted && (context.sessionPatient == resource.patient)
};

// POO policy ID: legacy-broad-read
permit(
  principal,
  action == Action::"read",
  resource
) when {
  true
};

// POO policy ID: routine-read
permit(
  principal,
  action == Action::"read",
  resource
) when {
  (principal.facility == resource.facility) && context.deviceTrusted
};
