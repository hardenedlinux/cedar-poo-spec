// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: break-glass
permit(
  principal,
  action == Action::"read",
  resource
) when {
  context.breakGlassGranted && (context.sessionActive && (context.patientUnableToConsent && (context.treatmentPurpose && (context.sessionPatient == resource.patient)))) && context.deviceTrusted
};

// POO policy ID: restricted-record
forbid(
  principal,
  action == Action::"read",
  resource
) when {
  resource.restricted && (!(context.breakGlassGranted && (context.sessionActive && (context.patientUnableToConsent && (context.treatmentPurpose && (context.sessionPatient == resource.patient))))))
};

// POO policy ID: routine-read
permit(
  principal,
  action == Action::"read",
  resource
) when {
  (principal.facility == resource.facility) && context.deviceTrusted
};

// POO policy ID: untrusted-device-or-identity
forbid(
  principal,
  action == Action::"read",
  resource
) when {
  (!context.deviceTrusted) || (!context.strongAuth)
};
