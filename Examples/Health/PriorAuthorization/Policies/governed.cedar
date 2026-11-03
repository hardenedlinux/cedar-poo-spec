// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: administrative-fields-missing
forbid(
  principal,
  action == Action::"submit-prior-authorization",
  resource == PayerEndpoint::"payer-a"
) when {
  !(context.codePresent && (context.durationPresent && context.followUpPresent))
};

// POO policy ID: billing-evidence-missing
forbid(
  principal,
  action == Action::"submit-prior-authorization",
  resource == PayerEndpoint::"payer-a"
) when {
  !context.billingSeen
};

// POO policy ID: clinical-evidence-missing
forbid(
  principal,
  action == Action::"submit-prior-authorization",
  resource == PayerEndpoint::"payer-a"
) when {
  !context.clinicalSeen
};

// POO policy ID: delegation-expired
forbid(
  principal,
  action in [Action::"read-clinical",Action::"read-billing",Action::"submit-prior-authorization"],
  resource
) when {
  !context.delegationActive
};

// POO policy ID: patient-misbinding
forbid(
  principal,
  action in [Action::"read-clinical",Action::"read-billing"],
  resource
) when {
  !(context.expectedPatient == resource.patient)
};

// POO policy ID: payer-requirements-stale
forbid(
  principal,
  action == Action::"submit-prior-authorization",
  resource == PayerEndpoint::"payer-a"
) when {
  !context.payerRequirementsCurrent
};

// POO policy ID: raw-record-in-draft
forbid(
  principal,
  action == Action::"submit-prior-authorization",
  resource == PayerEndpoint::"payer-a"
) when {
  context.rawRecordIncluded
};

// POO policy ID: read-billing
permit(
  principal,
  action == Action::"read-billing",
  resource
) when {
  (resource.kind == "billing") && ((context.expectedPatient == resource.patient) && context.delegationActive)
};

// POO policy ID: read-clinical
permit(
  principal,
  action == Action::"read-clinical",
  resource
) when {
  (resource.kind == "clinical") && ((context.expectedPatient == resource.patient) && context.delegationActive)
};

// POO policy ID: submit-draft
permit(
  principal,
  action == Action::"submit-prior-authorization",
  resource == PayerEndpoint::"payer-a"
) when {
  context.clinicalSeen && (context.billingSeen && (context.codePresent && (context.durationPresent && (context.followUpPresent && ((!context.rawRecordIncluded) && (context.payerRequirementsCurrent && context.delegationActive))))))
};
