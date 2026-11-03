// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: attested-platform
forbid(
  principal,
  action == Action::"query",
  resource
) when {
  !(context.attestationVerified && (context.attestationFresh && (context.measurement == resource.measurement)))
};

// POO policy ID: network-boundary
forbid(
  principal,
  action == Action::"query",
  resource
) when {
  !context.sourceIp.isInRange(ip("10.20.0.0/16"))
};

// POO policy ID: owner-approval
forbid(
  principal,
  action == Action::"query",
  resource
) when {
  !(context.ownerApproved && (!(principal.operator == context.approver)))
};

// POO policy ID: project-subscription
permit(
  principal,
  action == Action::"query",
  resource
) when {
  (principal.project == resource.project) && (context.subscriptionActive && (context.purpose == "analytics"))
};

// POO policy ID: region-boundary
forbid(
  principal,
  action == Action::"query",
  resource
) when {
  !(context.region == resource.region)
};
