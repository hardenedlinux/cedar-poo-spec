// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: legacy-subscription
permit(
  principal,
  action == Action::"query",
  resource
) when {
  context.subscriptionActive
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
  (principal.project == resource.project) && context.subscriptionActive
};
