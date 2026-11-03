// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: no-self-approval
forbid(
  principal in Role::"Approver",
  action == Action::"approve",
  resource is PurchaseOrder
) when {
  principal == resource.requester
};

// POO policy ID: operations-approval
permit(
  principal in Role::"Approver",
  action == Action::"approve",
  resource in OrderGroup::"Operations"
) when {
  context.amount.greaterThan(decimal("0.0000")) && context.amount.lessThanOrEqual(resource.limit) && ((context.viaAgent has operator) && ((context.viaAgent has enabled) && ((context.viaAgent.operator == principal) && context.viaAgent.enabled)))
};

// POO policy ID: revoke-purchasing-bot
forbid(
  principal in Role::"Approver",
  action == Action::"approve",
  resource in OrderGroup::"Operations"
) when {
  context.viaAgent == Agent::"purchasing-bot"
};
