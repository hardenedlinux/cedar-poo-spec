// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: agent-payment
permit(
  principal == Agent::"finance-bot",
  action == Action::"transfer",
  resource
) when {
  true
};

// POO policy ID: invalid-payment-amount
forbid(
  principal == Agent::"finance-bot",
  action == Action::"transfer",
  resource
) when {
  !(context.amount.greaterThan(decimal("0.0000")) && context.amount.lessThanOrEqual(decimal("100.0000")))
};
