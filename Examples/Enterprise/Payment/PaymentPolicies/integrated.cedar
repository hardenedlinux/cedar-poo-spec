// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: block-frozen-payment
forbid(
  principal,
  action == Action::"release",
  resource in PaymentGroup::"Operations"
) when {
  resource.blocked
};

// POO policy ID: controller-release
permit(
  principal in Role::"Controller",
  action == Action::"release",
  resource in PaymentGroup::"Operations"
) when {
  resource.matched && (resource.amount.lessThanOrEqual(decimal("500.0000")) || (principal in Role::"SeniorController"))
};

// POO policy ID: prepare-matched-payment
permit(
  principal in Role::"Clerk",
  action == Action::"prepare",
  resource in PaymentGroup::"Operations"
) when {
  (principal == resource.preparedBy) && (resource.matched && resource.amount.greaterThan(decimal("0.0000")))
};

// POO policy ID: separate-preparer-and-releaser
forbid(
  principal,
  action == Action::"release",
  resource in PaymentGroup::"Operations"
) when {
  principal == resource.preparedBy
};
