// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: controller-release
permit(
  principal in Role::"Controller",
  action == Action::"release",
  resource in PaymentGroup::"Operations"
) when {
  true
};

// POO policy ID: matched-release
permit(
  principal,
  action == Action::"release",
  resource in PaymentGroup::"Operations"
) when {
  resource.matched
};

// POO policy ID: prepare-matched-payment
permit(
  principal in Role::"Clerk",
  action == Action::"prepare",
  resource in PaymentGroup::"Operations"
) when {
  (principal == resource.preparedBy) && (resource.matched && resource.amount.greaterThan(decimal("0.0000")))
};
