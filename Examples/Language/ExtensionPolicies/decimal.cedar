// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: decimal-functions
permit(
  principal == User::"alice",
  action == Action::"view",
  resource == Document::"doc"
) when {
  (context.value == decimal("1.2500")) && (decimal("1.2500").lessThan(decimal("2.0000")) && (decimal("2.0000").lessThanOrEqual(decimal("2.0000")) && (decimal("2.0000").greaterThan(decimal("1.2500")) && (decimal("2.0000").greaterThanOrEqual(decimal("2.0000")) && true))))
};
