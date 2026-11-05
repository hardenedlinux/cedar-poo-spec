// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: alice-ticket-a
permit(
  principal == User::"alice",
  action == Action::"read",
  resource == Ticket::"ticket-a"
) when {
  (resource.status == "OPEN") && context.deviceTrusted
};

// POO policy ID: bob-ticket-a
permit(
  principal == User::"bob",
  action == Action::"read",
  resource == Ticket::"ticket-a"
) when {
  resource.status == "OPEN"
};

// POO policy ID: bob-ticket-b
permit(
  principal == User::"bob",
  action == Action::"read",
  resource == Ticket::"ticket-b"
) when {
  (resource.status == "OPEN") && context.deviceTrusted
};
