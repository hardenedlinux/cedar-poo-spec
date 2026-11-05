// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: hazard-report
permit(
  principal == DrivingPlanner::"vla-adapter",
  action == Action::"report-hazard",
  resource
) when {
  true
};

// POO policy ID: planner-acceleration
permit(
  principal == DrivingPlanner::"vla-adapter",
  action == Action::"accelerate",
  resource
) when {
  context.routeApproved && (!resource.pedestriansPresent)
};

// POO policy ID: safe-braking
permit(
  principal == DrivingPlanner::"vla-adapter",
  action == Action::"brake",
  resource
) when {
  true
};
