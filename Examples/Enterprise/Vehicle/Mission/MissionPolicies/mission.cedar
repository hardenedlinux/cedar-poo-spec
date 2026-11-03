// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: fallback-handoff
permit(
  principal == MissionPlanner::"untrusted-planner",
  action == Action::"fallback-handoff",
  resource
) when {
  true
};

// POO policy ID: mission-infeasible
forbid(
  principal == MissionPlanner::"untrusted-planner",
  action == Action::"proceed",
  resource
) when {
  !context.successorMissionFeasible
};

// POO policy ID: nominal-route
permit(
  principal == MissionPlanner::"untrusted-planner",
  action == Action::"proceed",
  resource
) when {
  context.routeApproved
};
