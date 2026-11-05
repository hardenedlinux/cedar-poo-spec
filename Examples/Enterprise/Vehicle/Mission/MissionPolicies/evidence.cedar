// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: fallback-handoff
permit(
  principal == MissionPlanner::"untrusted-planner",
  action == Action::"fallback-handoff",
  resource
) when {
  true
};

// POO policy ID: nominal-route
permit(
  principal == MissionPlanner::"untrusted-planner",
  action == Action::"proceed",
  resource
) when {
  context.routeApproved
};

// POO policy ID: unbound-successor-witness
forbid(
  principal == MissionPlanner::"untrusted-planner",
  action == Action::"proceed",
  resource
) when {
  !((context.proposalId == context.witnessProposalId) && ((context.missionVersion == context.witnessMissionVersion) && (context.vehicleStateId == context.witnessVehicleStateId)))
};
