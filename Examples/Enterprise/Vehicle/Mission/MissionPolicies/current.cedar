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
  context.routeApproved && context.successorPlatformSafe && (context.successorMissionFeasible && ((context.proposalId == context.witnessProposalId) && ((context.missionVersion == context.witnessMissionVersion) && (context.vehicleStateId == context.witnessVehicleStateId)) && ((0 <= context.observedTick) && ((context.observedTick <= context.decisionTick) && ((context.decisionTick - context.observedTick) <= 2)))))
};

// POO policy ID: unbound-successor-witness
forbid(
  principal == MissionPlanner::"untrusted-planner",
  action == Action::"proceed",
  resource
) when {
  !((context.proposalId == context.witnessProposalId) && ((context.missionVersion == context.witnessMissionVersion) && (context.vehicleStateId == context.witnessVehicleStateId)))
};
