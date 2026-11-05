// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: eu-individual-claims
forbid(
  principal is AgentCore::OAuthUser,
  action in [AgentCore::Action::"lakehouse-mcp-target___query_claims",AgentCore::Action::"lakehouse-mcp-target___get_claim_details"],
  resource == AgentCore::Gateway::"lakehouse-gateway"
) when {
  (context.input has geography) && (context.input.geography == "EU")
};

// POO policy ID: gateway-baseline
permit(
  principal is AgentCore::OAuthUser,
  action,
  resource == AgentCore::Gateway::"lakehouse-gateway"
);

// POO policy ID: policyholder-summary
forbid(
  principal is AgentCore::OAuthUser,
  action == AgentCore::Action::"lakehouse-mcp-target___get_claims_summary",
  resource == AgentCore::Gateway::"lakehouse-gateway"
) when {
  principal.hasTag("cognito:groups") && (principal.getTag("cognito:groups") like "*policyholders*")
};

// POO policy ID: restricted-geography
forbid(
  principal is AgentCore::OAuthUser,
  action in [AgentCore::Action::"lakehouse-mcp-target___query_claims",AgentCore::Action::"lakehouse-mcp-target___get_claim_details",AgentCore::Action::"lakehouse-mcp-target___get_claims_summary",AgentCore::Action::"lakehouse-mcp-target___query_login_audit",AgentCore::Action::"lakehouse-mcp-target___text_to_sql"],
  resource == AgentCore::Gateway::"lakehouse-gateway"
) when {
  (context.input has geography) && (context.input.geography == "RESTRICTED")
};
