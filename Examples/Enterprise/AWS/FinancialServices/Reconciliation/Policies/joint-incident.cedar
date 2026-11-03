// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: recon_correspondence_reads
permit(
  principal,
  action in [AgentCore::Action::"correspondence-search___search_correspondence",AgentCore::Action::"microsoft-graph___listSharedMailboxMessages"],
  resource == AgentCore::Gateway::"recon-egress-gateway"
);

// POO policy ID: recon_directory_reads
permit(
  principal,
  action in [AgentCore::Action::"contacts___list_contacts",AgentCore::Action::"templates___list_templates"],
  resource == AgentCore::Gateway::"recon-egress-gateway"
);

// POO policy ID: recon_knowledge_reads
permit(
  principal,
  action in [AgentCore::Action::"managed-kb___Retrieve"],
  resource == AgentCore::Gateway::"recon-egress-gateway"
);

// POO policy ID: recon_ledger_reads
permit(
  principal,
  action in [AgentCore::Action::"general-ledger___search_ledger",AgentCore::Action::"notices___search_notices"],
  resource == AgentCore::Gateway::"recon-egress-gateway"
);

// POO policy ID: recon_status_platform
permit(
  principal == AgentCore::IamEntity::"recon-bff",
  action == AgentCore::Action::"recon-status___recon_update_status",
  resource == AgentCore::Gateway::"recon-egress-gateway"
);

// POO policy ID: recon_write_gate
permit(
  principal,
  action == AgentCore::Action::"set-draw-status___set_draw_status",
  resource == AgentCore::Gateway::"recon-egress-gateway"
) when {
  (context.input has confidence) && context.input.confidence.greaterThanOrEqual(decimal("90.0"))
};

// POO policy ID: recon_write_human
permit(
  principal == AgentCore::IamEntity::"recon-bff",
  action == AgentCore::Action::"set-draw-status___set_draw_status",
  resource == AgentCore::Gateway::"recon-egress-gateway"
);
