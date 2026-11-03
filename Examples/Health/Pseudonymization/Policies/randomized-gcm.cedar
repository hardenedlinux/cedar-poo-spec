// Generated from Lean-POO. Cedar assigns new IDs when parsing this text.
// POO policy ID: agent-cannot-reidentify
forbid(
  principal,
  action == Action::"reidentify",
  resource
) when {
  principal.kind == "agent"
};

// POO policy ID: no-deterministic-join
forbid(
  principal,
  action == Action::"join",
  resource
) when {
  resource.mode == "aes-gcm"
};

// POO policy ID: owner-approval
forbid(
  principal,
  action == Action::"tokenize",
  resource
) when {
  !context.ownerApproved
};

// POO policy ID: owner-join-approval
forbid(
  principal,
  action == Action::"join",
  resource
) when {
  !context.ownerApproved
};

// POO policy ID: owner-reidentify-approval
forbid(
  principal,
  action == Action::"reidentify",
  resource
) when {
  !context.ownerApproved
};

// POO policy ID: reidentify
permit(
  principal,
  action == Action::"reidentify",
  resource
) when {
  (resource.mode == "aes-gcm") && ((context.targetDataset.mode == resource.mode) && ((context.targetDataset.scope == resource.scope) && ((context.targetDataset.keyDomain == resource.keyDomain) && ((context.targetDataset.tokenKeyVersion == resource.tokenKeyVersion) && (context.targetDataset.transformVersion == resource.transformVersion))))) && (context.keyAuthorized && (context.requestedKeyVersion == resource.tokenKeyVersion)) && ((context.targetDataset == resource) && ((principal.kind == "steward") && (context.reidentifyApproved && context.auditReady)))
};

// POO policy ID: tenant-join-boundary
forbid(
  principal,
  action == Action::"join",
  resource
) when {
  !(principal.tenant == resource.tenant)
};

// POO policy ID: tenant-reidentify-boundary
forbid(
  principal,
  action == Action::"reidentify",
  resource
) when {
  !(principal.tenant == resource.tenant)
};

// POO policy ID: tenant-token-boundary
forbid(
  principal,
  action == Action::"tokenize",
  resource
) when {
  !(principal.tenant == resource.tenant)
};

// POO policy ID: tokenize
permit(
  principal,
  action == Action::"tokenize",
  resource
) when {
  (resource.mode == "aes-gcm") && ((context.targetDataset.mode == resource.mode) && ((context.targetDataset.scope == resource.scope) && ((context.targetDataset.keyDomain == resource.keyDomain) && ((context.targetDataset.tokenKeyVersion == resource.tokenKeyVersion) && (context.targetDataset.transformVersion == resource.transformVersion))))) && (context.keyAuthorized && (context.requestedKeyVersion == resource.tokenKeyVersion)) && ((context.targetDataset == resource) && ((principal.kind == "ingest") && context.ivUnique))
};
