// Finite protocol abstraction instantiated from @deterministic-engineering/quint-models.
// Trusted bits summarize native interpreters; no cryptography, real CAS, codec correctness or Lean refinement is claimed.
module wallet_host {
  import state_rollback(MaxSends = 1).* from "@deterministic-engineering/quint-models/threat/execution/state-rollback/StateRollback"
}
