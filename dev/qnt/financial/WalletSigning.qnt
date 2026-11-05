// Finite threat exploration using the selected LeanPoo object graph.
// No claim of EVM, consensus, key custody, real concurrency or deployed durability.
module wallet_signing {
  import attackers_capabilities.* from "../attackers/Capabilities"
  import wallet_attackers_profile.* from "../../../.lake/build/wallet-attackers-profile"

  type State = {
    known: Set[str], actor: int, epoch: int, generation: int,
    allowed: bool, revoked: bool, expired: bool,
    prepared: bool, ticketEpoch: int, ticketGeneration: int, caller: int, tx: int,
    burned: bool, unknown: bool, signatures: int, unsafe: bool,
    paused: bool, delegated: bool, clearPending: bool, reportedClear: bool
  }
  var s: State

  pure def initial(actor: int): State = {
    known: if (actor == 0) Initial else Initial.union(Set("signerCredential", "signerNetwork")),
    actor: actor, epoch: 0, generation: 0, allowed: true, revoked: false, expired: false,
    prepared: false, ticketEpoch: 0, ticketGeneration: 0, caller: 0, tx: 0,
    burned: false, unknown: false, signatures: 0, unsafe: false,
    paused: false, delegated: true, clearPending: false, reportedClear: false
  }
  action init = { nondet actor = Set(0, 1).oneOf()
    s' = initial(actor) }
  action initLegitimate = s' = initial(1)
  action initAttacker = s' = initial(0)

  action acquireCap(cap: str): bool = all {
    not(s.known.contains(cap)), canLearn(s.known, Rules, cap),
    s' = s.with("known", s.known.union(Set(cap)))
  }
  action acquire = { nondet cap = Rules.map(rule => rule.grants).oneOf()
    acquireCap(cap)
  }
  action prepareAs(caller: int, tx: int): bool = all {
    not(s.prepared),
    s' = s.with("prepared", true).with("ticketEpoch", s.epoch)
      .with("ticketGeneration", s.generation).with("caller", caller).with("tx", tx)
  }
  action prepare = { nondet caller = Set(0, 1).oneOf()
    nondet tx = Set(0, 1, 2).oneOf()
    prepareAs(caller, tx) }
  action freeze = all { s.allowed, s.epoch < 2, s.generation < 2,
    s' = s.with("allowed", false).with("epoch", s.epoch + 1).with("generation", s.generation + 1) }
  action restore = all { not(s.allowed), s.epoch < 2, s.generation < 2,
    s' = s.with("allowed", true).with("epoch", s.epoch + 1).with("generation", s.generation + 1) }
  action renew = all { s.generation < 2, s' = s.with("generation", s.generation + 1) }
  action revoke = all { not(s.revoked), s' = s.with("revoked", true) }
  action expire = all { not(s.expired), s' = s.with("expired", true) }

  val currentUse = all {
    s.prepared, s.ticketEpoch == s.epoch, s.ticketGeneration == s.generation,
    s.allowed, not(s.revoked), not(s.expired), not(s.unknown), not(s.burned),
    s.caller == 1, s.known.contains("signerCredential"), s.tx == 0
  }
  action emit = all { s.signatures < 2,
    s' = s.with("burned", true).with("unknown", true).with("signatures", s.signatures + 1)
      .with("unsafe", s.unsafe or not(currentUse)) }
  action sign = all { currentUse, emit }
  action outcome = all { s.unknown, s' = s.with("unknown", false) }
  action recover = s' = s // Historical recovery never remints the original grant.
  action pause = all { not(s.paused), s' = s.with("paused", true).with("revoked", true) }
  action submitClear = all { not(s.clearPending), s' = s.with("clearPending", true) }
  action confirmClear = all { s.clearPending, s.delegated,
    s' = s.with("delegated", false).with("reportedClear", true) }

  val signatureSafety = not(s.unsafe) and s.signatures <= 1
  val burnRetention = s.signatures == 0 or s.burned
  val clearingTruth = not(s.reportedClear) or not(s.delegated)
  val isolatedRoots = s.actor == 1 or Isolated.intersect(s.known) == Set()
  val profileInventory = Isolated == Set("signerCredential", "workflowAuthority") and
    Goals == Set("exact-effect", "workload-identity", "deployment-isolation")
  val safety = signatureSafety and burnRetention and clearingTruth and isolatedRoots and profileInventory

  action step = any { acquire, prepare, freeze, restore, renew, revoke, expire,
    sign, outcome, recover, pause, submitClear, confirmClear }

  // Deliberately broken alternatives must produce retained counterexamples.
  action staleSign = all { s.prepared, s.caller == 1, s.tx == 0,
    s.known.contains("signerCredential"), not(s.burned), emit }
  action bypassSign = all { s.prepared, s.known.contains("signerNetwork"), emit }
  action remint = s' = s.with("burned", false).with("unknown", false)
  action falseClear = s' = s.with("paused", true).with("reportedClear", true)
  action stepBypass = any { step, bypassSign }
  action stepStale = any { step, staleSign }
  action stepRemint = any { step, remint }
  action stepFalseClear = any { step, falseClear }

  action checkSafe = all { assert(safety), s' = s }
  action checkUnsafe = all { assert(not(safety)), s' = s }
  action checkDelegated = all { assert(s.delegated), s' = s }

  run deployedTokenBypassTest = initAttacker
    .then(acquireCap("internalAI")).then(acquireCap("engineerAEndpoint"))
    .then(acquireCap("engineerCEndpoint")).then(acquireCap("deploymentToken"))
    .then(acquireCap("container")).then(acquireCap("signerNetwork"))
    .then(prepareAs(0, 1)).then(bypassSign).then(checkUnsafe)
  run validSigningTest = initLegitimate.then(prepareAs(1, 0)).then(sign).then(checkSafe)
  run stalePolicyTest = initLegitimate.then(prepareAs(1, 0)).then(freeze).then(staleSign).then(checkUnsafe)
  run staleGenerationTest = initLegitimate.then(prepareAs(1, 0)).then(renew).then(staleSign).then(checkUnsafe)
  run revokedTest = initLegitimate.then(prepareAs(1, 0)).then(revoke).then(staleSign).then(checkUnsafe)
  run recoveryReplayTest = initLegitimate.then(prepareAs(1, 0)).then(sign).then(remint).then(sign).then(checkUnsafe)
  run localPauseTest = initAttacker.then(pause).then(submitClear).then(checkDelegated)
  run clearingTest = initAttacker.then(pause).then(submitClear).then(confirmClear).then(checkSafe)
  run falseClearingTest = initAttacker.then(falseClear).then(checkUnsafe)
}
