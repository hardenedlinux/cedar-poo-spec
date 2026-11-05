// Finite abstraction of the composed Lean wallet containment boundary.
// Matching/finality bits are trusted Host observations, not EVM/crypto proofs.
module wallet_containment {
  type Containment = { delegated: bool, paused: bool, revoked: bool,
    everPaused: bool, clearPending: bool, cleared: bool, witness: bool,
    burned: bool, signatures: int, unsafe: bool }
  var c: Containment
  pure def initial(delegated: bool): Containment = {
    delegated: delegated, paused: false, revoked: false, everPaused: false,
    clearPending: false, cleared: false, witness: false,
    burned: false, signatures: 0, unsafe: false }
  action init = { nondet delegated = Set(false, true).oneOf()
    c' = initial(delegated) }
  action initClean = c' = initial(false)
  action initExposed = c' = initial(true)

  action attempt(bound: bool): bool = if (bound and not(c.delegated) and
      not(c.paused) and not(c.revoked) and not(c.clearPending) and not(c.burned) and c.signatures < 2)
    c' = c.with("burned", true).with("signatures", c.signatures + 1)
      .with("unsafe", c.unsafe or c.everPaused or c.delegated or c.signatures > 0)
    else c' = c
  action sign = { nondet bound = Set(false, true).oneOf()
    attempt(bound) }
  action pause = c' = c.with("paused", true).with("revoked", true).with("everPaused", true)
  action recoverAs(liveRevoked: bool): bool =
    c' = c.with("revoked", c.revoked or liveRevoked or c.paused)
  action recover = { nondet live = Set(false, true).oneOf()
    recoverAs(live) }
  action submitClear = if(c.paused and c.revoked and c.delegated)
    c' = c.with("clearPending", true) else c' = c
  action observeAs(wallet: bool, network: bool, nonce: bool,
      verified: bool, finalized: bool, noCode: bool): bool =
    if(c.clearPending and wallet and network and nonce and verified and finalized and noCode)
      c' = c.with("delegated", false).with("cleared", true).with("witness", true)
    else c' = c
  action observe = { nondet wallet = Set(false, true).oneOf()
    nondet network = Set(false, true).oneOf()
    nondet nonce = Set(false, true).oneOf()
    nondet verified = Set(false, true).oneOf()
    nondet finalized = Set(false, true).oneOf()
    nondet noCode = Set(false, true).oneOf()
    observeAs(wallet, network, nonce, verified, finalized, noCode) }

  val signatureSafety = not(c.unsafe) and c.signatures <= 1
  val clearingTruth = not(c.cleared) or (not(c.delegated) and c.witness)
  val pauseRetention = not(c.everPaused) or (c.paused and c.revoked)
  val safety = signatureSafety and clearingTruth and pauseRetention and
    (c.signatures == 0 or c.burned)
  action step = any { sign, pause, recover, submitClear, observe }

  // Explicit countermodels do not replace or weaken the hardened step.
  action brokenRecover = c' = c.with("paused", false).with("revoked", false)
  action falseClear = c' = c.with("delegated", false).with("cleared", true)
  action stepBrokenRecovery = any { step, brokenRecover }
  action stepFalseClear = any { step, falseClear }
  action checkSafe = all { assert(safety), c' = c }
  action checkBlocked = all { assert(c.signatures == 0), assert(safety), c' = c }
  action checkDelegated = all { assert(c.delegated), assert(safety), c' = c }
  action checkClearedPaused = all { assert(not(c.delegated)), assert(c.paused), c' = c }
  action checkUnsafe = all { assert(not(safety)), c' = c }

  run normalTransferTest = initClean.then(attempt(true)).then(checkSafe)
  run delegatedQuarantineTest = initExposed.then(attempt(true)).then(checkBlocked)
  run pauseBlocksTest = initClean.then(pause).then(attempt(true)).then(checkBlocked)
  run restartPreservesPauseTest = initClean.then(pause).then(recoverAs(false))
    .then(attempt(true)).then(checkBlocked)
  run clearingRequiresPauseTest = initExposed.then(submitClear)
    .then(observeAs(true,true,true,true,true,true)).then(checkDelegated)
  run unfinalizedClearTest = initExposed.then(pause).then(submitClear)
    .then(observeAs(true,true,true,true,false,true)).then(checkDelegated)
  run foreignClearTest = initExposed.then(pause).then(submitClear)
    .then(observeAs(false,true,true,true,true,true))
    .then(observeAs(true,true,false,true,true,true)).then(checkDelegated)
  run clearedDoesNotResumeTest = initExposed.then(pause).then(submitClear)
    .then(observeAs(true,true,true,true,true,true)).then(checkClearedPaused)
    .then(recoverAs(false)).then(attempt(true)).then(checkBlocked)
  run falseClearingCountermodelTest = initExposed.then(falseClear).then(checkUnsafe)
}
