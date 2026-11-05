// Same Lean-exported acquisition graph; no malware, chain codec or EVM model.
module wallet_replay {
  import attackers_capabilities.* from "../attackers/Capabilities"
  const Initial: Set[str]
  const Isolated: Set[str]
  const Goals: Set[str]
  const Rules: Set[{needs: Set[str], grants: str}]
  type State = { known: Set[str], countermodel: bool, legitimate: bool, paused: bool,
    queued: bool, settled: bool, delegationIssued: bool, delegated: bool,
    clearPending: bool, cleared: bool, unknown: bool, intents: int, uses: int, unsafeUse: bool }
  var r: State
  pure def initial(prior: bool, countermodel: bool, legitimate: bool): State = {
    known: if(legitimate) Initial.union(Set("signerCredential","signerNetwork")) else Initial,
    countermodel: countermodel, legitimate: legitimate, paused: false,
    queued: prior, settled: false, delegationIssued: false, delegated: prior,
    clearPending: false, cleared: false, unknown: prior, intents: 0, uses: 0, unsafeUse: false }
  action init = { nondet prior = Set(false,true).oneOf()
    nondet legitimate = Set(false,true).oneOf()
    r' = initial(prior,false,legitimate) }
  action initClean = r' = initial(false,false,false)
  action initPrior = r' = initial(true,false,false)
  action initLegitimate = r' = initial(false,false,true)
  action initCounter = r' = initial(false,true,false)
  action acquireCap(cap: str): bool = if(not(r.known.contains(cap)) and canLearn(r.known,Rules,cap))
    r' = r.with("known",r.known.union(Set(cap))) else r' = r
  action acquire = { nondet cap = Rules.map(rule=>rule.grants).oneOf()
    acquireCap(cap) }
  action path = acquireCap("internalAI").then(acquireCap("engineerAEndpoint"))
    .then(acquireCap("engineerCEndpoint")).then(acquireCap("deploymentToken"))
    .then(acquireCap("container")).then(acquireCap("signerNetwork"))
  action attempt(kind: int): bool = if(r.known.contains("signerNetwork") and r.intents < 4 and
      (if(r.countermodel) r.known.contains("deploymentToken") else
       r.known.contains("signerCredential") and kind==0 and not(r.paused) and
       not(r.delegated) and not(r.queued) and not(r.unknown)))
    r' = r.with("intents",r.intents+1).with("queued",r.queued or kind==0)
      .with("unknown",r.unknown or not(r.countermodel))
      .with("delegationIssued",r.delegationIssued or kind==1)
    else r' = r
  action request = { nondet kind = Set(0,1).oneOf()
    attempt(kind) }
  action confirmDelegation = if(r.delegationIssued and not(r.cleared))
    r' = r.with("delegated",true) else r' = r
  action pause = r' = r.with("paused",true)
  action settle = if(r.queued) r' = r.with("settled",true).with("queued",false) else r' = r
  action delegatedUse = if(r.delegated and r.uses < 2)
    r' = r.with("uses",r.uses+1).with("unsafeUse",r.unsafeUse or r.cleared) else r' = r
  action submitClear = if(r.paused and r.delegated)
    r' = r.with("clearPending",true) else r' = r
  action observeClear = if(r.clearPending)
    r' = r.with("delegated",false).with("cleared",true) else r' = r
  action closeAccess = r' = r.with("known",Set()).with("paused",true)
  action recover = r' = r
  action step = any { acquire, request, confirmDelegation, pause, settle,
    delegatedUse, submitClear, observeClear, closeAccess, recover }
  val isolation = r.legitimate or Isolated.intersect(r.known)==Set()
  val safety = isolation and not(r.unsafeUse) and (r.countermodel or (if(r.legitimate) r.intents<=1 else r.intents==0)) and
    (not(r.cleared) or (not(r.delegated) and r.paused))
  // These are deliberately FALSE claims about the correct containment model.
  val falseCancelClaim = not(r.paused) or not(r.settled)
  val falseRevokeClaim = not(r.paused) or not(r.delegated)
  action cleanCheck = all { assert(r.intents==0), assert(safety), r'=r }
  action priorSettled = all { assert(r.paused), assert(r.settled), assert(r.intents==0), assert(safety), r'=r }
  action priorUsed = all { assert(r.paused), assert(r.uses==1), assert(r.intents==0), assert(safety), r'=r }
  action clearedCheck = all { assert(r.cleared), assert(not(r.delegated)), assert(r.uses==1), assert(safety), r'=r }
  action stillDelegated = all { assert(r.delegated), assert(not(r.cleared)), r'=r }
  action counterCheck = all { assert(r.intents==2), assert(r.uses==1), assert(r.settled), assert(isolation), r'=r }
  action legitimateCheck = all { assert(r.intents==1), assert(r.unknown), assert(safety), r'=r }
  run legitimateTransferTest = initLegitimate.then(attempt(0)).then(attempt(0)).then(legitimateCheck)
  run guardedCleanTest = initClean.then(path).then(attempt(0)).then(attempt(1)).then(pause).then(cleanCheck)
  run bypassCountermodelTest = initCounter.then(path).then(attempt(0)).then(attempt(1))
    .then(confirmDelegation).then(pause).then(delegatedUse).then(settle).then(counterCheck)
  run lateSettlementTest = initPrior.then(pause).then(settle).then(priorSettled)
  run existingDelegationTest = initPrior.then(pause).then(delegatedUse).then(priorUsed)
  run clearedQueueStillSettlesTest = initPrior.then(pause).then(submitClear).then(observeClear).then(settle).then(priorSettled)
  run clearBlocksNewDelegatedUseTest = initPrior.then(pause).then(delegatedUse).then(submitClear)
    .then(observeClear).then(delegatedUse).then(clearedCheck)
  run clearingRequiresPauseTest = initPrior.then(submitClear).then(observeClear).then(stillDelegated)
  run recoveryDoesNotResumeTest = initPrior.then(pause).then(submitClear).then(observeClear)
    .then(recover).then(attempt(0)).then(cleanCheck)
  run isolatedKeyTest = initClean.then(path).then(acquireCap("signerCredential")).then(cleanCheck)
}
