import Tests.Governance.AuthorizationDeltaFormula
import Tests.Governance.AuthorizationDeltaDirect

/-!
Keep the trust boundary of the ticket-sharing proof visible to the build.
The exact-query allowlist is pinned to this Cedar/Lean fixture; changing the
query or its computation certificates requires reviewing the new dependencies.
-/

open Lean Elab Command

private def standardAxioms : List String :=
  ["propext", "Classical.choice", "Quot.sound"]

private def exactQueryAxioms : List String := standardAxioms ++
  [ "CedarPooSpec.AuthorizationDeltaFixture.after._native.native_decide.ax_1"
  , "CedarPooSpec.AuthorizationDeltaFixture.asserts._native.native_decide.ax_1"
  , "CedarPooSpec.AuthorizationDeltaFixture.before._native.native_decide.ax_1"
  , "CedarPooSpec.AuthorizationDeltaFixture.exactQueryShape._native.native_decide.ax_1_1"
  , "CedarPooSpec.TicketSharingExample.posturePolicies._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.publishedPolicies._native.native_decide.ax_1"
  ]

private def policyBodyAxioms : List String := exactQueryAxioms ++
  [ "CedarPooSpec.AuthorizationDeltaFixture.exactQuery._native.native_decide.ax_1_1"
  , "CedarPooSpec.AuthorizationDeltaFixture.schemaWF._native.native_decide.ax_1_1"
  , "CedarPooSpec.AuthorizationDeltaFixture.typecheckedAfter._native.native_decide.ax_1_1"
  , "CedarPooSpec.AuthorizationDeltaFixture.typecheckedBefore._native.native_decide.ax_1_1"
  , "_private.Cedar.Data.Int64.0.Int64.toInt_neg_of_not_ge_zero._native.native_decide.ax_1_2"
  , "_private.Cedar.Data.Int64.0.Int64.toInt_nonneg_of_ge_zero._native.native_decide.ax_1_1"
  , "_private.Cedar.Thm.SymCC.Data.Ext.0.Cedar.Thm.msPerDay_eq._native.native_decide.ax_1_1"
  , "_private.Cedar.Thm.SymCC.Data.Ext.0.Cedar.Thm.msPerDay_toInt._native.native_decide.ax_1_1"
  , "_private.Cedar.Thm.SymCC.Data.Ext.0.Cedar.Thm.toDate_eq_smod._native.native_decide.ax_1_6"
  , "_private.Cedar.Thm.SymCC.Data.Ext.0.Cedar.Thm.toDate_eq_smod._native.native_decide.ax_1_8"
  , "_private.Cedar.Thm.SymCC.Data.Ext.0.Cedar.Thm.toInt_div_msPerDay._native.native_decide.ax_1_1"
  , "_private.Cedar.Thm.SymCC.Data.Ext.0.Cedar.Thm.toInt_div_msPerDay._native.native_decide.ax_1_3"
  , "_private.Cedar.Thm.SymCC.Data.Ext.0.Cedar.Thm.toInt_div_msPerDay._native.native_decide.ax_1_6"
  ]

private def revisionAxioms : List String := policyBodyAxioms ++
  [ "CedarPooSpec.TicketSharingExample.model._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.policyRevision._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.policyRevisionBodies._native.native_decide.ax_1_1"
  , "CedarPooSpec.TicketSharingExample.postureReconciliation._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.revokedPolicies._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.revokedReconciliation._native.native_decide.ax_1"
  ]

private def directRevisionAxioms : List String := standardAxioms ++
  [ "CedarPooSpec.TicketSharingExample.model._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.policyRevision._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.policyRevisionBodies._native.native_decide.ax_1_1"
  , "CedarPooSpec.TicketSharingExample.posturePolicies._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.postureReconciliation._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.publishedPolicies._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.revokedPolicies._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.revokedReconciliation._native.native_decide.ax_1"
  ]

private def directPolicyAxioms : List String := standardAxioms ++
  [ "CedarPooSpec.TicketSharingExample.posturePolicies._native.native_decide.ax_1"
  , "CedarPooSpec.TicketSharingExample.publishedPolicies._native.native_decide.ax_1"
  ]

private def sameNames (actual : Array Name) (expected : List String) : Bool :=
  actual.size == expected.length && actual.toList.all (expected.contains ∘ toString)

run_cmd do
  let core ← collectAxioms
    ``CedarPooSpec.Authorization.Delta.BooleanCore.unsatOfShapeAndWellFormedAtoms
  unless sameNames core standardAxioms do
    throwError "Boolean core axiom boundary changed: {core}"

  let exact ← collectAxioms ``CedarPooSpec.AuthorizationDeltaFixture.exactUnsat
  unless sameNames exact exactQueryAxioms do
    throwError "Ticket-sharing exact-query axiom boundary changed: {exact}"

  let bodies ← collectAxioms
    ``CedarPooSpec.AuthorizationDeltaFixture.noGainForValidatedPolicyBodies
  unless sameNames bodies policyBodyAxioms do
    throwError "Direct policy-body theorem axiom boundary changed: {bodies}"

  let revision ← collectAxioms
    ``CedarPooSpec.AuthorizationDeltaFixture.noGainForValidatedTicketSharing
  unless sameNames revision revisionAxioms do
    throwError "C4 ticket-sharing theorem axiom boundary changed: {revision}"

  let direct ← collectAxioms
    ``CedarPooSpec.AuthorizationDeltaDirect.noErrorFreeAllowGain
  unless sameNames direct directPolicyAxioms do
    throwError "Direct linked-policy theorem axiom boundary changed: {direct}"

  let directRevision ← collectAxioms
    ``CedarPooSpec.AuthorizationDeltaDirect.noErrorFreeAllowGainForRevision
  unless sameNames directRevision directRevisionAxioms do
    throwError "Direct C4 theorem axiom boundary changed: {directRevision}"
