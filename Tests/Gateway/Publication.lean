import Tests.Gateway.Counterexamples
import Tests.Gateway.Objects

namespace CedarPooSpec.GatewayTest

#guard currentPublication.isSome
#guard againstCurrent

-- A raw constructor is permitted only when it meets the actual authority's
-- complete postcondition. Its origin is not a Contract-bypass privilege.
#guard (Gateway.prepare model "base" schema context weakenedProfile request "invoke" true).isOk
#guard !(againstCurrent { prepared with profile := weakenedProfile }
    (assessments := [⟨"source", .satisfied⟩]))
#guard !(againstCurrent relabeledPrepared (actualContext := relabeledContext))

-- Keep the claim but substitute a new canonical key: the current publication
-- still rejects a new logical family, even if all candidate labels agree.
def renewedKeyContext : Gateway.Context :=
  { context with scope := { scope with canonicalOperation := "task/new-key" } }
def renewedKeyPrepared : Gateway.Prepared String Bool request :=
  { prepared with context := renewedKeyContext, operationId := ⟨"task/new-key"⟩ }
#guard (authorize renewedKeyPrepared (currentContext := renewedKeyContext)).isOk
#guard !(againstCurrent renewedKeyPrepared (actualContext := renewedKeyContext))

#guard !(againstCurrent { prepared with context := { context with scope := { scope with budgetDomain := "new-budget" } } }
    (actualContext := { context with scope := { scope with budgetDomain := "new-budget" } }))
#guard !(againstCurrent { prepared with context := { context with scope := { scope with historyDomain := "new-history" } } }
    (actualContext := { context with scope := { scope with historyDomain := "new-history" } }))
#guard !(againstCurrent { prepared with context := { context with ownerEpoch := 2 } }
    (actualContext := { context with ownerEpoch := 2 }))

-- Self-selecting a weaker original makes a local Session pass. It does not
-- replace the independently selected current authority used by againstCurrent.
def selfSelectedWeakerPublication :=
  strippedObject.toOption.bind fun object =>
    (Gateway.ProfileObject.openSession weakenedProfile object).toOption.bind fun session =>
      (Gateway.ProfileObject.capturePublication context session).toOption.map fun publication =>
        (Gateway.authorizePublished publication { prepared with profile := weakenedProfile }
          model "invoke" true context [⟨"source", .satisfied⟩] entities).isOk
#guard selfSelectedWeakerPublication == some true
#guard !(againstCurrent { prepared with profile := weakenedProfile }
    (assessments := [⟨"source", .satisfied⟩]))

-- A stronger actual object requires its exact selected requirements.
def strongerPublicationChecks : Option (Bool × Bool) :=
  extendedObject.toOption.bind fun object =>
    (Gateway.ProfileObject.openSession profile object).toOption.bind fun session =>
      (Gateway.ProfileObject.capturePublication context session).toOption.map fun publication =>
        let stale := (Gateway.authorizePublished publication prepared model "invoke" true context checks entities).isOk
        let candidate := { prepared with profile := publication.selected }
        let actualChecks := publication.selected.requiredChecks.map fun name => ⟨name, .satisfied⟩
        let current := (Gateway.authorizePublished publication candidate model "invoke" true context actualChecks entities).isOk
        (stale, current)
#guard strongerPublicationChecks == some (false, true)

-- No coercion turns a raw semantic receipt into publication-indexed evidence.
#check_failure fun (entry : (object : Gateway.ProfileObject.Object) ×
    Gateway.ProfileObject.Publication profile object)
    (raw : Gateway.Receipt prepared model "invoke" true context checks entities) =>
  Gateway.consumeAdmission entry.2 raw ({} : Admission.OperationLedger) grants "approval"
#guard (consume {} grants "approval").isSome

-- An authenticated publication is still not an actual account/history store.
-- Rollback of that input and of the ledger remains a Host recovery obligation.
#guard againstCurrent && (let externalBudget := 0; externalBudget == 0)
#guard (consume {} grants "approval").isSome && (consume {} grants "approval").isSome

#print axioms Gateway.ProfileObject.Publication.preserves_original
#print axioms Gateway.published_profile_refines_authoritative_original
#print axioms Gateway.published_scope_cannot_reset
#print axioms Gateway.weakened_original_cannot_have_published_receipt
#print axioms Gateway.published_original_obligations_are_satisfied
#print axioms Gateway.wrong_profile_cannot_bind
#print axioms Gateway.changed_context_cannot_bind
#print axioms Gateway.published_execution_preserves_original_and_delta

end CedarPooSpec.GatewayTest
