import Tests.Gateway.Fixture

namespace CedarPooSpec.GatewayTest

-- Directly constructible preparation cannot bypass the same admission checks.
#guard (Gateway.prepare model "base" schema context profile request "invoke" true).isOk
#guard (authorize).isOk
#guard (authorize (prepared "tool") (effect := "tool")).isOk
#guard !(authorize (prepared "unknown") (effect := "unknown")).isOk
#guard !(authorize (state := false)).isOk
#guard !(authorize (effect := "tool")).isOk
#guard !(authorize (currentContext := { context with ownerEpoch := 2 })).isOk
#guard !(authorize (currentContext := { context with factFloor := 2 })).isOk
#guard !(authorize (currentContext := { context with scope := { scope with sourceCut := "source-2" } })).isOk
#guard !(authorize (currentModel := replacedModel)).isOk
#guard !(authorize (currentModel := sourceChangedModel)).isOk
#guard !(authorize { prepared with operationId := ⟨"new-nonce"⟩ }).isOk
#guard !(authorize { prepared with profile := { profile with identity := "other-profile" } }).isOk
#guard !(authorize (assessments := [⟨"source", .unknown⟩, ⟨"budget", .satisfied⟩, ⟨"history", .satisfied⟩])).isOk
#guard !(authorize (assessments := [⟨"source", .satisfied⟩, ⟨"budget", .satisfied⟩])).isOk
#guard !(authorize (assessments := checks ++ [⟨"history", .satisfied⟩])).isOk
#guard !(Gateway.prepare model "base" schema { context with scope := { scope with originalRoot := "" } }
    profile request "invoke" true).isOk

def firstConsumption := consume {} (grants) "approval"
#guard firstConsumption.isSome
#guard (firstConsumption.map (fun value => value.authorities.grants.map (·.used))) == some [1]
#guard (firstConsumption.bind (fun value => consume value.operations (grants "renewed") "renewed")).isNone
#guard (consume {} (grants "different-authority") "approval").isNone
#guard (consume {} ⟨[⟨"approval", "other-effect", 1, 0⟩]⟩ "approval").isNone
#guard (consume {} ⟨[⟨"approval", "invoke", 1, 1⟩]⟩ "approval").isNone

-- Changes to facts/schema/projection cannot borrow a fixed-world Delta plan.
#guard !(Gateway.prepareDelta model "base" "restricted" schema scope { scope with sourceCut := "source-2" }).isOk
#guard !(Gateway.prepareDelta model "base" "restricted" schema scope { scope with schemaIdentity := "schema-2" }).isOk
#guard !(Gateway.prepareDelta model "base" "restricted" schema scope { scope with projectionClosure := "projection-2" }).isOk
#guard (Gateway.prepareDelta model "base" "restricted" schema scope scope).isOk
#guard ((Gateway.prepareDelta model "base" "restricted" schema scope scope).toOption.map
    (fun plan => plan.matchesCurrent sourceChangedModel scope)) == some false

-- Universal library laws are audited through their actual imported declarations.
#print axioms Gateway.accepted_assessments_are_satisfied
#print axioms Gateway.unknown_assessment_cannot_be_accepted
#print axioms Gateway.admitted_actual_request_is_error_free
#print axioms Gateway.admitted_context_is_current
#print axioms Gateway.admitted_profile_preserves_required_checks
#print axioms Gateway.no_execution_gain_for_validated_input
#print axioms Gateway.changed_scope_rejects_delta_reuse
#print axioms Gateway.admitted_execution_preserves_delta
#print axioms Gateway.admitted_original_scope_is_preserved
#print axioms Gateway.admitted_operation_is_canonical
#print axioms Gateway.consumption_preserves_operation_prefix
#print axioms Gateway.consumed_operation_rejects_replay
#print axioms Gateway.renewed_authority_cannot_repeat_consumed_operation
#print axioms Gateway.bound_delta_preserves_original_scope
#print axioms Gateway.changed_scope_cannot_bind_admission
#print axioms Gateway.bound_admitted_execution_preserves_delta

end CedarPooSpec.GatewayTest
