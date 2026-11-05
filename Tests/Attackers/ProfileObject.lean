import CedarPooSpec.Attackers.ProfileObject

namespace CedarPooSpec.AttackersObjectTest
open CedarPooSpec.Attackers ProfileObject

def base : Model String := ⟨["endpoint"], [], ["independent-authority"], ["exact-effect"]⟩
def paymentExtra : Model String :=
  ⟨[], [⟨["endpoint"], "payment-network"⟩], [], ["payment-signing"]⟩
def healthExtra : Model String :=
  ⟨[], [⟨["endpoint"], "health-gateway"⟩], [], ["health-disclosure"]⟩

def family := do
  let root ← define "ExternalAttacker" base
  let payment ← augment root "PaymentAttacker" paymentExtra
  let health ← derive payment "HealthAttacker" ["ExternalAttacker"] healthExtra
  let combined ← mix health "CombinedAttacker" ["PaymentAttacker", "HealthAttacker"]
  pure (payment, health, combined)

def readModel (object : Object base) : Option (Certified base) := do
  let session ← (openSession base object).toOption
  (← session.read .model)

def bothParentsRetained : Bool :=
  match family with
  | .error _ => false
  | .ok (payment, health, combined) =>
      match openSession base payment, openSession base health, openSession base combined with
      | .ok paymentSession, .ok healthSession, .ok selected =>
          (selectSessions paymentSession selected).isSome && (selectSessions healthSession selected).isSome
      | _, _, _ => false

#guard family.isOk
#guard bothParentsRetained
#guard (family.toOption.bind (readModel ∘ (·.2.2))).map
  (fun checked => checked.model.rules.length) == some 2
#guard (family.toOption.bind (readModel ∘ (·.2.2))).map
  (fun checked => checked.model.goals.length) == some 3

-- Replacing a raw slot invalidates/recomputes the inherited certified model.
def brokenIsolation := family.bind fun (_, _, combined) => combined.extendWith "BrokenIsolation" do
  LeanPoo.Object.Dataflow.Builder.value .initial ["endpoint", "independent-authority"]
#guard brokenIsolation.isOk
#guard (brokenIsolation.toOption.bind readModel).isNone

-- Keeping the base index alone is insufficient: dropping a parent's additional
-- attacker powers gives a falsely smaller threat model. Actual parent selection refuses.
def droppedRules := family.bind fun (_, _, combined) => combined.extendWith "DroppedRules" do
  LeanPoo.Object.Dataflow.Builder.value .rules []
#guard (droppedRules.toOption.bind readModel).isSome

def parentRefusesDroppedRules : Bool :=
  match family, droppedRules with
  | .ok (payment, health, _), .ok selected =>
      match openSession base payment, openSession base health, openSession base selected with
      | .ok paymentSession, .ok healthSession, .ok selectedSession =>
          (selectSessions paymentSession selectedSession).isNone &&
            (selectSessions healthSession selectedSession).isNone
      | _, _, _ => false
  | _, _ => false
#guard parentRefusesDroppedRules

-- An assumption-changing rule is rejected, not silently classified as another
-- specialization of the same independent-boundary object.
def collapsedTrust := family.bind fun (_, _, combined) =>
  augment combined "CollapsedTrust" ⟨[], [⟨["payment-network"], "independent-authority"⟩], [], []⟩
#guard collapsedTrust.isOk
#guard (collapsedTrust.toOption.bind readModel).isNone

#print axioms selection_retains_actual_parent
#print axioms certified_isolation
end CedarPooSpec.AttackersObjectTest
