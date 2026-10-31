import CedarPooSpec.Data.StorageEffect
import CedarPooSpec.PolicyJson
import Lean.Data.Json

namespace CedarPooSpec.Data.StorageEffectFixture

open Cedar.Spec CedarPooSpec.Data Lean

private def obj (fields : List (String × Json)) : Json := Json.mkObj fields

private def sourceJson (source : SourceLabel) : Json :=
  obj [("resource", CedarPooSpec.PolicyJson.entity source.resource),
    ("owner", CedarPooSpec.PolicyJson.entity source.owner),
    ("tenant", toJson source.tenant), ("restricted", toJson source.restricted)]

private def destinationJson (destination : Destination) (tier : StorageTier) : Json :=
  obj [("resource", CedarPooSpec.PolicyJson.entity destination.resource),
    ("tenant", toJson destination.tenant),
    ("accepted_owners", toJson (destination.acceptedOwners.map CedarPooSpec.PolicyJson.entity)),
    ("accepts_restricted", toJson destination.acceptsRestricted),
    ("tier", toJson (if tier == .remote then "remote" else "durable-local"))]

def effectJson (effect : StorageEffect) : Json :=
  obj [("operation_id", toJson effect.operationId),
    ("subject", CedarPooSpec.PolicyJson.entity effect.subject),
    ("purpose", toJson effect.purpose), ("snapshot_cid", toJson effect.snapshotCid),
    ("sources", toJson (effect.sources.map sourceJson)),
    ("destination", destinationJson effect.destination effect.tier),
    ("policy_root", toJson effect.policyRoot),
    ("lineage_revision", toJson effect.lineageRevision)]

private def claimJson (claim : StorageClaim) : Json :=
  obj [("effect", effectJson claim.effect), ("epoch", toJson claim.epoch),
    ("expires_at", toJson claim.expiresAt), ("allowed", toJson claim.allowed)]

def currentJson (current : CurrentStorageState) : Json :=
  obj [("policy_root", toJson current.policyRoot),
    ("lineage_revision", toJson current.lineageRevision),
    ("epoch", toJson current.epoch), ("now", toJson current.now)]

private def service : EntityUID := ⟨⟨"Service", []⟩, "publisher"⟩
private def sourceId : EntityUID := ⟨⟨"Dataset", []⟩, "orders"⟩
private def owner : EntityUID := ⟨⟨"Team", []⟩, "analytics"⟩
private def otherOwner : EntityUID := ⟨⟨"Team", []⟩, "other"⟩
private def destinationId : EntityUID := ⟨⟨"Bucket", []⟩, "archive"⟩

def baseSource : SourceLabel :=
  { resource := sourceId, owner, tenant := "tenant-a", restricted := false }

def baseDestination : Destination :=
  { resource := destinationId, tenant := "tenant-a",
    acceptedOwners := [owner], acceptsRestricted := false }

def baseEffect : StorageEffect :=
  { operationId := "op-001", subject := service, purpose := "archive",
    snapshotCid := "bafyreibsgh7hsmqsgp42ls3jdd26u4coplmgk5vl4l5fbff3vjziaoidai",
    sources := [baseSource], destination := baseDestination, tier := .remote,
    policyRoot := "policy-root-1", lineageRevision := "lineage-1" }

private def baseClaim : StorageClaim :=
  { effect := baseEffect, epoch := 4, expiresAt := 100, allowed := true }

def baseCurrent : CurrentStorageState :=
  { policyRoot := "policy-root-1", lineageRevision := "lineage-1", epoch := 4, now := 99 }

def cases : List (String × StorageEffect × StorageClaim × CurrentStorageState) :=
  [("allow", baseEffect, baseClaim, baseCurrent),
   ("local-allow", { baseEffect with tier := .durableLocal },
      { baseClaim with effect := { baseEffect with tier := .durableLocal } }, baseCurrent),
   ("restricted", { baseEffect with sources := [{ baseSource with restricted := true }] },
      { baseClaim with effect := { baseEffect with
          sources := [{ baseSource with restricted := true }] } }, baseCurrent),
   ("restricted-accepted-still-raw", { baseEffect with
       sources := [{ baseSource with restricted := true }],
       destination := { baseDestination with acceptsRestricted := true } },
      { baseClaim with effect := { baseEffect with
          sources := [{ baseSource with restricted := true }],
          destination := { baseDestination with acceptsRestricted := true } } }, baseCurrent),
   ("tenant", { baseEffect with sources := [{ baseSource with tenant := "tenant-b" }] },
      { baseClaim with effect := { baseEffect with
          sources := [{ baseSource with tenant := "tenant-b" }] } }, baseCurrent),
   ("owner", { baseEffect with sources := [{ baseSource with owner := otherOwner }] },
      { baseClaim with effect := { baseEffect with
          sources := [{ baseSource with owner := otherOwner }] } }, baseCurrent),
   ("operation-substitution", baseEffect,
      { baseClaim with effect := { baseEffect with operationId := "op-002" } }, baseCurrent),
   ("subject-substitution", baseEffect,
      { baseClaim with effect := { baseEffect with subject := sourceId } }, baseCurrent),
   ("purpose-substitution", baseEffect,
      { baseClaim with effect := { baseEffect with purpose := "other-use" } }, baseCurrent),
   ("source-substitution", baseEffect,
      { baseClaim with effect := { baseEffect with sources :=
          [{ baseSource with resource := destinationId }] } }, baseCurrent),
   ("destination-substitution", baseEffect,
      { baseClaim with effect := { baseEffect with destination :=
          { baseDestination with resource := sourceId } } }, baseCurrent),
   ("root-substitution", baseEffect,
      { baseClaim with effect := { baseEffect with snapshotCid :=
          "bafkreie7vj2rmiytc6plrz7n4bejnug2rzeypl2u3cnibf2aa4dhqdp6u4" } },
      baseCurrent),
   ("stale-policy", baseEffect, baseClaim,
      { baseCurrent with policyRoot := "policy-root-2" }),
   ("stale-lineage", baseEffect, baseClaim,
      { baseCurrent with lineageRevision := "lineage-2" }),
   ("stale-epoch", baseEffect, baseClaim, { baseCurrent with epoch := 5 }),
   ("expired", baseEffect, baseClaim, { baseCurrent with now := 100 }),
   ("denied", baseEffect, { baseClaim with allowed := false }, baseCurrent)]

def fixture : Json :=
  obj [("schema", toJson "cedar-poo-storage-effect-v1"),
    ("cases", toJson (cases.map fun (name, effect, claim, current) =>
      obj [("name", toJson name), ("effect", effectJson effect),
        ("claim", claimJson claim), ("current", currentJson current),
        ("allow", toJson (effect.rawAdmitted claim current))]))]

end CedarPooSpec.Data.StorageEffectFixture
