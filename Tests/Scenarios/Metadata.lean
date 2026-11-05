import CedarPooSpec.Scenarios

namespace CedarPooSpec.ScenariosTest
open CedarPooSpec.Scenarios

def synthetic : Metadata :=
  { id := "wallet-base", title := "Synthetic wallet", domain := "financial-services",
    summary := "Reusable native-value signing model", kind := .synthetic,
    limitations := ["Synthetic inputs; no physical signing"] }
def source : Disclosure :=
  { publisher := "Binance", title := "Initial findings", url := "https://www.binance.com/en/blog/community/3229153443759566763",
    publishedOn := "2026-11-03", accessedOn := "2026-11-05", status := .preliminary }
def incident : Metadata :=
  { synthetic with
    id := "binance-2026-10-29", kind := .reportedIncident,
    event := some ⟨"2026-10-29", some "2026-10-30", "UTC"⟩, disclosures := [source] }

#guard synthetic.valid
#guard incident.valid
#guard !({ synthetic with id := " " }).valid
#guard !({ synthetic with limitations := [] }).valid
#guard !({ synthetic with domain := "" }).valid
#guard !({ incident with event := none }).valid
#guard !({ incident with disclosures := [] }).valid
#guard !({ incident with disclosures := [{ source with url := "file:///untrusted" }] }).valid
#guard !({ incident with disclosures := [{ source with publishedOn := "2026-02-30" }] }).valid
#guard !({ incident with disclosures := [{ source with accessedOn := "2026-11-02" }] }).valid
#guard !({ incident with event := some ⟨"2026-10-30", some "2026-10-29", "UTC"⟩ }).valid
#guard !({ incident with event := some ⟨"2026-10-29", none, ""⟩ }).valid
#guard !validDay "2026-11-05T00:00:00Z"
#guard validDay "2024-02-29"
#guard !validDay "2025-02-29"

def parent := (create synthetic (7 : Nat)).toOption.get (by native_decide)
def child := derive parent incident (· + 1)
#guard child.isOk
#guard (child.toOption.map (·.model)) == some 8
#guard (child.toOption.map (·.metadata.value.id)) == some incident.id
#guard (child.toOption.map (fun scenario => scenario.ancestors.map Metadata.id)) == some [synthetic.id]
#guard !(derive parent synthetic id).isOk
#guard !(create { incident with disclosures := [] } (7 : Nat)).isOk
#guard !(prepareMetadata { incident with event := none }).isOk

#print axioms every_scenario_has_valid_metadata
#print axioms create_preserves_model
#print axioms derivation_retains_parent
#print axioms derivation_preserves_binding
#print axioms invocation_retains_metadata
end CedarPooSpec.ScenariosTest
