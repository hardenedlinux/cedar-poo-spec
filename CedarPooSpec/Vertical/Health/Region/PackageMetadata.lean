import Lean.Data.Json

/-!
Read only the publication identity of an official FHIR NPM package. Resource
parsing, profile validation, and terminology evaluation belong to the Host.
-/

namespace CedarPooSpec.Vertical.Health.Region.PackageMetadata

structure Pin where
  name : String
  version : String
  canonical : String
  jurisdiction : String
  fhirVersion : String
  deriving DecidableEq, Repr

def Pin.reference (pin : Pin) : String := s!"{pin.name}#{pin.version}"

def australia : Pin :=
  { name := "hl7.fhir.au.core", version := "2.0.0",
    canonical := "http://hl7.org.au/fhir/core",
    jurisdiction := "urn:iso:std:iso:3166#AU", fhirVersion := "4.0.1" }

def unitedStates : Pin :=
  { name := "hl7.fhir.us.core", version := "9.0.0",
    canonical := "http://hl7.org/fhir/us/core",
    jurisdiction := "urn:iso:std:iso:3166#US", fhirVersion := "4.0.1" }

def decode (json : Lean.Json) : Except String Pin := do
  let versions ← (json.getObjValAs? (Array String) "fhirVersions").mapError toString
  if versions.size != 1 then
    throw "expected exactly one FHIR base version"
  let pin : Pin := {
    name := ← (json.getObjValAs? String "name").mapError toString
    version := ← (json.getObjValAs? String "version").mapError toString
    canonical := ← (json.getObjValAs? String "canonical").mapError toString
    jurisdiction := ← (json.getObjValAs? String "jurisdiction").mapError toString
    fhirVersion := versions[0]!
  }
  let dependencies ← (json.getObjVal? "dependencies").mapError toString
  let base ← (dependencies.getObjValAs? String "hl7.fhir.r4.core").mapError toString
  if base != pin.fhirVersion then
    throw "FHIR base dependency differs from fhirVersions"
  return pin

def check (expected : Pin) (json : Lean.Json) : Except String Unit := do
  let actual ← decode json
  if actual != expected then
    throw s!"unexpected FHIR package: {repr actual}"

/-- Import the publication identity from an official FHIR package.json file. -/
def loadFile (path : System.FilePath) : IO Pin := do
  let content ← IO.FS.readFile path
  let json ← match Lean.Json.parse content with
    | .ok json => pure json
    | .error err => throw <| IO.userError s!"{path}: {err}"
  match decode json with
  | .ok pin => pure pin
  | .error err => throw <| IO.userError s!"{path}: {err}"

def checkFile (expected : Pin) (path : System.FilePath) : IO Unit := do
  let actual ← loadFile path
  if actual != expected then
    throw <| IO.userError s!"{path}: unexpected FHIR package: {repr actual}"

end CedarPooSpec.Vertical.Health.Region.PackageMetadata
