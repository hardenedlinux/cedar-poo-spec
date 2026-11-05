import Cedar.Spec.Ext.Datetime
import Lean.Data.Json

/-! Scenario provenance describes the source and scope of a model. Date/shape
checks do not authenticate a publisher or prove its reported incident claims. -/
namespace CedarPooSpec.Scenarios

inductive Kind where
  | synthetic | reportedIncident
  deriving DecidableEq, Repr

inductive DisclosureStatus where
  | preliminary | publisherConfirmed
  deriving DecidableEq, Repr

structure EventWindow where
  startsOn : String
  endsOn : Option String := none
  timezone : String
  deriving DecidableEq, Repr

structure Disclosure where
  publisher : String
  title : String
  url : String
  publishedOn : String
  accessedOn : String
  status : DisclosureStatus
  deriving DecidableEq, Repr

structure Metadata where
  id : String
  title : String
  domain : String
  summary : String
  kind : Kind
  event : Option EventWindow := none
  disclosures : List Disclosure := []
  limitations : List String
  deriving DecidableEq, Repr

/-- Reuse Cedar's official calendar parser, restricted to date-only input. -/
def validDay (day : String) : Bool :=
  day.length == 10 && (Cedar.Spec.Ext.Datetime.parse day).isSome

def dayLE (earlier later : String) : Bool :=
  match Cedar.Spec.Ext.Datetime.parse earlier, Cedar.Spec.Ext.Datetime.parse later with
  | some a, some b => Cedar.Spec.Ext.Datetime.le a b
  | _, _ => false

def EventWindow.valid (event : EventWindow) : Bool :=
  validDay event.startsOn && !event.timezone.trimAscii.toString.isEmpty &&
    event.endsOn.all (fun last => validDay last && dayLE event.startsOn last)

def Disclosure.valid (source : Disclosure) : Bool :=
  !source.publisher.trimAscii.toString.isEmpty && !source.title.trimAscii.toString.isEmpty &&
    source.url.startsWith "https://" && source.url.length > 8 &&
    validDay source.publishedOn && validDay source.accessedOn &&
    dayLE source.publishedOn source.accessedOn

def Metadata.valid (metadata : Metadata) : Bool :=
  !metadata.id.trimAscii.toString.isEmpty && !metadata.title.trimAscii.toString.isEmpty &&
    !metadata.domain.trimAscii.toString.isEmpty && !metadata.summary.trimAscii.toString.isEmpty &&
    !metadata.limitations.isEmpty &&
    metadata.limitations.all (fun text => !text.trimAscii.toString.isEmpty) &&
    metadata.event.all EventWindow.valid && metadata.disclosures.all Disclosure.valid &&
    (metadata.kind == .synthetic || (metadata.event.isSome && !metadata.disclosures.isEmpty))

structure CertifiedMetadata where
  value : Metadata
  valid : value.valid = true

private def eventJson (event : EventWindow) : Lean.Json := Lean.Json.mkObj [
  ("starts_on", Lean.toJson event.startsOn), ("ends_on", Lean.toJson event.endsOn),
  ("timezone", Lean.toJson event.timezone)]

def Metadata.toJson (metadata : Metadata) : Lean.Json := Lean.Json.mkObj [
  ("id", Lean.toJson metadata.id), ("title", Lean.toJson metadata.title),
  ("domain", Lean.toJson metadata.domain), ("summary", Lean.toJson metadata.summary),
  ("kind", Lean.toJson (match metadata.kind with | .synthetic => "synthetic" | .reportedIncident => "reported-incident")),
  ("event", metadata.event.map eventJson |>.getD Lean.Json.null),
  ("disclosures", Lean.toJson (metadata.disclosures.map fun source => Lean.Json.mkObj [
    ("publisher", Lean.toJson source.publisher), ("title", Lean.toJson source.title),
    ("url", Lean.toJson source.url), ("published_on", Lean.toJson source.publishedOn),
    ("accessed_on", Lean.toJson source.accessedOn),
    ("status", Lean.toJson (match source.status with | .preliminary => "preliminary" | .publisherConfirmed => "publisher-confirmed"))])),
  ("limitations", Lean.toJson metadata.limitations)]

end CedarPooSpec.Scenarios
