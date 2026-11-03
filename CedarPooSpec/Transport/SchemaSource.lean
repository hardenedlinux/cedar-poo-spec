import CedarPooSpec.SchemaJson.Encoding
import CedarPooSpec.Transport.SourceTable

namespace CedarPooSpec.Transport
/-- The schema's semantic value and exact public wire are retained together. -/
structure SchemaSource extends SourceSnapshot .schema where
  meaning : Cedar.Validation.Schema
  aligned : SchemaJson.schema meaning = .ok value

def SchemaSource.capture (meaning : Cedar.Validation.Schema) : Except String SchemaSource :=
  match aligned : SchemaJson.schema meaning with
  | .error cause => .error (reprStr cause)
  | .ok value => .ok { toSourceSnapshot := SourceSnapshot.ofJson value, meaning, aligned }

theorem SchemaSource.wire_bound (source : SchemaSource) :
    source.toSourceSnapshot.wire = source.value.compress := source.encoded
end CedarPooSpec.Transport
