//! Structural inventory of accepted input, one owned entry at a time.
use std::collections::BTreeSet;
#[derive(Default)]
pub(crate) struct Inventory {
    pub entries: usize,
    pub revisions: usize,
    pub sources: usize,
    pub entities: usize,
    pub schemas: usize,
    pub validations: usize,
}
pub(crate) fn read(input: &str) -> Result<Inventory, String> {
    let doc = crate::catalog_input::document(input)?;
    let mut result = Inventory {
        entries: doc.entries.len(),
        ..Inventory::default()
    };
    let mut sources = BTreeSet::new();
    for raw in doc.entries.values() {
        let fields = crate::catalog_input::fields(raw);
        if !fields.contains_key("cases") {
            continue;
        }
        let schema = crate::catalog_input::is_schema_bound(&fields);
        let cases = if schema {
            doc.sources.validated_manifest(raw)?.cases
        } else {
            doc.sources.manifest(raw)?.cases
        };
        result.schemas += usize::from(schema);
        let mut revisions = BTreeSet::new();
        for (i, case) in cases.iter().enumerate() {
            result.entities += usize::from(i == 0 || case.entities != cases[i - 1].entities);
            if revisions.insert(&case.revision) {
                result.revisions += 1;
                result.validations += usize::from(schema);
                sources.insert(case.policies.source_identity()?.to_owned());
            }
        }
    }
    result.sources = sources.len();
    Ok(result)
}
