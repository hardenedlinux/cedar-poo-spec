//! Structural inventory of accepted input, one owned entry at a time.
use serde_json::Value;
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
    let source = crate::catalog_input::decode(input)?;
    let mut result = Inventory {
        entries: source.len(),
        ..Inventory::default()
    };
    for raw in source.values() {
        let entry = crate::catalog_input::value(raw)?;
        result.entry(&entry)?;
    }
    Ok(result)
}
impl Inventory {
    fn entry(&mut self, entry: &Value) -> Result<(), String> {
        let Some(cases) = entry.get("cases").and_then(Value::as_array) else {
            return Ok(());
        };
        let schema = entry.get("schema").is_some();
        self.schemas += usize::from(schema);
        let mut revisions = BTreeSet::new();
        let mut sources = BTreeSet::new();
        for (index, case) in cases.iter().enumerate() {
            self.entities +=
                usize::from(index == 0 || case.get("entities") != cases[index - 1].get("entities"));
            if let Some(revision) = case.get("revision").and_then(Value::as_str)
                && revisions.insert(revision)
            {
                self.revisions += 1;
                self.validations += usize::from(schema);
                if let Some(source) = case.get("policies") {
                    sources.insert(serde_json::to_string(source).map_err(|e| e.to_string())?);
                }
            }
        }
        self.sources += sources.len();
        Ok(())
    }
}
