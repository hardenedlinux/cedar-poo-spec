//! Catalog composition owns finite schema/syntax plans; request state remains local.
use crate::{
    CompiledPolicyJson, Manifest, ReplayMetrics, ReplayReceipt, SchemaBoundReceipt,
    SchemaPreparation, ValidatedManifest,
};
use crate::{preparation::PreparedReplay, syntax_preparation::SyntaxPreparation};
use cedar_poo_core::SchemaSourceJson;

/// Explicit catalog lifecycle. Plans describe source use, never SDK validity.
#[derive(Default)]
pub struct CatalogPreparation {
    schemas: SchemaPreparation,
    syntax: SyntaxPreparation,
}
impl CatalogPreparation {
    /// Count distinct sources per manifest; retain SDK state only across planned shared uses.
    pub fn from_sources(
        schemas: impl IntoIterator<Item = SchemaSourceJson>,
        policies: impl IntoIterator<Item = Vec<CompiledPolicyJson>>,
    ) -> Result<Self, String> {
        Ok(Self {
            schemas: SchemaPreparation::from_sources(schemas)?,
            syntax: SyntaxPreparation::plan(policies)?,
        })
    }
    /// Replay all cases with fresh request/entity owners and both authorizers.
    pub fn replay(
        &mut self,
        manifest: &Manifest,
        mut metrics: Option<&mut ReplayMetrics>,
    ) -> Result<Vec<ReplayReceipt>, String> {
        let result = crate::replay::check_manifest_prepared_using(
            &manifest.cases,
            None,
            metrics.as_deref_mut(),
            Default::default(),
            &mut PreparedReplay::sharing(&mut self.syntax),
        );
        self.finish(&manifest.cases, metrics)?;
        result
    }
    /// Strict validation remains per revision and per schema, including every reuse.
    pub fn replay_validated(
        &mut self,
        manifest: &ValidatedManifest,
        mut metrics: Option<&mut ReplayMetrics>,
    ) -> Result<Vec<SchemaBoundReceipt>, String> {
        let result = self
            .schemas
            .acquire(&manifest.schema, metrics.as_deref_mut())
            .and_then(|schema| {
                crate::schema::replay_with_schema_using(
                    manifest,
                    &schema,
                    metrics.as_deref_mut(),
                    &mut PreparedReplay::sharing(&mut self.syntax),
                )
            });
        self.finish(&manifest.cases, metrics)?;
        result
    }
    fn finish(
        &mut self,
        cases: &[crate::Case],
        metrics: Option<&mut ReplayMetrics>,
    ) -> Result<(), String> {
        let retired = self.syntax.finish(cases)?;
        if let Some(stats) = metrics {
            stats.catalog_syntax_retirements += retired;
        }
        Ok(())
    }
}
