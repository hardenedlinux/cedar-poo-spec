//! Python is a consumer of the existing typed Rust runtime, never its semantic owner.
use cedar_poo_runtime::{Manifest, SchemaEvolutionBundle, ValidatedManifest};
use pyo3::exceptions::PyValueError;
use pyo3::types::{PyBytes, PyModule, PyModuleMethods};
use pyo3::{Bound, PyResult, Python, pyfunction, pymodule, wrap_pyfunction};
use serde::Serialize;

fn encode(value: &impl Serialize) -> Result<Vec<u8>, String> {
    let mut output = serde_json::to_vec(value).map_err(|error| error.to_string())?;
    output.push(b'\n');
    Ok(output)
}
fn replay(input: &[u8]) -> Result<Vec<u8>, String> {
    let manifest: Manifest =
        serde_json::from_slice(input).map_err(|error| format!("manifest JSON: {error}"))?;
    encode(&cedar_poo_runtime::replay_manifest(&manifest)?)
}
fn replay_validated(input: &[u8]) -> Result<Vec<u8>, String> {
    let manifest: ValidatedManifest = serde_json::from_slice(input)
        .map_err(|error| format!("validated manifest JSON: {error}"))?;
    encode(&cedar_poo_runtime::replay_validated_manifest(&manifest)?)
}
fn replay_revision(input: &[u8]) -> Result<Vec<u8>, String> {
    let bundle: SchemaEvolutionBundle = serde_json::from_slice(input)
        .map_err(|error| format!("schema evolution bundle JSON: {error}"))?;
    encode(&cedar_poo_runtime::replay_schema_only_revision(&bundle)?)
}
fn native_bytes<'py>(
    py: Python<'py>,
    input: &[u8],
    run: fn(&[u8]) -> Result<Vec<u8>, String>,
) -> PyResult<Bound<'py, PyBytes>> {
    let input = input.to_vec();
    let output = py
        .detach(move || run(&input))
        .map_err(PyValueError::new_err)?;
    Ok(PyBytes::new(py, &output))
}
/// Replay a raw manifest through the shared Rust runtime; return exact CLI JSON receipt bytes.
#[pyfunction]
fn replay_receipts<'py>(py: Python<'py>, manifest_json: &[u8]) -> PyResult<Bound<'py, PyBytes>> {
    native_bytes(py, manifest_json, replay)
}
/// Validate a schema-bound manifest and replay it with the official Cedar SDK.
#[pyfunction]
fn replay_validated_receipts<'py>(
    py: Python<'py>,
    manifest_json: &[u8],
) -> PyResult<Bound<'py, PyBytes>> {
    native_bytes(py, manifest_json, replay_validated)
}
/// Replay a schema-only revision using the existing Rust revision owner.
#[pyfunction]
fn replay_schema_only_revision<'py>(
    py: Python<'py>,
    bundle_json: &[u8],
) -> PyResult<Bound<'py, PyBytes>> {
    native_bytes(py, bundle_json, replay_revision)
}
/// A direct native extension: no Cargo invocation, subprocess or Python policy evaluator.
#[pymodule(gil_used = false)]
fn _native(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_function(wrap_pyfunction!(replay_receipts, module)?)?;
    module.add_function(wrap_pyfunction!(replay_validated_receipts, module)?)?;
    module.add_function(wrap_pyfunction!(replay_schema_only_revision, module)?)?;
    Ok(())
}
