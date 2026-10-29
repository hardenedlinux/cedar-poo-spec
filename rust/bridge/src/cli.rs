//! Stream a Lean manifest through the Rust Cedar conformance checker.

use cedar_poo_core::{CompiledPolicyJson, TemplateSourceJson};
use cedar_poo_runtime::{
    Manifest, SchemaEvolutionBundle, ValidatedManifest, check_direct_sources, check_manifest,
    check_template_source, render_artifacts, render_policy_source, render_validated_policy_sources,
    replay_manifest, replay_schema_only_revision, replay_validated_manifest,
};
use serde::Deserialize;
use std::fs;
use std::io::{self, Read};
use std::path::Path;

#[derive(Deserialize)]
struct TemplateSourceBundle {
    source: TemplateSourceJson,
    materialized: CompiledPolicyJson,
}

/// Read one JSON manifest from standard input and check all cases.
pub fn run() -> Result<(), String> {
    let mut input = String::new();
    io::stdin()
        .read_to_string(&mut input)
        .map_err(|error| error.to_string())?;
    let args: Vec<String> = std::env::args().skip(1).collect();
    dispatch(&input, &args)
}

fn dispatch(input: &str, args: &[String]) -> Result<(), String> {
    if args.len() == 1 && args[0] == "render" {
        let policies: CompiledPolicyJson = input
            .parse()
            .map_err(|error| format!("Cedar policy JSON: {error}"))?;
        print!("{}", render_policy_source(&policies)?);
        return Ok(());
    }
    if args.len() == 1 && args[0] == "check-template-source" {
        let bundle: TemplateSourceBundle = serde_json::from_str(input)
            .map_err(|error| format!("template source bundle JSON: {error}"))?;
        check_template_source(&bundle.source, &bundle.materialized)?;
        println!("Cedar template source matches Lean materialization");
        return Ok(());
    }
    if args == ["benchmark-catalog"] {
        crate::catalog::benchmark(input)?;
        return Ok(());
    }
    if args == ["replay-catalog"] {
        println!(
            "{}",
            serde_json::to_string(&crate::catalog::replay(input)?)
                .map_err(|error| error.to_string())?
        );
        return Ok(());
    }
    if args == ["replay-validated-receipts"] {
        let manifest: ValidatedManifest = serde_json::from_str(input)
            .map_err(|error| format!("validated manifest JSON: {error}"))?;
        let receipts = replay_validated_manifest(&manifest)?;
        println!(
            "{}",
            serde_json::to_string(&receipts).map_err(|error| error.to_string())?
        );
        return Ok(());
    }
    if let [command, case_name] = args
        && command == "identified-sources"
    {
        let manifest: ValidatedManifest = serde_json::from_str(input)
            .map_err(|error| format!("validated manifest JSON: {error}"))?;
        let sources = render_validated_policy_sources(&manifest, case_name)?;
        println!(
            "{}",
            serde_json::to_string(&sources).map_err(|error| error.to_string())?
        );
        return Ok(());
    }
    if args == ["replay-schema-only-revision"] {
        let bundle: SchemaEvolutionBundle = serde_json::from_str(input)
            .map_err(|error| format!("schema evolution bundle JSON: {error}"))?;
        let receipt = replay_schema_only_revision(&bundle)?;
        println!(
            "{}",
            serde_json::to_string(&receipt).map_err(|error| error.to_string())?
        );
        return Ok(());
    }
    let manifest: Manifest =
        serde_json::from_str(input).map_err(|error| format!("manifest JSON: {error}"))?;
    run_manifest_command(&manifest, args)
}

fn run_manifest_command(manifest: &Manifest, args: &[String]) -> Result<(), String> {
    if args == ["replay-receipts"] {
        let receipts = replay_manifest(manifest)?;
        println!(
            "{}",
            serde_json::to_string(&receipts).map_err(|error| error.to_string())?
        );
        return Ok(());
    }
    check_manifest(manifest)?;
    match args {
        [] => println!("Cedar conformance: {} cases", manifest.cases.len()),
        [command, directory] if command == "emit" => {
            emit(manifest, Path::new(directory))?;
        }
        [command, directory] if command == "check-artifacts" => {
            check_artifacts(manifest, Path::new(directory))?;
        }
        [command, directory] if command == "check-direct" => {
            check_direct_sources(manifest, Path::new(directory))?;
            println!("Direct Cedar parity: {} cases", manifest.cases.len());
        }
        _ => {
            return Err(
                "usage: cedar-poo-bridge [render|check-template-source|replay-receipts|replay-validated-receipts|replay-catalog|identified-sources CASE_NAME|replay-schema-only-revision|emit DIRECTORY|check-artifacts DIRECTORY|check-direct DIRECTORY]".into(),
            );
        }
    }
    Ok(())
}

fn emit(manifest: &Manifest, directory: &Path) -> Result<(), String> {
    fs::create_dir_all(directory).map_err(|error| error.to_string())?;
    for (revision, text) in render_artifacts(manifest)? {
        fs::write(directory.join(format!("{revision}.cedar")), text)
            .map_err(|error| error.to_string())?;
    }
    println!(
        "Cedar language artifacts written to {}",
        directory.display()
    );
    Ok(())
}

fn check_artifacts(manifest: &Manifest, directory: &Path) -> Result<(), String> {
    let expected = render_artifacts(manifest)?;
    expected.iter().try_for_each(|(revision, text)| {
        let path = directory.join(format!("{revision}.cedar"));
        let actual =
            fs::read_to_string(&path).map_err(|error| format!("{}: {error}", path.display()))?;
        if &actual != text {
            return Err(format!(
                "{} is stale; run just export-cedar-language",
                path.display()
            ));
        }
        Ok::<(), String>(())
    })?;
    let mut actual_names = fs::read_dir(directory)
        .map_err(|error| error.to_string())?
        .map(|entry| {
            let path = entry.map_err(|error| error.to_string())?.path();
            if path
                .extension()
                .is_none_or(|extension| extension != "cedar")
            {
                return Ok(None);
            }
            let name = path
                .file_stem()
                .and_then(|stem| stem.to_str())
                .ok_or_else(|| format!("invalid artifact name: {}", path.display()))?;
            Ok(Some(name.to_owned()))
        })
        .collect::<Result<Vec<Option<String>>, String>>()?
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    actual_names.sort();
    if actual_names != expected.keys().cloned().collect::<Vec<_>>() {
        return Err("Cedar language artifact set is stale".into());
    }
    println!(
        "Cedar conformance: {} cases; language artifacts: {} revisions",
        manifest.cases.len(),
        expected.len()
    );
    Ok(())
}
