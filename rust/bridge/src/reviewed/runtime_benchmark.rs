//! Native API latency, separate from full-corpus regression wall time.
use super::{Bundle, Case, Prepared, activate_prepared, coverage, prepare, validate_refusals};
use cedar_poo_core::SchemaSourceJson;
use cedar_poo_runtime::gateway::{
    EffectIo, Envelope, ProviderJournal, Receipt, ReleaseIdentity, ReviewAuthority, Simulator,
    Witness, reconcile, verify,
};
use cedar_poo_runtime::{ValidatedManifest, ValidatedProgram, replay_validated_manifest};
use serde_json::{Value, json};
use std::{collections::BTreeMap, io::Write, time::Instant};

const SERIAL: usize = 16;
const WORKERS: usize = 4;
const PER_WORKER: usize = 8;
const SCALE: usize = 1024;
#[derive(Default)]
struct Measurements {
    times: BTreeMap<&'static str, Vec<u128>>,
    entries: usize,
    cases: usize,
    refusals: usize,
    allowed: usize,
    blocked: usize,
    scale: Option<(Case, SchemaSourceJson)>,
    samples: Vec<Value>,
    program_samples: Vec<Value>,
}
fn measure<T>(
    data: &mut Measurements,
    name: &'static str,
    run: impl FnOnce() -> Result<T, String>,
) -> Result<T, String> {
    let start = Instant::now();
    let result = run()?;
    data.times
        .entry(name)
        .or_default()
        .push(start.elapsed().as_nanos());
    Ok(result)
}
fn verify_preparation(sim: &Simulator, envelope: &Envelope, expected: bool) -> Result<(), String> {
    if sim.prepare(std::hint::black_box(envelope)).is_ok() != expected {
        return Err("runtime prepare differs from actual Lean outcome".into());
    }
    Ok(())
}
fn concurrent(sim: &Simulator, envelope: &Envelope, expected: bool) -> Result<Vec<u128>, String> {
    let barrier = std::sync::Barrier::new(WORKERS);
    std::thread::scope(|scope| {
        let tasks: Vec<_> = (0..WORKERS)
            .map(|_| {
                let barrier = &barrier;
                scope.spawn(move || {
                    barrier.wait();
                    (0..PER_WORKER)
                        .map(|_| {
                            let start = Instant::now();
                            verify_preparation(sim, envelope, expected)?;
                            Ok(start.elapsed().as_nanos())
                        })
                        .collect::<Result<Vec<_>, String>>()
                })
            })
            .collect();
        let mut values = Vec::new();
        for task in tasks {
            values.extend(task.join().map_err(|_| "benchmark worker panicked")??);
        }
        Ok(values)
    })
}
fn send(
    sim: &Simulator,
    witness: &mut Witness,
    provider: &mut ProviderJournal,
) -> Result<cedar_poo_runtime::gateway::Signed, String> {
    let envelope = sim.envelope();
    let (outcome, receipt) = sim.execute(
        sim.prepare(&envelope)?,
        &envelope,
        EffectIo {
            witness,
            provider,
            crash_after_send: false,
        },
    )?;
    if !outcome.receipted || outcome.unknown {
        return Err("runtime send did not complete".into());
    }
    receipt.ok_or("runtime send omitted its receipt".into())
}
fn qualify_case(
    data: &mut Measurements,
    prepared: &Prepared,
    index: usize,
    entry: &str,
    group: usize,
    program: &ValidatedProgram,
) -> Result<(), String> {
    let starts: BTreeMap<_, _> = data
        .times
        .iter()
        .map(|(phase, values)| (*phase, values.len()))
        .collect();
    let before = &prepared.before.cases[index];
    let after = &prepared.restored.cases[index];
    let expected = after.expected == "allow" && after.expected_error_policies.is_empty();
    measure(data, "sdk.prepare", || {
        replay_validated_manifest(&ValidatedManifest {
            schema: prepared.before.schema.clone(),
            cases: vec![before.clone()],
        })
    })?;
    let cold = measure(data, "operation.construct", || {
        Simulator::with_release(before, &prepared.before.schema, prepared.release.clone())
    })?;
    measure(data, "sdk.replay.prepared", || program.replay(before))?;
    let sim = measure(data, "operation.construct.shared-program", || {
        Simulator::with_prepared_release(before, program, prepared.release.clone())
    })?;
    if cold.lifecycle_view()? != sim.lifecycle_view()?
        || serde_json::to_value(cold.envelope()).map_err(|e| e.to_string())?
            != serde_json::to_value(sim.envelope()).map_err(|e| e.to_string())?
    {
        return Err("shared program changed initial operation state or signed evidence".into());
    }
    drop(cold);
    measure(data, "review.publish.two", || {
        activate_prepared(&sim, prepared, index)
    })?;
    let envelope = sim.envelope();
    for _ in 0..4 {
        verify_preparation(&sim, &envelope, expected)?;
    }
    let label = if expected {
        "prepare.allowed"
    } else {
        "prepare.blocked"
    };
    for _ in 0..SERIAL {
        measure(data, label, || {
            verify_preparation(&sim, &envelope, expected)
        })?;
    }
    let samples = concurrent(&sim, &envelope, expected)?;
    data.times
        .entry(if expected {
            "prepare.concurrent.allowed"
        } else {
            "prepare.concurrent.blocked"
        })
        .or_default()
        .extend(samples);
    measure(data, "sources.renew", || sim.refresh_facts(after, 200))?;
    verify_preparation(&sim, &sim.envelope(), expected)?;
    if expected {
        let mut witness = Witness::simulation();
        let mut provider = ProviderJournal::default();
        let receipt = measure(data, "execute.empty-log", || {
            send(&sim, &mut witness, &mut provider)
        })?;
        let audit = reconcile(
            &provider,
            &[receipt],
            &witness.snapshot(),
            &sim.audit_authority(&witness),
        );
        if audit != Default::default() {
            return Err("runtime benchmark independent audit failed".into());
        }
        data.allowed += 1;
        if data.scale.is_none() {
            data.scale = Some((after.clone(), prepared.before.schema.clone()));
        }
    } else {
        data.blocked += 1;
    }
    let samples: BTreeMap<_, _> = data
        .times
        .iter()
        .map(|(phase, values)| (*phase, &values[*starts.get(phase).unwrap_or(&0)..]))
        .collect();
    data.samples.push(json!({"entry":entry,"group":group,"case":after.name,"allowed":expected,"evidence_statements":envelope.facts.len(),"field_bindings":sim.fact_authority().public_material().0.len(),"samples_ns":samples}));
    data.cases += 1;
    Ok(())
}
fn qualify_entry(
    data: &mut Measurements,
    name: &str,
    input: &str,
    canonical: &crate::catalog_input::Document<'_>,
) -> Result<(), String> {
    let raw: Value = serde_json::from_str(input).map_err(|e| e.to_string())?;
    let bundle: Bundle = serde_json::from_str(input).map_err(|e| e.to_string())?;
    if bundle.format_version != 1 {
        return Err("unsupported runtime workload".into());
    }
    coverage::check(&bundle, canonical, name)?;
    for (index, group) in bundle.groups.iter().enumerate() {
        let prepared = prepare(group, &raw["groups"][index], &ReviewAuthority::simulation())?;
        let first = prepared
            .before
            .cases
            .first()
            .ok_or("empty prepared runtime group")?;
        let (program, receipt) = measure(data, "program.prepare", || {
            ValidatedProgram::prepare(&prepared.before.schema, first)
        })?;
        if receipt.replay
            != replay_validated_manifest(&ValidatedManifest {
                schema: prepared.before.schema.clone(),
                cases: vec![first.clone()],
            })?
            .remove(0)
            .replay
        {
            return Err("program bootstrap changed the independent SDK receipt".into());
        }
        data.program_samples.push(
            json!({"entry":name,"group":index,"elapsed_ns":data.times["program.prepare"].last()}),
        );
        for case in 0..prepared.before.cases.len() {
            qualify_case(data, &prepared, case, name, index, &program)?;
        }
    }
    data.refusals += validate_refusals(&bundle)?;
    data.entries += 1;
    eprintln!("RUNTIME-ENTRY: {name}; cases={}", data.cases);
    Ok(())
}
fn growing_log(data: &mut Measurements) -> Result<(), String> {
    let (case, schema) = data
        .scale
        .as_ref()
        .ok_or("missing actual allow scale seed")?
        .clone();
    let (program, _) = measure(data, "program.prepare", || {
        ValidatedProgram::prepare(&schema, &case)
    })?;
    let release = ReleaseIdentity {
        root: case.revision.clone(),
        source: super::policy_hash(&case.policies)?,
    };
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let mut receipts = Vec::new();
    let mut audit = None;
    (0..SCALE).try_for_each(|index| -> Result<(), String> {
        let mut operation = case.clone();
        // Distinct logical operations over one actual Cedar world; no grant is reused.
        operation.name = format!("runtime-append-{index}");
        let sim = Simulator::with_prepared_release(&operation, &program, release.clone())?;
        let phase = match index {
            0..16 => "execute.log-0-15",
            16..64 => "execute.log-16-63",
            64..256 => "execute.log-64-255",
            _ => "execute.log-256-1023",
        };
        let receipt = measure(data, phase, || send(&sim, &mut witness, &mut provider))?;
        let decoded: Receipt = verify(&receipt, &sim.verifying_key())?;
        if decoded.action != provider.actions[index] {
            return Err("scale provider observation changed".into());
        }
        receipts.push(receipt);
        audit = Some(sim.audit_authority(&witness));
        Ok(())
    })?;
    let report = reconcile(
        &provider,
        &receipts,
        &witness.snapshot(),
        &audit.ok_or("missing scale audit")?,
    );
    if report != Default::default()
        || witness.entries().len() != SCALE
        || provider.actions.len() != SCALE
    {
        return Err("growing-log independent reconciliation failed".into());
    }
    Ok(())
}
fn statistics(values: &[u128]) -> Value {
    let mut values = values.to_vec();
    values.sort_unstable();
    let at = |percent: usize| values[(values.len() - 1) * percent / 100];
    json!({"count":values.len(),"p50_ns":at(50),"p95_ns":at(95),"p99_ns":at(99),"max_ns":values[values.len()-1]})
}
fn report(data: &mut Measurements, output: &mut impl Write) -> Result<(), String> {
    if data.entries != 51
        || data.cases != 1253
        || data.refusals != 39
        || data.allowed == 0
        || data.blocked == 0
    {
        return Err("incomplete runtime benchmark workload".into());
    }
    let phases: BTreeMap<_, _> = data
        .times
        .iter_mut()
        .map(|(name, values)| (*name, statistics(values)))
        .collect();
    for (name, stats) in &phases {
        for percentile in ["p50_ns", "p95_ns", "p99_ns"] {
            eprintln!(
                "measurement: cedar.gateway.runtime.{name}.{percentile} {} ns",
                stats[percentile]
            );
        }
    }
    serde_json::to_writer(&mut *output, &json!({"kind":"gateway-runtime-api","build_profile":"release",
        "entries":data.entries,"cases":data.cases,"refusals":data.refusals,"allowed":data.allowed,"blocked":data.blocked,
        "serial_per_case":SERIAL,"workers":WORKERS,"per_worker":PER_WORKER,"scale_operations":0,"samples":data.samples,"program_samples":data.program_samples,
        "scope":"decoded typed native API inputs, simulated issuers/provider, same-image preparation contention; no RPC/network latency or production SLO", "phases":phases})).map_err(|e|e.to_string())?;
    writeln!(output).map_err(|e| e.to_string())
}
/// Whole-domain native API measurements; invocation/receipt assertions remain native.
pub(crate) fn benchmark(
    input: &str,
    directory: &str,
    output: &mut impl Write,
    append_only: bool,
) -> Result<(), String> {
    if cfg!(debug_assertions) {
        return Err("runtime latency requires the release executable".into());
    }
    let original = crate::catalog::replay(input)?;
    let canonical = crate::catalog_input::document(input)?;
    let mut measurements = Measurements::default();
    if append_only {
        return benchmark_append(&canonical, &mut measurements, output);
    }
    let started = Instant::now();
    for name in original
        .as_object()
        .ok_or("missing canonical runtime entries")?
        .keys()
    {
        if !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') {
            return Err("unsafe runtime entry name".into());
        }
        let file = std::path::Path::new(directory).join(format!("{name}.json"));
        qualify_entry(
            &mut measurements,
            name,
            &std::fs::read_to_string(file).map_err(|e| e.to_string())?,
            &canonical,
        )?;
        serde_json::to_writer(
            &mut *output,
            &json!({"kind":"runtime-progress","entry":name,
            "cases":measurements.cases,"elapsed_ms":started.elapsed().as_millis()}),
        )
        .map_err(|e| e.to_string())?;
        writeln!(output).map_err(|e| e.to_string())?;
        output.flush().map_err(|e| e.to_string())?;
    }
    report(&mut measurements, output)
}

fn benchmark_append(
    canonical: &crate::catalog_input::Document<'_>,
    data: &mut Measurements,
    output: &mut impl Write,
) -> Result<(), String> {
    let mut provenance = None;
    for (name, raw) in &canonical.entries {
        if crate::catalog_input::is_schema_bound(&crate::catalog_input::fields(raw)) {
            let manifest = canonical.sources.validated_manifest(raw)?;
            if let Some((case, schema)) = scale_seed(manifest) {
                provenance = Some(json!({"entry":name,"case":case.name}));
                data.scale = Some((case, schema));
                break;
            }
        }
    }
    growing_log(data)?;
    let phases: BTreeMap<_, _> = data
        .times
        .iter_mut()
        .map(|(name, values)| (*name, statistics(values)))
        .collect();
    for (name, stats) in &phases {
        for key in ["p50_ns", "p95_ns", "p99_ns"] {
            eprintln!(
                "measurement: cedar.gateway.runtime.{name}.{key} {} ns",
                stats[key]
            );
        }
    }
    serde_json::to_writer(&mut *output, &json!({"kind":"gateway-append-scale","build_profile":"release",
        "source":provenance,"operations":SCALE,"phases":phases,"samples_ns":data.times,
        "scope":"distinct logical operations over one real Cedar world, one explicit shared SDK program and append-only witness/provider; fresh evaluation per operation; independent full-log reconciliation after timing"})).map_err(|e|e.to_string())?;
    writeln!(output).map_err(|e| e.to_string())
}

fn scale_seed(manifest: ValidatedManifest) -> Option<(Case, SchemaSourceJson)> {
    manifest
        .cases
        .into_iter()
        .find(|case| case.expected == "allow" && case.expected_error_policies.is_empty())
        .map(|case| (case, manifest.schema))
}
