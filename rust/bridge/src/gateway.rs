//! Whole-catalog protocol qualification and a bounded MCP simulation entrypoint.
use cedar_poo_runtime::gateway::{
    EffectIo, Envelope, Fault, Outcome, ProviderJournal, Reconciliation, Simulator, Witness,
    reconcile,
};
use cedar_poo_runtime::{Case, ValidatedManifest};
use serde::Deserialize;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::io::{BufRead, Read, Write};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Oracle {
    format_version: u64,
    protocol: cedar_poo_runtime::gateway::Version,
    cases: Vec<OracleCase>,
    audit_cases: Vec<AuditCase>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AuditCase {
    fault: String,
    expected: Reconciliation,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct OracleCase {
    fault: Fault,
    cedar_allowed: bool,
    expected: Outcome,
}

pub(crate) fn replay(
    input: &str,
    oracle_path: &str,
    output: &mut impl Write,
) -> Result<(), String> {
    // Preserve independent full catalogue/data/cross-artifact validation.
    let original = crate::catalog::replay(input)?;
    let oracle: Oracle =
        serde_json::from_str(&std::fs::read_to_string(oracle_path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    if oracle.format_version != 1
        || oracle.protocol.major != 1
        || oracle.protocol.minor != 0
        || (oracle.cases.len() != 64 || oracle.audit_cases.len() != 13)
    {
        return Err("unsupported/incomplete protocol oracle".into());
    }
    let document = crate::catalog_input::document(input)?;
    write!(
        output,
        "{{\"format_version\":1,\"catalogue_entries\":51,\"outcomes\":["
    )
    .map_err(|e| e.to_string())?;
    let mut rows = 0usize;
    let mut entries = Vec::new();
    let mut excluded = Vec::new();
    for (name, raw) in &document.entries {
        let fields = crate::catalog_input::fields(raw);
        if fields.contains_key("cases") {
            if crate::catalog_input::is_schema_bound(&fields) {
                let manifest = document.sources.validated_manifest(raw)?;
                qualify(
                    name,
                    &manifest.cases,
                    Some(&manifest.schema),
                    &oracle,
                    &mut rows,
                    output,
                )?;
            } else {
                let manifest = document.sources.manifest(raw)?;
                qualify(name, &manifest.cases, None, &oracle, &mut rows, output)?;
            }
            entries.push(name.clone());
        } else if name == "attested-schema-evolution" {
            let bundle = document.sources.evolution(raw)?;
            qualify(
                &format!("{name}/before"),
                &bundle.before.cases,
                Some(&bundle.before.schema),
                &oracle,
                &mut rows,
                output,
            )?;
            qualify(
                &format!("{name}/after"),
                &bundle.after.cases,
                Some(&bundle.after.schema),
                &oracle,
                &mut rows,
                output,
            )?;
            entries.push(name.clone());
        } else if [
            "pseudonymization-deployable",
            "pseudonymization-tabular",
            "claim-settlement-handoff",
        ]
        .contains(&name.as_str())
        {
            excluded.push(name.clone());
        } else {
            return Err(format!("unclassified protocol catalogue entry: {name}"));
        }
    }
    if entries.len() != 48
        || excluded.len() != 3
        || original.as_object().map_or(0, |v| v.len()) != 51
    {
        return Err("incomplete domain coverage".into());
    }
    writeln!(
        output,
        "],\"covered_entries\":{},\"data_or_artifact_entries\":{},\"outcome_count\":{rows}}}",
        serde_json::to_string(&entries).map_err(|e| e.to_string())?,
        serde_json::to_string(&excluded).map_err(|e| e.to_string())?
    )
    .map_err(|e| e.to_string())?;
    output.flush().map_err(|e| e.to_string())
}
fn qualify(
    name: &str,
    cases: &[Case],
    schema: Option<&cedar_poo_core::SchemaSourceJson>,
    oracle: &Oracle,
    rows: &mut usize,
    output: &mut impl Write,
) -> Result<(), String> {
    let mut audited = false;
    for case in cases {
        let (base, expected_allow) = qualify_effects(name, case, schema, oracle, rows, output)?;
        if expected_allow && !audited {
            qualify_audits(name, case, &base, &oracle.audit_cases, rows, output)?;
            audited = true;
        }
    }
    eprintln!(
        "EFFECT-PROTOCOL-ENTRY: {name}; cases={}; outcomes={rows}",
        cases.len()
    );
    Ok(())
}

fn qualify_effects(
    name: &str,
    case: &Case,
    schema: Option<&cedar_poo_core::SchemaSourceJson>,
    oracle: &Oracle,
    rows: &mut usize,
    output: &mut impl Write,
) -> Result<(Simulator, bool), String> {
    let base = Simulator::new(case, schema)?;
    // Raw evaluation is retained as a negative control, not silently promoted
    // into a schema-qualified Production admission.
    let expected_allow =
        schema.is_some() && case.expected == "allow" && case.expected_error_policies.is_empty();
    for sample in oracle
        .cases
        .iter()
        .filter(|row| row.cedar_allowed == expected_allow)
    {
        let simulator = base.fork_simulation()?;
        let (actual, reconciliation) = simulator.run(sample.fault)?;
        if actual != sample.expected {
            return Err(format!(
                "protocol mismatch {name}/{} {:?}: {actual:?} != {:?}",
                case.name, sample.fault, sample.expected
            ));
        }
        let missing = usize::from(actual.unknown);
        if reconciliation.unresolved_precommits.len() != missing
            || reconciliation.missing_receipts.len() != missing
            || !reconciliation.missing_actions.is_empty()
            || !reconciliation.duplicates.is_empty()
            || !reconciliation.mismatched.is_empty()
            || reconciliation.invalid_receipts != 0
            || reconciliation.invalid_log
        {
            return Err(format!(
                "independent reconciliation mismatch: {name}/{}",
                case.name
            ));
        }
        if *rows != 0 {
            write!(output, ",").map_err(|e| e.to_string())?;
        }
        serde_json::to_writer(&mut *output,&json!({"kind":"effect","entry":name,"case":case.name,"schema_qualified":schema.is_some(),"fault":sample.fault,"outcome":actual,"reconciliation":reconciliation})).map_err(|e|e.to_string())?;
        *rows += 1;
    }
    Ok((base, expected_allow))
}

fn bind_audit_expected(
    mut report: Reconciliation,
    operation: &str,
) -> Result<Reconciliation, String> {
    for item in [
        &mut report.unresolved_precommits,
        &mut report.missing_receipts,
        &mut report.missing_actions,
        &mut report.mismatched,
        &mut report.duplicates,
    ]
    .into_iter()
    .flatten()
    {
        if item != "operation" {
            return Err("unbound audit oracle operation".into());
        }
        *item = operation.to_owned();
    }
    Ok(report)
}

fn qualify_audits(
    name: &str,
    case: &Case,
    base: &Simulator,
    samples: &[AuditCase],
    rows: &mut usize,
    output: &mut impl Write,
) -> Result<(), String> {
    for sample in samples {
        let simulator = base.fork_simulation()?;
        let envelope = simulator.envelope();
        let mut witness = Witness::simulation();
        let mut provider = ProviderJournal::default();
        let (_, receipt) = simulator.execute(
            simulator.prepare(&envelope)?,
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: false,
            },
        )?;
        let mut receipts = vec![receipt.ok_or("missing clean outcome")?];
        let mut observed_snapshot = witness.snapshot();
        match sample.fault.as_str() {
            "clean" => (),
            "precommitOnly" => {
                receipts.clear();
                provider.actions.clear();
            }
            "missingReceipt" => receipts.clear(),
            "missingAction" => provider.actions.clear(),
            "mismatch" => provider.actions[0].effect.payload = "changed".into(),
            "duplicateAction" => provider.actions.push(provider.actions[0].clone()),
            "duplicateReceipt" => receipts.push(receipts[0].clone()),
            "duplicatePrecommit" | "supersededPrecommit" => {
                // Independent observed windows deliberately expose ambiguous
                // signed intents; one outcome must never resolve both entries.
                let next = base.fork_simulation()?;
                let next_envelope = next.envelope();
                let mut next_provider = ProviderJournal::default();
                let (_, next_receipt) = next.execute(
                    next.prepare(&next_envelope)?,
                    &next_envelope,
                    EffectIo {
                        witness: &mut witness,
                        provider: &mut next_provider,
                        crash_after_send: false,
                    },
                )?;
                if sample.fault == "duplicatePrecommit" {
                    receipts = vec![next_receipt.ok_or("missing later outcome")?];
                    provider = next_provider;
                }
                observed_snapshot = witness.snapshot();
            }
            "invalidReceipt" => receipts[0].signature[0] ^= 1,
            "unanchoredReceipt" => {
                // This control is a separately trusted empty log, not rollback
                // below the original witness's retained checkpoint floor.
                witness = Witness::simulation();
                observed_snapshot = witness.snapshot();
            }
            "rewrittenLog" => observed_snapshot.entries[0].payload[0] ^= 1,
            "truncatedLog" => observed_snapshot.entries.clear(),
            _ => return Err("unclassified reconciliation control".into()),
        }
        let actual = reconcile(
            &provider,
            &receipts,
            &observed_snapshot,
            &simulator.audit_authority(&witness),
        );
        let expected = bind_audit_expected(sample.expected.clone(), &envelope.effect.operation)?;
        if actual != expected {
            return Err(format!(
                "audit mismatch {name}/{}: {actual:?} != {expected:?}",
                sample.fault
            ));
        }
        if *rows != 0 {
            write!(output, ",").map_err(|e| e.to_string())?;
        }
        serde_json::to_writer(&mut *output,&json!({"kind":"audit","entry":name,"case":case.name,"fault":sample.fault,"reconciliation":actual})).map_err(|e|e.to_string())?;
        *rows += 1;
    }
    Ok(())
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Rpc {
    jsonrpc: String,
    id: Option<Value>,
    method: String,
    #[serde(default)]
    params: Value,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Call {
    name: String,
    arguments: Value,
    #[serde(rename = "_meta")]
    meta: CallMeta,
}
#[derive(Deserialize)]
struct CallMeta {
    #[serde(rename = "io.modelcontextprotocol/protocolVersion")]
    version: String,
    #[serde(rename = "io.modelcontextprotocol/clientInfo")]
    client_info: Value,
    #[serde(rename = "io.modelcontextprotocol/clientCapabilities")]
    capabilities: Value,
    #[serde(rename = "org.hardenedlinux/cedar-envelope")]
    evidence: Option<Envelope>,
    #[serde(flatten)]
    _extensions: BTreeMap<String, Value>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CallRequest {
    jsonrpc: String,
    id: Value,
    method: String,
    params: Call,
}
/// A fixed profile simulation. The caller cannot select trusted facts, policies
/// or scope from its arguments. It forwards no external network traffic.
pub(crate) struct McpSimulation {
    profiles: BTreeMap<String, (Case, Simulator)>,
    witness: Witness,
    provider: ProviderJournal,
    enforce: bool,
}
impl McpSimulation {
    pub(crate) fn new(manifest: ValidatedManifest, enforce: bool) -> Result<Self, String> {
        let mut profiles = BTreeMap::new();
        for case in manifest.cases {
            let simulator = Simulator::new(&case, Some(&manifest.schema))?;
            if profiles
                .insert(case.name.clone(), (case, simulator))
                .is_some()
            {
                return Err("duplicate mapped tool".into());
            }
        }
        Ok(Self {
            profiles,
            witness: Witness::simulation(),
            provider: ProviderJournal::default(),
            enforce,
        })
    }
    pub(crate) fn from_profiles(
        profiles: Vec<(Case, Simulator)>,
        enforce: bool,
    ) -> Result<Self, String> {
        let mut selected = BTreeMap::new();
        for (case, simulator) in profiles {
            if selected
                .insert(case.name.clone(), (case, simulator))
                .is_some()
            {
                return Err("duplicate reviewed tool name".into());
            }
        }
        Ok(Self {
            profiles: selected,
            witness: Witness::simulation(),
            provider: ProviderJournal::default(),
            enforce,
        })
    }
    pub(crate) fn handle(&mut self, line: &str) -> Option<Value> {
        let request: Rpc = match serde_json::from_str(line) {
            Ok(v) => v,
            Err(_) => return Some(error(Value::Null, -32700, "Invalid JSON-RPC message")),
        };
        let id = request.id?;
        if request.jsonrpc != "2.0"
            || !(id.is_string() || id.as_i64().is_some() || id.as_u64().is_some())
        {
            return Some(error(id, -32600, "Invalid request"));
        }
        let meta = &request.params["_meta"];
        if meta["io.modelcontextprotocol/protocolVersion"] != "2026-07-28" {
            return Some(
                json!({"jsonrpc":"2.0","id":id,"error":{"code":-32022,"message":"Unsupported protocol version","data":{"supported":["2026-07-28"],"requested":meta["io.modelcontextprotocol/protocolVersion"]}}}),
            );
        }
        if !meta["io.modelcontextprotocol/clientInfo"].is_object()
            || !meta["io.modelcontextprotocol/clientCapabilities"].is_object()
        {
            return Some(error(id, -32602, "Missing client metadata"));
        }
        let result = match request.method.as_str() {
            "ping" => json!({"resultType":"complete"}),
            "server/discover" => {
                json!({"resultType":"complete","supportedVersions":["2026-07-28"],"capabilities":{"tools":{}},"_meta":{"io.modelcontextprotocol/serverInfo":{"name":"cedar-poo-simulation","version":"1.0.0"}},"instructions":"Simulation only; explicit signed evidence required; no external forwarding."})
            }
            "tools/list" => {
                json!({"resultType":"complete","tools":self.profiles.iter().map(|(name,(case,_))|json!({"name":name,"inputSchema":{"type":"object","const":case.request.context},"description":"Exact schema-qualified simulation operation"})).collect::<Vec<_>>()})
            }
            "tools/call" => {
                // Decode security-bearing fields directly from original bytes;
                // a Value round trip would erase duplicate envelope fields.
                let typed: CallRequest = match serde_json::from_str(line) {
                    Ok(v) => v,
                    Err(_) => return Some(error(id, -32602, "Invalid tool call")),
                };
                if typed.jsonrpc != "2.0" || typed.id != id || typed.method != "tools/call" {
                    return Some(error(id, -32600, "Invalid typed request"));
                }
                let call = typed.params;
                if call.meta.version != "2026-07-28"
                    || !call.meta.client_info.is_object()
                    || !call.meta.capabilities.is_object()
                {
                    return Some(error(id, -32602, "Invalid client metadata"));
                }
                let Some((case, simulator)) = self.profiles.get(&call.name) else {
                    return Some(error(id, -32602, "Unmapped tool"));
                };
                use cedar_poo_core::JsonSourceIdentity;
                if !call.arguments.same_source(&case.request.context) {
                    return Some(error(id, -32602, "Projected arguments changed"));
                }
                let supplied = request.params["_meta"]
                    .get("org.hardenedlinux/cedar-envelope")
                    .is_some();
                let envelope = match call.meta.evidence {
                    Some(value) => value,
                    None if !supplied => simulator.envelope(),
                    None => return Some(error(id, -32602, "Malformed evidence")),
                };
                let prepared = simulator.prepare(&envelope);
                if !self.enforce {
                    json!({"resultType":"complete","isError":false,"content":[{"type":"text","text":"Shadow observation; no enforcing receipt or simulated effect issued"}],"structuredContent":{"mode":"shadow","would_deny":prepared.is_err()}})
                } else {
                    match prepared.and_then(|handle| {
                        simulator.execute(
                            handle,
                            &envelope,
                            EffectIo {
                                witness: &mut self.witness,
                                provider: &mut self.provider,
                                crash_after_send: false,
                            },
                        )
                    }) {
                        Ok((outcome, receipt)) => {
                            let message = if outcome.receipted {
                                "Simulated effect completed"
                            } else {
                                "Simulated effect did not produce a complete outcome"
                            };
                            json!({"resultType":"complete","isError":!outcome.receipted,"content":[{"type":"text","text":message}],"structuredContent":{"outcome":outcome,"receipt":receipt}})
                        }
                        Err(_) => {
                            json!({"resultType":"complete","isError":true,"content":[{"type":"text","text":"Current effect admission refused"}]})
                        }
                    }
                }
            }
            _ => return Some(error(id, -32601, "Method not supported")),
        };
        Some(json!({"jsonrpc":"2.0","id":id,"result":result}))
    }
}
fn error(id: Value, code: i64, message: &str) -> Value {
    if id.is_null() {
        json!({"jsonrpc":"2.0","error":{"code":code,"message":message}})
    } else {
        json!({"jsonrpc":"2.0","id":id,"error":{"code":code,"message":message}})
    }
}
pub(crate) fn stdio(path: &str, enforce: bool) -> Result<(), String> {
    let manifest = serde_json::from_str(&std::fs::read_to_string(path).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    serve(McpSimulation::new(manifest, enforce)?)
}
pub(crate) fn serve(mut server: McpSimulation) -> Result<(), String> {
    let input = std::io::stdin();
    let mut input = input.lock();
    let mut output = std::io::stdout().lock();
    loop {
        let mut frame = Vec::new();
        let count = (&mut input)
            .take(1_048_577)
            .read_until(b'\n', &mut frame)
            .map_err(|e| e.to_string())?;
        if count == 0 {
            break;
        }
        if count > 1_048_576 {
            return Err("MCP frame exceeds 1 MiB".into());
        }
        let line = std::str::from_utf8(&frame).map_err(|e| e.to_string())?;
        if let Some(response) = server.handle(line) {
            serde_json::to_writer(&mut output, &response).map_err(|e| e.to_string())?;
            writeln!(output).map_err(|e| e.to_string())?;
            output.flush().map_err(|e| e.to_string())?;
        }
    }
    Ok(())
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AuditTrust {
    gateway_key: Vec<u8>,
    log_key: Vec<u8>,
    minimum_size: u64,
    facts: Vec<cedar_poo_runtime::gateway::FactBinding>,
    source_keys: BTreeMap<String, Vec<u8>>,
    observed_at: u64,
    review_key: Option<Vec<u8>>,
    approval_key: Option<Vec<u8>>,
    provider_key: Option<Vec<u8>>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AuditInput {
    snapshot: cedar_poo_runtime::gateway::LogSnapshot,
    journal: ProviderJournal,
    receipts: Vec<cedar_poo_runtime::gateway::Signed>,
    provider_outcomes: Option<Vec<cedar_poo_runtime::gateway::Signed>>,
}
pub(crate) fn audit(input: &str, trust_path: &str) -> Result<Value, String> {
    let trust: AuditTrust =
        serde_json::from_str(&std::fs::read_to_string(trust_path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    let input: AuditInput = serde_json::from_str(input).map_err(|e| e.to_string())?;
    let gateway_key = cedar_poo_runtime::gateway::public_key(&trust.gateway_key)?;
    let log_key = cedar_poo_runtime::gateway::public_key(&trust.log_key)?;
    let source_keys = trust
        .source_keys
        .into_iter()
        .map(|(name, key)| Ok((name, cedar_poo_runtime::gateway::public_key(&key)?)))
        .collect::<Result<_, String>>()?;
    let facts = cedar_poo_runtime::gateway::FactAuthority::new(
        trust.facts,
        source_keys,
        trust.observed_at,
    )?;
    let authority = cedar_poo_runtime::gateway::AuditAuthority {
        prepared_publications: None,
        gateway_key,
        log_key,
        facts,
        minimum_size: trust.minimum_size,
        review_trust: match (trust.review_key, trust.approval_key) {
            (None, None) => None,
            (Some(review), Some(approval)) => Some(cedar_poo_runtime::gateway::ReviewTrust {
                review_key: cedar_poo_runtime::gateway::public_key(&review)?,
                approval_key: cedar_poo_runtime::gateway::public_key(&approval)?,
            }),
            _ => return Err("both independent review and approval keys are required".into()),
        },
    };
    let report = match (trust.provider_key, input.provider_outcomes) {
        (None, None) => cedar_poo_runtime::gateway::reconcile(
            &input.journal,
            &input.receipts,
            &input.snapshot,
            &authority,
        ),
        (Some(key), Some(outcomes)) if input.receipts.is_empty() => {
            let provider_key = cedar_poo_runtime::gateway::public_key(&key)?;
            cedar_poo_runtime::gateway::reconcile_provider_outcomes(
                &input.journal,
                &outcomes,
                &input.snapshot,
                cedar_poo_runtime::gateway::ProviderAuditTrust {
                    authority: &authority,
                    provider_key: &provider_key,
                },
            )
        }
        _ => {
            return Err(
                "completion evidence differs from independently configured audit mode".into(),
            );
        }
    };
    serde_json::to_value(report).map_err(|e| e.to_string())
}
