#![cfg(feature = "gateway")]
use cedar_poo_runtime::gateway::{EffectIo, ProviderJournal, Simulator, Witness};
use cedar_poo_runtime::{Case, ValidatedManifest};
use serde_json::{Value, json};
use std::io::Write;
use std::process::{Command, Stdio};
fn fixture() -> (ValidatedManifest, Case) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.lake/build");
    let input: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("gateway-production-current-use.json")).unwrap(),
    )
    .unwrap();
    let cases: Vec<Case> = serde_json::from_value(input["manifest"]["cases"].clone()).unwrap();
    let case = cases
        .into_iter()
        .find(|case| case.revision == "health-disclosure" && case.expected == "allow")
        .unwrap();
    let manifest = ValidatedManifest {
        schema: serde_json::from_value(input["schemas"]["health-disclosure"].clone()).unwrap(),
        cases: vec![case.clone()],
    };
    (manifest, case)
}
fn meta() -> Value {
    json!({"io.modelcontextprotocol/protocolVersion":"2026-07-28","io.modelcontextprotocol/clientInfo":{"name":"native-test","version":"1"},"io.modelcontextprotocol/clientCapabilities":{}})
}
#[test]
#[ignore = "requires Production vectors; run just check-effect-protocol"]
fn gateway_stdio_process_binds_current_sources_and_mode() {
    let (manifest, case) = fixture();
    let temp = std::env::temp_dir().join(format!("cedar-gateway-mcp-{}.json", std::process::id()));
    // Use original producer JSON for Case; the runtime intentionally exposes no
    // unchecked serializer that could pretend an arbitrary expected decision.
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.lake/build/gateway-production-current-use.json");
    let producer: Value = serde_json::from_str(&std::fs::read_to_string(root).unwrap()).unwrap();
    let raw = producer["manifest"]["cases"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["name"] == case.name)
        .unwrap();
    std::fs::write(
        &temp,
        serde_json::to_vec(&json!({"schema":&*manifest.schema,"cases":[raw]})).unwrap(),
    )
    .unwrap();
    for mode in ["--enforce", "--shadow"] {
        let mut requests = vec![
            json!({"jsonrpc":"2.0","id":"discover","method":"server/discover","params":{"_meta":meta()}}),
        ];
        requests.push(json!({"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"unmapped","arguments":{},"_meta":meta()}}));
        requests.push(json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":case.name,"arguments":case.request.context,"_meta":meta()}}));
        requests.push(json!({"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":case.name,"arguments":case.request.context,"_meta":meta()}}));
        let simulator = Simulator::new(&case, Some(&manifest.schema)).unwrap();
        let mut bad_meta = meta();
        let mut forged = simulator.envelope();
        forged.facts[0].signature[0] ^= 1;
        bad_meta["org.hardenedlinux/cedar-envelope"] = serde_json::to_value(forged).unwrap();
        requests.push(json!({"jsonrpc":"2.0","id":4,"method":"tools/call","params":{"name":case.name,"arguments":case.request.context,"_meta":bad_meta}}));
        let mut wrong_version = meta();
        wrong_version["io.modelcontextprotocol/protocolVersion"] = json!("2099-01-01");
        let invalid_version = json!({"jsonrpc":"2.0","id":"version","method":"tools/call","params":{"name":case.name,"arguments":case.request.context,"_meta":wrong_version}});
        let changed_arguments = json!({"jsonrpc":"2.0","id":"arguments","method":"tools/call","params":{"name":case.name,"arguments":{"__unmapped":true},"_meta":meta()}});
        let mut duplicate_meta = meta();
        duplicate_meta["org.hardenedlinux/cedar-envelope"] =
            serde_json::to_value(simulator.envelope()).unwrap();
        let duplicate = json!({"jsonrpc":"2.0","id":"duplicate","method":"tools/call","params":{"name":case.name,"arguments":case.request.context,"_meta":duplicate_meta}})
            .to_string().replace("\"major\":1", "\"major\":1,\"major\":1");
        assert!(duplicate.contains("\"major\":1,\"major\":1"));
        let mut child = Command::new(env!("CARGO_BIN_EXE_cedar-poo-bridge"))
            .args(["gateway-stdio", temp.to_str().unwrap(), mode])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        {
            let mut stdin = child.stdin.take().unwrap();
            // Refusals precede the successful use; a spent grant cannot hide a
            // malformed-wire acceptance defect.
            writeln!(stdin, "{invalid_version}").unwrap();
            writeln!(stdin, "{changed_arguments}").unwrap();
            writeln!(stdin, "{duplicate}").unwrap();
            for request in requests {
                writeln!(stdin, "{request}").unwrap();
            }
        }
        let output = child.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let rows: Vec<Value> = String::from_utf8(output.stdout)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        assert_eq!(rows.len(), 8);
        assert_eq!(rows[0]["error"]["code"], -32022);
        assert_eq!(rows[1]["error"]["code"], -32602);
        assert_eq!(rows[2]["error"]["code"], -32602);
        let rows = &rows[3..];
        assert_eq!(
            rows[0]["result"]["supportedVersions"],
            json!(["2026-07-28"])
        );
        assert!(rows[1]["error"].is_object());
        if mode == "--enforce" {
            assert_eq!(
                rows[2]["result"]["structuredContent"]["outcome"]["sent"],
                true
            );
            assert_eq!(rows[3]["result"]["isError"], true);
            assert_eq!(rows[4]["result"]["isError"], true);
        } else {
            assert_eq!(rows[2]["result"]["structuredContent"]["would_deny"], false);
            assert!(
                rows[2]["result"]["structuredContent"]
                    .get("receipt")
                    .is_none()
            );
            assert_eq!(rows[4]["result"]["structuredContent"]["would_deny"], true);
        }
    }
    std::fs::remove_file(temp).unwrap();
}
#[test]
#[ignore = "requires Production vectors; run just check-effect-protocol"]
fn gateway_public_auditor_cli_requires_only_public_trust_material() {
    let (manifest, case) = fixture();
    let simulator = Simulator::new(&case, Some(&manifest.schema)).unwrap();
    let envelope = simulator.envelope();
    let mut witness = Witness::simulation();
    let mut provider = ProviderJournal::default();
    let (_, receipt) = simulator
        .execute(
            simulator.prepare(&envelope).unwrap(),
            &envelope,
            EffectIo {
                witness: &mut witness,
                provider: &mut provider,
                crash_after_send: false,
            },
        )
        .unwrap();
    let (facts, source_keys, observed_at) = simulator.fact_authority().public_material();
    let trust = json!({"gateway_key":simulator.verifying_key().to_encoded_point(false).as_bytes(),"log_key":witness.verifying_key().to_encoded_point(false).as_bytes(),"minimum_size":1,"facts":facts,"source_keys":source_keys,"observed_at":observed_at});
    let temp =
        std::env::temp_dir().join(format!("cedar-gateway-audit-{}.json", std::process::id()));
    std::fs::write(&temp, serde_json::to_vec(&trust).unwrap()).unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_cedar-poo-bridge"))
        .args(["gateway-reconcile", temp.to_str().unwrap()])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    {
        let mut stdin = child.stdin.take().unwrap();
        write!(
            stdin,
            "{}",
            json!({"snapshot":witness.snapshot(),"journal":provider,"receipts":[receipt.unwrap()]})
        )
        .unwrap();
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["invalid_receipts"], 0);
    assert_eq!(report["invalid_log"], false);
    assert_eq!(report["missing_receipts"], json!([]));
    std::fs::remove_file(temp).unwrap();
}
