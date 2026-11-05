use serde_json::{Value, json};
use std::io::Write;
use std::process::{Command, Stdio};

#[test]
#[ignore = "requires actual Lean Delta output; run just check-reviewed-effects"]
fn reviewed_stdio_process_executes_the_published_revision_and_shadow_stays_read_only() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.lake/build/reviewed-effects/agent-payment-validated.json");
    let fixture: Value = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    let (index, case) = fixture["groups"]
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
        .find_map(|(index, group)| {
            group["plan"]["stages"]["entries"]["restored"]["cases"]
                .as_array()
                .unwrap()
                .iter()
                .find(|case| {
                    case["expected"] == "allow" && case["expected_error_policies"] == json!([])
                })
                .map(|case| (index, case.clone()))
        })
        .unwrap();
    for mode in ["--enforce", "--shadow"] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_cedar-poo-bridge"))
            .args([
                "gateway-reviewed-stdio",
                path.to_str().unwrap(),
                &index.to_string(),
                mode,
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        {
            let mut input = child.stdin.take().unwrap();
            for id in [1, 2] {
                writeln!(input,"{}",json!({"jsonrpc":"2.0","id":id,"method":"tools/call","params":{"name":case["name"],"arguments":case["request"]["context"],"_meta":{
                "io.modelcontextprotocol/protocolVersion":"2026-07-28","io.modelcontextprotocol/clientInfo":{"name":"reviewed-process-test","version":"1"},"io.modelcontextprotocol/clientCapabilities":{}}}})).unwrap();
            }
        }
        let output = child.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let responses: Vec<Value> = String::from_utf8(output.stdout)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        assert_eq!(responses.len(), 2);
        let content = &responses[0]["result"]["structuredContent"];
        if mode == "--enforce" {
            assert_eq!(content["outcome"]["receipted"], true);
            assert_eq!(responses[1]["result"]["isError"], true);
            let receipt: cedar_poo_runtime::gateway::Signed =
                serde_json::from_value(content["receipt"].clone()).unwrap();
            let record: Value = serde_json::from_slice(&receipt.payload).unwrap();
            assert_eq!(record["publications"].as_array().unwrap().len(), 2);
            let commit: cedar_poo_runtime::gateway::Signed =
                serde_json::from_value(record["commit"].clone()).unwrap();
            let precommit: Value = serde_json::from_slice(&commit.payload).unwrap();
            assert_eq!(precommit["review"]["epoch"], 9);
            assert_ne!(precommit["review"]["before"], precommit["review"]["after"]);
        } else {
            assert_eq!(content["would_deny"], false);
            assert!(content.get("receipt").is_none());
            assert_eq!(
                responses[1]["result"]["structuredContent"]["would_deny"],
                false
            );
        }
    }
}
