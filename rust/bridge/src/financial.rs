//! Replay-only cross-domain handoff simulation; no credentials or settlement effects are issued.
use cedar_policy::EntityUid;
use cedar_poo_core::handoff::{Grant, Scope};
use cedar_poo_runtime::{SchemaBoundReceipt, ValidatedManifest};
use serde::Deserialize;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::str::FromStr;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct WireScope {
    case_id: String,
    claim_digest: String,
    source_actor: String,
    target_actor: String,
    source_root: String,
    target_root: String,
    credential_mode: String,
}
impl WireScope {
    fn checked(&self) -> Result<Scope<EntityUid>, String> {
        Ok(Scope {
            case_id: self.case_id.clone(),
            claim_digest: self.claim_digest.clone(),
            source_actor: EntityUid::from_str(&self.source_actor).map_err(|e| e.to_string())?,
            target_actor: EntityUid::from_str(&self.target_actor).map_err(|e| e.to_string())?,
            source_root: self.source_root.clone(),
            target_root: self.target_root.clone(),
            credential_mode: self
                .credential_mode
                .clone()
                .try_into()
                .map_err(str::to_owned)?,
        })
    }
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct WireGrant {
    scope: WireScope,
    epoch: u64,
    expires_at: u64,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct BankCall {
    case_name: String,
    phase: String,
    lob: String,
    origin: String,
    action: String,
    required: Option<Vec<String>>,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Scenario {
    name: String,
    scope: WireScope,
    configured: Option<WireScope>,
    grant: WireGrant,
    current_epoch: u64,
    now: u64,
    claims: Vec<String>,
    banking: Vec<BankCall>,
    expected_gateway: bool,
    expected_admitted: bool,
}

fn required(mode: &str, lob: &str) -> Option<Vec<&'static str>> {
    let mut keys = match mode {
        "SourceM2M" => vec!["m2mGatewayToLob", "jwtAtLob"],
        "GatewayBoundM2M" => vec!["gatewayInWorkloadChain", "m2mGatewayToLob", "jwtAtLob"],
        "OBO" => vec!["oboGatewayToLob", "userAtLob", "jwtAtLob"],
        _ => return None,
    };
    keys.extend(["userJwtAgentToGateway", "cedarAtGateway"]);
    keys.push(match lob {
        "Retail" => "retailDataPlane",
        "Transaction" => "transactionDataPlane",
        "Lending" => "lendingDataPlane",
        _ => return None,
    });
    Some(keys)
}

type CaseIndex<'a> = BTreeMap<String, (&'a cedar_poo_runtime::Case, &'a SchemaBoundReceipt)>;

fn index<'a>(
    manifest: &'a ValidatedManifest,
    receipts: &'a [SchemaBoundReceipt],
) -> Result<CaseIndex<'a>, String> {
    if manifest.cases.len() != receipts.len() {
        return Err("settlement receipt cardinality mismatch".into());
    }
    let mut result = BTreeMap::new();
    for (case, receipt) in manifest.cases.iter().zip(receipts) {
        if result.insert(case.name.clone(), (case, receipt)).is_some() {
            return Err("duplicate settlement case".into());
        }
    }
    Ok(result)
}

fn bound<'a>(
    index: &CaseIndex<'a>,
    name: &str,
    root: &str,
    actor: &EntityUid,
) -> Result<(&'a cedar_poo_runtime::Case, &'a SchemaBoundReceipt), String> {
    let (case, receipt) = index
        .get(name)
        .copied()
        .ok_or_else(|| format!("missing linked case {name}"))?;
    if case.revision != root
        || EntityUid::from_str(&case.request.principal).map_err(|e| e.to_string())? != *actor
    {
        return Err(format!("handoff case root/actor mismatch: {name}"));
    }
    Ok((case, receipt))
}

pub(crate) fn replay(
    value: Value,
    verified: &BTreeMap<String, (ValidatedManifest, Vec<SchemaBoundReceipt>)>,
) -> Result<Value, String> {
    let scenarios: Vec<Scenario> = serde_json::from_value(value).map_err(|e| e.to_string())?;
    if scenarios.is_empty() {
        return Err("empty claim-settlement handoff scenarios".into());
    }
    let (claims, claim_receipts) = verified
        .get("claim-settlement-claims")
        .ok_or("missing claims replay")?;
    let (banking, bank_receipts) = verified
        .get("claim-settlement-banking")
        .ok_or("missing banking replay")?;
    let claims_index = index(claims, claim_receipts)?;
    let banking_index = index(banking, bank_receipts)?;
    let mut names = BTreeSet::new();
    let mut referenced_claims = BTreeSet::new();
    let mut referenced_bank = BTreeSet::new();
    let mut output = Vec::new();
    for scenario in scenarios {
        if !names.insert(scenario.name.clone())
            || scenario.claims.len() != 2
            || scenario.banking.len() != 4
        {
            return Err("duplicate scenario or changed settlement topology".into());
        }
        let scope = scenario.scope.checked()?;
        let configured = scenario
            .configured
            .as_ref()
            .map(WireScope::checked)
            .transpose()?;
        let grant = Grant {
            scope: scenario.grant.scope.checked()?,
            epoch: scenario.grant.epoch,
            expires_at: scenario.grant.expires_at,
        };
        let mut gateway = true;
        for (index, name) in scenario.claims.iter().enumerate() {
            if name != &format!("{}-claims-{index}", scenario.name) {
                return Err("claims scenario/index binding mismatch".into());
            }
            if !referenced_claims.insert(name.clone()) {
                return Err("reused claims case binding".into());
            }
            let (_, receipt) = bound(&claims_index, name, &scope.source_root, &scope.source_actor)?;
            gateway &= receipt.replay.error_free_allow;
        }
        for (index, call) in scenario.banking.iter().enumerate() {
            if call.case_name != format!("{}-bank-{index}", scenario.name) {
                return Err("banking scenario/index binding mismatch".into());
            }
            if !referenced_bank.insert(call.case_name.clone()) {
                return Err("reused banking case binding".into());
            }
            let (phase, lob) = [
                ("balance-check", "Retail"),
                ("record-transfer", "Transaction"),
                ("debit-source", "Retail"),
                ("credit-destination", "Retail"),
            ][index];
            let (case, receipt) = bound(
                &banking_index,
                &call.case_name,
                &scope.target_root,
                &scope.target_actor,
            )?;
            if call.phase != phase
                || call.lob != lob
                || EntityUid::from_str(&call.origin).map_err(|e| e.to_string())?
                    != scope.target_actor
                || EntityUid::from_str(&call.action).map_err(|e| e.to_string())?
                    != EntityUid::from_str(&case.request.action).map_err(|e| e.to_string())?
            {
                return Err("bank phase/LOB/action/origin binding mismatch".into());
            }
            let expected = required(scope.credential_mode.as_str(), &call.lob);
            let actual = call
                .required
                .as_ref()
                .map(|items| items.iter().map(String::as_str).collect::<Vec<_>>());
            if actual != expected {
                return Err("banking requirement projection mismatch".into());
            }
            gateway &= receipt.replay.error_free_allow && expected.is_some();
        }
        let scope_allowed = configured.as_ref() == Some(&scope)
            && grant.admits(&scope, scenario.current_epoch, scenario.now);
        let admitted = gateway && scope_allowed;
        if gateway != scenario.expected_gateway || admitted != scenario.expected_admitted {
            return Err(format!(
                "claim-settlement Lean/Rust mismatch: {}",
                scenario.name
            ));
        }
        output.push(json!({"name":scenario.name,"gatewayAllows":gateway,"scopeAllows":scope_allowed,"admitted":admitted}));
    }
    if referenced_claims.len() != claims.cases.len() || referenced_bank.len() != banking.cases.len()
    {
        return Err("unreferenced settlement replay cases".into());
    }
    Ok(json!({"kind":"claim-settlement-handoff-simulation","scenarios":output}))
}
