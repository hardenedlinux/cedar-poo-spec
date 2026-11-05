use super::{FirstCommit, settlement_race};
use serde::{Deserialize, Serialize};

#[derive(Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RecoveryRound {
    pub handoffs_after_first: u64,
    pub handoffs_after_second: u64,
    pub handoffs_after_confirmation: u64,
    pub expected_advances: u64,
    pub expected_crashes: u64,
}

impl RecoveryRound {
    pub fn baseline() -> Self {
        Self {
            handoffs_after_first: 2,
            handoffs_after_second: 2,
            handoffs_after_confirmation: 2,
            expected_advances: 6,
            expected_crashes: 3,
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RecoveryPlan {
    format: String,
    scope: String,
    rounds: Vec<RecoveryRound>,
}

#[test]
#[ignore = "requires the Lean-generated recovery plan from just check-gateway"]
fn lean_plan_drives_both_native_commit_orders() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.lake/build/gateway-recovery-plan.json");
    let plan: RecoveryPlan = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    assert_eq!(plan.format, "cedar-poo-legacy-recovery-plan-v1");
    assert_eq!(plan.scope, "settled-read-only-recovery");
    assert_eq!(plan.rounds.len(), 3);
    for round in &plan.rounds {
        assert!(round.handoffs_after_first > 0);
        assert!(round.handoffs_after_second > 0);
        assert!(round.handoffs_after_confirmation > 0);
        assert_eq!(
            round.expected_advances,
            round.handoffs_after_first
                + round.handoffs_after_second
                + round.handoffs_after_confirmation
        );
        assert_eq!(round.expected_crashes, 3);
    }
    settlement_race(
        "model-aligned-takeover",
        true,
        Some(FirstCommit::Takeover),
        &plan.rounds,
    );
    settlement_race(
        "model-aligned-migration",
        true,
        Some(FirstCommit::Migration),
        &plan.rounds,
    );
}
