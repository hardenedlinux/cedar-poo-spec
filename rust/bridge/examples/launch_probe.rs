//! Diagnostic main-entry timing; never used to qualify ordinary latency.
use std::time::{Instant, SystemTime, UNIX_EPOCH};
fn unix_ns() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("valid realtime clock")
        .as_nanos()
}
fn main() {
    let entry = unix_ns();
    let started = Instant::now();
    eprintln!(
        "{}",
        serde_json::json!({"observation":"native-main-entry","unix_ns":entry,"pid":std::process::id()})
    );
    let result = cedar_poo_bridge::cli::run_observed();
    eprintln!(
        "{}",
        serde_json::json!({"observation":"native-main-return","unix_ns":unix_ns(),"elapsed_ns":started.elapsed().as_nanos(),"success":result.is_ok()})
    );
    if let Err(error) = result {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
