use super::{AuditAuthority, FactAuthority, ProviderJournal, Reconciliation, reconcile_recovery};
use crate::gateway::wire::simulation_key;
use crate::gateway::{FactBinding, Origin, Witness};

#[test]
fn verified_log_reuse_keeps_the_original_root_and_current_independent_floor() {
    let log = Witness::simulation();
    let history =
        crate::gateway::witness::verify_view(log.view(), &log.verifying_key(), 0).unwrap();
    let fact = FactBinding {
        issuer: "issuer".into(),
        subject: "subject".into(),
        audience: "audience".into(),
        source: "source".into(),
        field: "field".into(),
        value: "value".into(),
        generation: 0,
        origin: Origin::Observed,
        not_before: 0,
        expires_at: 1,
    };
    let facts = FactAuthority::new(
        vec![fact],
        [("issuer".into(), *simulation_key(3).verifying_key())].into(),
        0,
    )
    .unwrap();
    let mut authority = AuditAuthority {
        gateway_key: *simulation_key(3).verifying_key(),
        log_key: log.verifying_key(),
        facts,
        minimum_size: 0,
        review_trust: None,
        prepared_publications: None,
    };
    let journal = ProviderJournal::default();
    assert_eq!(
        reconcile_recovery(&journal, &[], &history, &authority, None, None),
        Reconciliation::default()
    );
    authority.log_key = *simulation_key(7).verifying_key();
    assert!(reconcile_recovery(&journal, &[], &history, &authority, None, None).invalid_log);
    authority.log_key = log.verifying_key();
    authority.minimum_size = 1;
    assert!(reconcile_recovery(&journal, &[], &history, &authority, None, None).invalid_log);
}
