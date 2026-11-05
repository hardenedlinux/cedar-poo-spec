//! Authenticated review, separate expansion approval and publication lineage.
mod authority;
mod record;
mod verification;
pub use authority::ReviewAuthority;
pub use record::{
    AnalysisKind, GainApproval, PublicationDelivery, PublicationRecord, PublicationView,
    ReleaseIdentity, ReviewRecord,
};
pub use verification::{ReviewTrust, publication_matches, verify_publications};
mod preparation;
pub use preparation::PreparedPublications;
