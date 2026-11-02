//! Test-owned authority/store interpreter; no production Gateway backend.
use crate::{Manifest, replay_manifest};
use std::sync::{
    Arc, Barrier, Mutex,
    atomic::{AtomicUsize, Ordering},
};

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
struct Image {
    root: String,
    epoch: u64,
    mode: String,
    floor: u64,
    durable_root: String,
    durable_epoch: u64,
    durable_mode: String,
    unknown: bool,
}
struct Review {
    base: String,
    candidate: String,
    no_gain: bool,
    approved: bool,
}
impl Review {
    fn from_json(value: &serde_json::Value) -> Self {
        Self {
            base: value["base"].as_str().unwrap().into(),
            candidate: value["candidate"].as_str().unwrap().into(),
            no_gain: value["no_gain"].as_bool().unwrap(),
            approved: value["approved"].as_bool().unwrap(),
        }
    }
}
impl Image {
    fn initial(base: &str) -> Self {
        Self {
            root: base.into(),
            epoch: 7,
            mode: "enforcing".into(),
            floor: 7,
            durable_root: base.into(),
            durable_epoch: 7,
            durable_mode: "enforcing".into(),
            unknown: false,
        }
    }
    fn step(&mut self, command: u64, review: &Review) -> u64 {
        match command {
            0 | 6 => {
                if self.epoch == self.floor
                    && self.epoch == 7
                    && self.root == review.base
                    && self.mode == "enforcing"
                    && (review.no_gain || review.approved)
                {
                    self.root = review.candidate.clone();
                    self.epoch += 1; // Entry above fixes this modeled epoch to seven.
                    self.floor = self.epoch;
                    self.durable_root = self.root.clone();
                    self.durable_epoch = self.epoch;
                    self.durable_mode = self.mode.clone();
                    self.unknown |= command == 6;
                    return if command == 6 { 2 } else { 1 };
                }
            }
            1 | 2 | 5 => {
                let mode = match command {
                    1 => "observing",
                    2 => "disabled",
                    _ => "enforcing",
                };
                self.mode = mode.into();
                self.durable_mode = mode.into();
            }
            3 => {
                self.root = self.durable_root.clone();
                self.epoch = self.durable_epoch;
                self.mode = self.durable_mode.clone();
            }
            4 => {
                self.root = review.base.clone();
                self.epoch = 7;
                self.mode = "enforcing".into();
            }
            _ => panic!("undeclared command"),
        }
        0
    }
}
#[derive(Clone)]
struct Ticket {
    owner: Arc<()>,
    generation: u64,
}
struct Current {
    generation: u64,
    image: Image,
}
struct Authority {
    owner: Arc<()>,
    current: Mutex<Current>,
    review: Review,
}
#[derive(Debug, PartialEq, Eq)]
enum Attempt {
    Committed(u64),
    Stale,
    Denied,
    Missing,
    Exhausted,
    Foreign,
}
impl Attempt {
    fn code(&self) -> u64 {
        match self {
            Self::Committed(reply) => *reply,
            Self::Stale => 3,
            Self::Denied => 4,
            Self::Missing => 5,
            Self::Exhausted => 6,
            Self::Foreign => 7,
        }
    }
}
impl Authority {
    fn new(review: Review) -> Self {
        Self {
            owner: Arc::new(()),
            current: Mutex::new(Current {
                generation: 0,
                image: Image::initial(&review.base),
            }),
            review,
        }
    }
    fn capture(&self) -> Ticket {
        Ticket {
            owner: Arc::clone(&self.owner),
            generation: self.current.lock().unwrap().generation,
        }
    }
    fn publish(
        &self,
        ticket: Option<&Ticket>,
        lost: bool,
        observe: impl FnOnce(&Image),
    ) -> Attempt {
        let Some(ticket) = ticket else {
            return Attempt::Missing;
        };
        if !Arc::ptr_eq(&ticket.owner, &self.owner) {
            return Attempt::Foreign;
        }
        let mut current = self.current.lock().unwrap();
        if ticket.generation != current.generation {
            return Attempt::Stale;
        }
        // Fresh admission, state installation and observation share this lock.
        let mut next = current.image.clone();
        let reply = next.step(if lost { 6 } else { 0 }, &self.review);
        if reply == 0 {
            return Attempt::Denied;
        }
        let Some(generation) = current.generation.checked_add(1) else {
            return Attempt::Exhausted;
        };
        current.image = next;
        current.generation = generation;
        observe(&current.image);
        Attempt::Committed(reply)
    }
    fn control(&self, command: u64) -> Result<(), Attempt> {
        assert!((1..=5).contains(&command));
        let mut current = self.current.lock().unwrap();
        let Some(generation) = current.generation.checked_add(1) else {
            return Err(Attempt::Exhausted);
        };
        current.image.step(command, &self.review);
        current.generation = generation;
        Ok(())
    }
}
fn fixture_review(no_gain: bool, approved: bool) -> Review {
    Review {
        base: "base".into(),
        candidate: "candidate".into(),
        no_gain,
        approved,
    }
}

#[test]
fn simultaneous_preparations_have_one_actual_commit_boundary() {
    for (no_gain, approved) in [(true, false), (false, true), (false, false)] {
        let authority = Arc::new(Authority::new(fixture_review(no_gain, approved)));
        let barrier = Arc::new(Barrier::new(2));
        let effects = Arc::new(AtomicUsize::new(0));
        let workers: Vec<_> = (0..2)
            .map(|actor| {
                let (authority, barrier, effects) = (
                    Arc::clone(&authority),
                    Arc::clone(&barrier),
                    Arc::clone(&effects),
                );
                std::thread::spawn(move || {
                    let ticket = authority.capture();
                    barrier.wait();
                    authority.publish(Some(&ticket), actor == 0, |committed| {
                        assert!(
                            authority.current.try_lock().is_err(),
                            "observer escaped the authority transaction"
                        );
                        assert_eq!(committed.epoch, 8);
                        effects.fetch_add(1, Ordering::SeqCst);
                    })
                })
            })
            .collect();
        let replies: Vec<_> = workers
            .into_iter()
            .map(|worker| worker.join().unwrap())
            .collect();
        let eligible = no_gain || approved;
        assert_eq!(effects.load(Ordering::SeqCst), usize::from(eligible));
        assert_eq!(
            replies
                .iter()
                .filter(|reply| matches!(reply, Attempt::Committed(_)))
                .count(),
            usize::from(eligible)
        );
        if eligible {
            assert_eq!(
                replies
                    .iter()
                    .filter(|reply| **reply == Attempt::Stale)
                    .count(),
                1
            );
        } else {
            assert!(replies.iter().all(|reply| *reply == Attempt::Denied));
        }
        let current = authority.current.lock().unwrap();
        assert_eq!(
            current.image.unknown,
            replies.contains(&Attempt::Committed(2))
        );
    }
}
#[test]
fn restored_attributes_do_not_revive_a_prepared_cut() {
    let authority = Authority::new(fixture_review(true, false));
    let ticket = authority.capture();
    let original = authority.current.lock().unwrap().image.clone();
    authority.control(1).unwrap();
    authority.control(5).unwrap();
    assert_eq!(authority.current.lock().unwrap().image, original);
    assert_eq!(
        authority.publish(Some(&ticket), false, |_| panic!("stale observer")),
        Attempt::Stale
    );
    let fresh = authority.capture();
    assert_eq!(
        authority.publish(Some(&fresh), false, |_| {}),
        Attempt::Committed(1)
    );
}
#[test]
fn lost_reply_recovery_and_live_rollback_keep_the_original_commit() {
    let authority = Authority::new(fixture_review(false, true));
    let ticket = authority.capture();
    assert_eq!(
        authority.publish(Some(&ticket), true, |image| assert!(image.unknown)),
        Attempt::Committed(2)
    );
    for command in [3, 4, 3] {
        authority.control(command).unwrap();
    }
    assert_eq!(
        authority.publish(Some(&ticket), false, |_| panic!("duplicate observer")),
        Attempt::Stale
    );
    let fresh = authority.capture();
    assert_eq!(
        authority.publish(Some(&fresh), false, |_| panic!("renewed observer")),
        Attempt::Denied
    );
    let current = authority.current.lock().unwrap();
    assert_eq!(current.image.epoch, 8);
    assert_eq!(current.image.floor, 8);
    assert!(current.image.unknown);
}
#[test]
fn generation_exhaustion_refuses_before_installation_or_observation() {
    let authority = Authority::new(fixture_review(true, false));
    authority.current.lock().unwrap().generation = u64::MAX;
    let ticket = authority.capture();
    let original = authority.current.lock().unwrap().image.clone();
    assert_eq!(
        authority.publish(Some(&ticket), false, |_| panic!("overflow observer")),
        Attempt::Exhausted
    );
    assert_eq!(authority.control(1), Err(Attempt::Exhausted));
    let current = authority.current.lock().unwrap();
    assert_eq!(current.generation, u64::MAX);
    assert_eq!(current.image, original);
}
#[test]
fn independent_prechecks_without_atomic_install_can_duplicate() {
    let review = fixture_review(true, false);
    let original = Image::initial(&review.base);
    let mut first = original.clone();
    let mut second = original;
    // Expected counterexample, not an admitted authority implementation.
    assert_eq!(first.step(0, &review) + second.step(0, &review), 2);
}

#[test]
#[ignore = "requires solver-produced Lean fixtures; run just check-gateway-delta"]
fn simulated_publication_histories_match_lean() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.lake/build");
    let manifest: Manifest = serde_json::from_str(
        &std::fs::read_to_string(root.join("gateway-current-review-manifest.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(replay_manifest(&manifest).unwrap().len(), 10);
    let input: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("gateway-publication-traces.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(input["format_version"], 1);
    let runs = input["runs"].as_array().unwrap();
    assert_eq!(runs.len(), 4);
    let mut steps = 0;
    for run in runs {
        let review = Review::from_json(run);
        let traces = run["traces"].as_array().unwrap();
        assert_eq!(traces.len(), 343);
        for (seed, trace) in traces.iter().enumerate() {
            assert_eq!(trace["seed"], seed);
            let commands = trace["commands"].as_array().unwrap();
            let observations = trace["observations"].as_array().unwrap();
            assert_eq!(commands.len(), 3);
            assert_eq!(observations.len(), 3);
            let mut image = Image::initial(&review.base);
            let mut commits = 0;
            for (index, (command, expected)) in commands.iter().zip(observations).enumerate() {
                let command = command.as_u64().unwrap();
                assert_eq!(command as usize, seed / 7usize.pow(index as u32) % 7);
                let reply = image.step(command, &review);
                commits += usize::from(reply != 0);
                assert!(commits <= 1);
                assert_eq!(expected["reply"], reply, "reply: {seed}/{index}");
                assert_eq!(
                    expected["state"],
                    serde_json::to_value(&image).unwrap(),
                    "state: {seed}/{index}"
                );
                steps += 1;
            }
        }
    }
    assert_eq!(steps, 4116);
}

#[test]
#[ignore = "requires solver-produced Lean fixtures; run just check-gateway-delta"]
fn prepared_publication_interleavings_match_lean() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../.lake/build/gateway-publication-cas.json");
    let input: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    assert_eq!(input["format_version"], 1);
    let runs = input["runs"].as_array().unwrap();
    assert_eq!(runs.len(), 4);
    let mut total_steps = 0;
    let mut total_histories = 0;
    for run in runs {
        let traces = run["traces"].as_array().unwrap();
        assert_eq!(traces.len(), 632);
        for trace in traces {
            let authority = Authority::new(Review::from_json(run));
            let mut first: Option<Ticket> = None;
            let mut second: Option<Ticket> = None;
            let effects = AtomicUsize::new(0);
            let faults = trace["faults"].as_u64().unwrap();
            assert!(faults < 4);
            let commands = trace["commands"].as_array().unwrap();
            let observations = trace["observations"].as_array().unwrap();
            assert_eq!(commands.len(), observations.len());
            assert!((4..=5).contains(&commands.len()));
            for (index, (command, expected)) in commands.iter().zip(observations).enumerate() {
                let command = command.as_u64().unwrap();
                let (before_generation, before_image) = {
                    let before = authority.current.lock().unwrap();
                    (before.generation, before.image.clone())
                };
                let before_effects = effects.load(Ordering::SeqCst);
                let attempted_generation = match command {
                    2 => first.as_ref().map(|ticket| ticket.generation),
                    3 => second.as_ref().map(|ticket| ticket.generation),
                    _ => None,
                };
                let reply = match command {
                    0 => {
                        first = Some(authority.capture());
                        0
                    }
                    1 => {
                        second = Some(authority.capture());
                        0
                    }
                    2 | 3 => {
                        let (ticket, lost) = if command == 2 {
                            (first.as_ref(), faults % 2 == 1)
                        } else {
                            (second.as_ref(), faults / 2 % 2 == 1)
                        };
                        authority
                            .publish(ticket, lost, |_| {
                                assert!(matches!(
                                    authority.current.try_lock(),
                                    Err(std::sync::TryLockError::WouldBlock)
                                ));
                                effects.fetch_add(1, Ordering::SeqCst);
                            })
                            .code()
                    }
                    4..=8 => {
                        let control = match command {
                            4 => 3,
                            5 => 4,
                            6 => 1,
                            7 => 5,
                            _ => 2,
                        };
                        authority.control(control).unwrap();
                        0
                    }
                    _ => panic!("undeclared prepared-publication command"),
                };
                let current = authority.current.lock().unwrap();
                // Check the history laws against the actual shared authority,
                // separately from agreement with the serialized Lean fixture.
                assert!(before_generation <= current.generation);
                assert!(before_image.floor <= current.image.floor);
                assert!(!before_image.unknown || current.image.unknown);
                if attempted_generation.is_some_and(|cut| cut < before_generation) {
                    assert_eq!(reply, Attempt::Stale.code());
                    assert_eq!(current.generation, before_generation);
                    assert_eq!(current.image, before_image);
                    assert_eq!(effects.load(Ordering::SeqCst), before_effects);
                }
                let observed = serde_json::json!({"generation":current.generation, "image":current.image,
                    "first":first.as_ref().map(|ticket| ticket.generation),
                    "second":second.as_ref().map(|ticket| ticket.generation)});
                assert_eq!(expected["reply"], reply, "reply {commands:?}/{index}");
                assert_eq!(expected["state"], observed, "state {commands:?}/{index}");
                assert_eq!(
                    expected["commits"],
                    effects.load(Ordering::SeqCst),
                    "actual observer {commands:?}/{index}"
                );
                assert!(effects.load(Ordering::SeqCst) <= 1);
                total_steps += 1;
            }
            total_histories += 1;
        }
    }
    assert_eq!(total_histories, 2528);
    assert_eq!(total_steps, 12528);
}

#[test]
fn posture_writer_is_excluded_until_the_actual_commit_observer_returns() {
    let authority = Arc::new(Authority::new(fixture_review(true, false)));
    let ticket = authority.capture();
    let (entered_tx, entered_rx) = std::sync::mpsc::channel();
    let (probed_tx, probed_rx) = std::sync::mpsc::channel();
    let writer_authority = Arc::clone(&authority);
    let writer = std::thread::spawn(move || {
        entered_rx.recv().unwrap();
        assert!(matches!(
            writer_authority.current.try_lock(),
            Err(std::sync::TryLockError::WouldBlock)
        ));
        probed_tx.send(()).unwrap();
        writer_authority.control(1).unwrap();
    });
    assert_eq!(
        authority.publish(Some(&ticket), false, |image| {
            assert_eq!(image.epoch, 8);
            assert_eq!(image.mode, "enforcing");
            entered_tx.send(()).unwrap();
            probed_rx.recv().unwrap();
        }),
        Attempt::Committed(1)
    );
    writer.join().unwrap();
    let current = authority.current.lock().unwrap();
    assert_eq!(current.generation, 2);
    assert_eq!(current.image.epoch, 8);
    assert_eq!(current.image.mode, "observing");
}

#[test]
fn rolling_back_the_authority_record_remains_an_explicit_counterexample() {
    let authority = Authority::new(fixture_review(true, false));
    let original = authority.current.lock().unwrap().image.clone();
    let ticket = authority.capture();
    let effects = AtomicUsize::new(0);
    assert_eq!(
        authority.publish(Some(&ticket), false, |_| {
            effects.fetch_add(1, Ordering::SeqCst);
        }),
        Attempt::Committed(1)
    );
    // Fault injection violates the authority's non-rollback premise. A mutex
    // cannot authenticate a restored generation or recover erased consumption.
    *authority.current.lock().unwrap() = Current {
        generation: ticket.generation,
        image: original,
    };
    assert_eq!(
        authority.publish(Some(&ticket), false, |_| {
            effects.fetch_add(1, Ordering::SeqCst);
        }),
        Attempt::Committed(1)
    );
    assert_eq!(effects.load(Ordering::SeqCst), 2);
}

#[test]
fn equal_generations_from_another_authority_are_not_a_ticket() {
    let first = Authority::new(fixture_review(true, false));
    let other = Authority::new(fixture_review(true, false));
    let ticket = first.capture();
    assert_eq!(ticket.generation, other.capture().generation);
    assert_eq!(
        other.publish(Some(&ticket), false, |_| panic!("foreign observer")),
        Attempt::Foreign
    );
    assert_eq!(other.current.lock().unwrap().generation, 0);
    assert_eq!(
        other.publish(Some(&other.capture()), false, |_| {}),
        Attempt::Committed(1)
    );
}
