//! An index read from Git and given to the core: the ledger it holds, and
//! whether a package revision it vouches for may be adopted.

use std::path::Path;

use totebag::git::Mirror;
use totebag::index::checkpoint::{self, History};
use totebag::index::strict::{hex_bytes, time};
use totebag_index::core::generated::api::*;
use totebag_index::facts::{Atom, Atoms, list, nat, rebuild};

mod common;
use common::*;

fn read(s: &Scratch, repo: &Path) -> History {
    let mirror = Mirror::open(s.0.join(format!("m{}", rand())), "sha1").unwrap();
    let head = mirror.fetch_history(&url(repo), "refs/heads/main").unwrap();
    checkpoint::history(&mirror, &head).unwrap()
}

fn rand() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos()
}

/// Whether `history`'s index alone, read from `repo` and checked at
/// `checked`, makes the package revision eligible at `now`, with this
/// machine witnessing its head since `seen`.
fn eligible(history: &History, repo: &Path, now: &str, checked: &str, seen: &str) -> bool {
    let mut atoms = Atoms::default();
    let state = rebuild(history, history.checkpoints.len(), &mut atoms).unwrap();
    let root = &history.checkpoints[0];
    let head = history.checkpoints.last().unwrap();
    let source = atoms.origin(&url(repo), "refs/heads/main");
    let trust = IxTrust {
        index: atoms.of(Atom::Checkpoint(history.id())),
        source: source.clone(),
        pin: atoms.point(&root.rev, &root.digest),
    };
    let origin = IxOrigin {
        index: trust.index.clone(),
        source: source.clone(),
        head: atoms.point(&head.rev, &head.digest),
        checked: nat(time(checked).unwrap()),
    };
    let receipt = IxReceipt {
        index: trust.index.clone(),
        source,
        point: origin.head.clone(),
        first: nat(time(seen).unwrap()),
    };
    let key = atoms.key(&key());
    let digest = atoms.of(Atom::Content(hex_bytes(&SOURCE["sha256:".len()..])));
    ix_evaluate_ledgers(
        nat(0),
        list([trust]),
        list([IxWitness::IxLocal]),
        IxLimits {
            age: nat(3600),
            lifetime: nat(7 * 86_400),
            source_age: nat(600),
        },
        list([IxLedger::IxOpen(state.into())]),
        list([origin]),
        list([receipt]),
        nat(time(now).unwrap()),
        key,
        digest,
    )
}

#[test]
fn a_history_becomes_the_ledger_it_holds() {
    tauto_messages::install();
    let s = Scratch::new("ledger");
    let repo = s.0.join("repo");
    init(&repo);
    commit(
        &repo,
        &batch(
            1,
            "2026-10-01T12:00:00Z",
            "2026-10-03T12:00:00Z",
            &[observation("2026-10-01T11:00:00Z"), decision("accept")],
        ),
    );
    let history = read(&s, &repo);
    let mut atoms = Atoms::default();
    let state = rebuild(&history, history.checkpoints.len(), &mut atoms).unwrap();
    assert_eq!(state.sequence, nat(1));
    assert_eq!(state.index, atoms.of(Atom::Checkpoint(history.id())));
    let head = history.checkpoints.last().unwrap();
    assert!(state.head == atoms.point(&head.rev, &head.digest));
    assert!(!state.retired);
    // The same identity is the same number; another kind of identity with
    // the same bytes is not.
    let project = atoms.key(&key()).project;
    assert_eq!(project, atoms.key(&key()).project);
    assert_ne!(project, atoms.of(Atom::Content(key().project)));
}

#[test]
fn the_core_refuses_what_the_reader_lets_through() {
    tauto_messages::install();
    let s = Scratch::new("refuse");
    // A decision on a revision no one observed is well formed, but not a
    // valid next batch.
    let repo = s.0.join("decide");
    init(&repo);
    commit(
        &repo,
        &batch(
            1,
            "2026-10-01T12:00:00Z",
            "2026-10-03T12:00:00Z",
            &[decision("accept")],
        ),
    );
    let history = read(&s, &repo);
    let err = rebuild(&history, history.checkpoints.len(), &mut Atoms::default())
        .err()
        .unwrap();
    assert!(err.contains("an event in it is not allowed"), "{err}");

    let repo = s.0.join("skip");
    init(&repo);
    commit(
        &repo,
        &batch(2, "2026-10-01T12:00:00Z", "2026-10-03T12:00:00Z", &[]),
    );
    let history = read(&s, &repo);
    let err = rebuild(&history, history.checkpoints.len(), &mut Atoms::default())
        .err()
        .unwrap();
    assert!(err.contains("numbered 2 after 0"), "{err}");

    let repo = s.0.join("backwards");
    init(&repo);
    commit(
        &repo,
        &batch(1, "2026-09-30T12:00:00Z", "2026-10-03T12:00:00Z", &[]),
    );
    let history = read(&s, &repo);
    let err = rebuild(&history, history.checkpoints.len(), &mut Atoms::default())
        .err()
        .unwrap();
    assert!(err.contains("issued before"), "{err}");
}

#[test]
fn an_accepted_revision_waits_its_age_and_needs_a_fresh_check() {
    tauto_messages::install();
    let s = Scratch::new("admit");
    let accepted = |name: &str, verdict: &str| {
        let repo = s.0.join(name);
        init(&repo);
        commit(
            &repo,
            &batch(
                1,
                "2026-10-01T11:00:00Z",
                "2026-10-03T11:00:00Z",
                &[observation("2026-10-01T11:00:00Z"), decision(verdict)],
            ),
        );
        let history = read(&s, &repo);
        (repo, history)
    };
    let (repo, history) = accepted("accept", "accept");
    let at = |now: &str, checked: &str, seen: &str| eligible(&history, &repo, now, checked, seen);
    // An hour after it was first seen, here and by the index; checked a
    // minute ago.
    let (now, checked, seen) = (
        "2026-10-01T12:00:00Z",
        "2026-10-01T11:59:00Z",
        "2026-10-01T11:00:00Z",
    );
    assert!(at(now, checked, seen));
    // A second too early.
    assert!(!at("2026-10-01T11:59:59Z", checked, seen));
    // Seen here only half an hour ago.
    assert!(!at(now, checked, "2026-10-01T11:30:00Z"));
    // The check of the origin is eleven minutes old.
    assert!(!at("2026-10-01T12:10:00Z", "2026-10-01T11:59:00Z", seen));
    // The batch is no longer valid.
    assert!(!at("2026-10-03T11:00:00Z", "2026-10-03T10:59:00Z", seen));

    let (repo, history) = accepted("reject", "reject");
    assert!(!eligible(&history, &repo, now, checked, seen));
}
