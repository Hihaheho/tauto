//! Syncing an index into the protected state and asking whether a revision
//! may be adopted: what moves the ledger, what freezes it, and what changes
//! nothing.

use std::path::Path;

use totebag::git::Mirror;
use totebag::index::checkpoint;
use totebag::index::ledger::Sha256;
use totebag::index::policy::{Limits, Rule, Trusted, Witness};
use totebag::index::state::{Point, Store};
use totebag::index::strict::{hex_bytes, time};
use totebag_index::engine::{self, Synced};
use totebag_index::explain::explain;

mod common;
use common::*;

/// The index's ID and its root, as a policy would name them.
fn root_of(s: &Scratch, repo: &Path) -> (Sha256, Point) {
    let mirror = Mirror::open(s.0.join("probe"), "sha1").unwrap();
    let head = mirror.fetch_history(&url(repo), "refs/heads/main").unwrap();
    let h = checkpoint::history(&mirror, &head).unwrap();
    let root = &h.checkpoints[0];
    (
        h.id(),
        Point {
            rev: root.rev.clone(),
            digest: root.digest,
        },
    )
}

fn trusted(s: &Scratch, repo: &Path) -> Trusted {
    let (index, pin) = root_of(s, repo);
    Trusted {
        alias: "alice".into(),
        url: url(repo),
        reference: "refs/heads/main".into(),
        index,
        pin,
    }
}

fn policy(alice: &Trusted) -> Rule {
    Rule {
        observers: vec![alice.clone()],
        witnesses: vec![Witness::Local],
        limits: Limits {
            min_age: 3600,
            max_checkpoint_lifetime: 7 * 86_400,
            max_source_check_age: 600,
        },
    }
}

fn accepted(repo: &Path) {
    init(repo);
    commit(
        repo,
        &batch(
            1,
            "2026-10-01T11:00:00Z",
            "2026-10-03T11:00:00Z",
            &[observation("2026-10-01T11:00:00Z"), decision("accept")],
        ),
    );
}

fn t(s: &str) -> u64 {
    time(s).unwrap()
}

fn source() -> Sha256 {
    hex_bytes(&SOURCE["sha256:".len()..])
}

#[test]
fn a_synced_index_lets_a_revision_in_once_it_has_waited() {
    tauto_messages::install();
    let s = Scratch::new("engine-admit");
    let repo = s.0.join("alice");
    accepted(&repo);
    let alice = trusted(&s, &repo);
    let policy = policy(&alice);
    let store = Store::at(s.0.join("state"));
    let mut held = store.hold().unwrap();

    let synced = engine::sync(&store, &mut held, &alice, t("2026-10-01T11:00:30Z")).unwrap();
    let Synced::Open { head, taken: 1 } = synced else {
        panic!("{synced:?}")
    };
    let ledger = held.state.ledger(&alice.index).unwrap().clone();
    assert_eq!(ledger.prefix, head);
    assert_eq!(ledger.pin, head, "the origin answered with it just now");
    assert_eq!(held.state.receipts.len(), 1);

    // An hour later the check of the origin is too old.
    let ask = |held: &mut _, now: &str| {
        engine::evaluate(&store, held, &policy, t(now), &key(), &source())
    };
    assert_eq!(ask(&mut held, "2026-10-01T11:30:00Z"), Ok(false));
    let why = |held: &totebag::index::state::Held, now: &str| {
        explain(&store, &held.state, &policy, t(now), &key(), &source()).join("\n")
    };
    let w = why(&held, "2026-10-01T11:30:00Z");
    assert!(
        w.contains(
            "alice: observed it at 2026-10-01T11:00:00Z; it waits until 2026-10-01T12:00:00Z"
        ),
        "{w}"
    );
    assert!(
        w.contains("this machine: has had alice's record of it at 2026-10-01T11:00:30Z"),
        "{w}"
    );
    assert_eq!(ask(&mut held, "2026-10-01T12:00:30Z"), Ok(false));
    let w = why(&held, "2026-10-01T12:00:30Z");
    assert!(
        w.contains("alice: its origin was checked 1h 0m ago, more than the 10m allowed"),
        "{w}"
    );
    // Synced again: nothing new, the first sight stays, the check is fresh.
    let synced = engine::sync(&store, &mut held, &alice, t("2026-10-01T12:00:00Z")).unwrap();
    assert!(
        matches!(synced, Synced::Open { taken: 0, .. }),
        "{synced:?}"
    );
    assert_eq!(
        held.state.receipts[0].first_seen_at,
        t("2026-10-01T11:00:30Z")
    );
    assert_eq!(ask(&mut held, "2026-10-01T12:00:30Z"), Ok(true));
    assert_eq!(why(&held, "2026-10-01T12:00:30Z"), "");
    assert_eq!(held.state.evaluated_at, t("2026-10-01T12:00:30Z"));
    // Another tree for the same revision is not what was observed.
    assert_eq!(
        engine::evaluate(
            &store,
            &mut held,
            &policy,
            t("2026-10-01T12:00:31Z"),
            &key(),
            &[7; 32]
        ),
        Ok(false)
    );
    // The clock went back.
    let err = ask(&mut held, "2026-10-01T12:00:00Z").unwrap_err();
    assert!(err.contains("before the last evaluation"), "{err}");

    held.save().unwrap();
    let saved = held.state.clone();
    drop(held);
    assert_eq!(store.hold().unwrap().state, saved);
}

#[test]
fn a_refused_batch_freezes_the_ledger_before_it() {
    tauto_messages::install();
    let s = Scratch::new("engine-refused");
    let repo = s.0.join("alice");
    accepted(&repo);
    let alice = trusted(&s, &repo);
    let store = Store::at(s.0.join("state"));
    let mut held = store.hold().unwrap();
    let now = t("2026-10-01T11:00:30Z");
    let Synced::Open { head, .. } = engine::sync(&store, &mut held, &alice, now).unwrap() else {
        panic!()
    };
    commit(
        &repo,
        &batch(5, "2026-10-01T12:00:00Z", "2026-10-03T12:00:00Z", &[]),
    );
    let synced = engine::sync(&store, &mut held, &alice, now + 3600).unwrap();
    let Synced::Frozen { prefix, why } = synced else {
        panic!("{synced:?}")
    };
    assert_eq!(prefix, head);
    assert!(why.contains("numbered 5 after 1"), "{why}");
    // It stays frozen, and adopts nothing.
    commit(
        &repo,
        &batch(6, "2026-10-01T12:00:00Z", "2026-10-03T12:00:00Z", &[]),
    );
    let synced = engine::sync(&store, &mut held, &alice, now + 3601).unwrap();
    assert!(matches!(synced, Synced::Frozen { .. }), "{synced:?}");
    assert_eq!(
        engine::evaluate(
            &store,
            &mut held,
            &policy(&alice),
            now + 3601,
            &key(),
            &source()
        ),
        Ok(false)
    );
    let w = explain(
        &store,
        &held.state,
        &policy(&alice),
        now + 3601,
        &key(),
        &source(),
    );
    assert!(w[0].starts_with("alice: stopped at"), "{w:?}");
}

#[test]
fn a_rewritten_history_freezes_the_ledger() {
    tauto_messages::install();
    let s = Scratch::new("engine-rewritten");
    let repo = s.0.join("alice");
    accepted(&repo);
    let alice = trusted(&s, &repo);
    let store = Store::at(s.0.join("state"));
    let mut held = store.hold().unwrap();
    let now = t("2026-10-01T11:00:30Z");
    engine::sync(&store, &mut held, &alice, now).unwrap();
    git(&repo, &["reset", "--quiet", "--hard", "HEAD~1"]);
    commit(
        &repo,
        &batch(
            1,
            "2026-10-01T11:00:00Z",
            "2026-10-03T11:00:00Z",
            &[observation("2026-10-01T10:00:00Z"), decision("accept")],
        ),
    );
    let synced = engine::sync(&store, &mut held, &alice, now + 60).unwrap();
    let Synced::Frozen { why, .. } = synced else {
        panic!("{synced:?}")
    };
    assert!(why.contains("no longer holds"), "{why}");
}

#[test]
fn what_cannot_be_read_changes_nothing() {
    tauto_messages::install();
    let s = Scratch::new("engine-unread");
    let repo = s.0.join("alice");
    accepted(&repo);
    let alice = trusted(&s, &repo);
    let store = Store::at(s.0.join("state"));
    let mut held = store.hold().unwrap();
    let now = t("2026-10-01T11:00:30Z");
    engine::sync(&store, &mut held, &alice, now).unwrap();
    let before = held.state.clone();
    commit(
        &repo,
        &batch(2, "2026-10-01T12:00:00Z", "2026-10-03T12:00:00Z", &[])
            .replace("format = 1", "format = 2"),
    );
    let err = engine::sync(&store, &mut held, &alice, now + 60).unwrap_err();
    assert!(err.contains("nothing from it is used"), "{err}");
    assert_eq!(held.state, before);

    let other = Trusted {
        index: [9; 32],
        ..alice.clone()
    };
    let err = engine::sync(&store, &mut held, &other, now + 60).unwrap_err();
    assert!(err.contains("format 2"), "{err}");
}

#[test]
fn another_index_at_the_url_is_refused() {
    tauto_messages::install();
    let s = Scratch::new("engine-other");
    let repo = s.0.join("alice");
    accepted(&repo);
    let alice = trusted(&s, &repo);
    let other = Trusted {
        index: [9; 32],
        ..alice
    };
    let store = Store::at(s.0.join("state"));
    let mut held = store.hold().unwrap();
    let err = engine::sync(&store, &mut held, &other, t("2026-10-01T11:00:30Z")).unwrap_err();
    assert!(err.contains("not the sha256:0909"), "{err}");
    assert!(held.state.ledgers.is_empty());
}
