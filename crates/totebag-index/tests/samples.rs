//! A few of `totes/index/proof/samples.taut` again through the compiled core:
//! the Rust the core becomes answers as the checked definitions compute.

use std::rc::Rc;

use tauto_rt::Nat;
use totebag_index::core::generated::List;
use totebag_index::core::generated::api::*;

fn n(x: u64) -> Nat {
    Nat::from_u64(x)
}

fn list<A>(items: Vec<A>) -> List<A> {
    items
        .into_iter()
        .rev()
        .fold(List::Nil, |rest, a| List::Cons(a, Rc::new(rest).into()))
}

fn point(revision: u64, digest: u64) -> IxPoint {
    IxPoint {
        revision: n(revision),
        digest: n(digest),
    }
}

fn key() -> IxKey {
    IxKey {
        project: n(1),
        revision: n(1),
    }
}

fn root(index: u64, revision: u64) -> IxState {
    IxState {
        index: n(index),
        config: n(10),
        sequence: n(0),
        issued: n(0),
        until: n(4),
        head: point(revision, index),
        checkpoints: list(vec![IxCheckpoint {
            point: point(revision, index),
            sequence: n(0),
        }]),
        observations: List::Nil.into(),
        receipts: List::Nil.into(),
        votes: List::Nil,
        withdrawals: List::Nil,
        retired: false,
    }
}

fn step(state: IxState, batch: IxBatch) -> IxState {
    ix_step(state, batch).expect("a valid batch")
}

struct Sample {
    alice: IxState,
    bob: IxState,
}

fn sample() -> Sample {
    let alice = step(
        root(1, 0),
        IxBatch {
            sequence: n(1),
            issued: n(1),
            until: n(4),
            config: n(10),
            parent: point(0, 1),
            point: point(1, 11),
            events: list(vec![
                IxEvent::IxObserve(key(), n(7), n(1)),
                IxEvent::IxDecide(key(), true),
            ])
            .into(),
        },
    );
    let alice = step(
        alice,
        IxBatch {
            sequence: n(2),
            issued: n(4),
            until: n(20),
            config: n(10),
            parent: point(1, 11),
            point: point(2, 12),
            events: List::Nil.into(),
        },
    );
    let bob = step(
        root(2, 10),
        IxBatch {
            sequence: n(1),
            issued: n(4),
            until: n(20),
            config: n(10),
            parent: point(10, 2),
            point: point(11, 21),
            events: list(vec![IxEvent::MkIxWitness(
                IxReceipt {
                    index: n(1),
                    source: n(101),
                    point: point(2, 12),
                    first: n(4),
                }
                .into(),
            )])
            .into(),
        },
    );
    Sample { alice, bob }
}

fn eligible(s: &Sample, now: u64, checked: u64) -> bool {
    let alice = IxTrust {
        index: n(1),
        source: n(101),
        pin: point(0, 1),
    };
    let bob = IxTrust {
        index: n(2),
        source: n(102),
        pin: point(10, 2),
    };
    ix_evaluate_ledgers(
        n(0),
        list(vec![alice]),
        list(vec![IxWitness::IxRemote(bob)]),
        IxLimits {
            age: n(5),
            lifetime: n(20),
            source_age: n(3),
        },
        list(vec![
            IxLedger::IxOpen(s.alice.clone().into()),
            IxLedger::IxOpen(s.bob.clone().into()),
        ]),
        list(vec![
            IxOrigin {
                index: n(1),
                source: n(101),
                head: point(2, 12),
                checked: n(checked),
            },
            IxOrigin {
                index: n(2),
                source: n(102),
                head: point(11, 21),
                checked: n(checked),
            },
        ]),
        List::Nil,
        n(now),
        key(),
        n(7),
    )
}

#[test]
fn the_compiled_core_answers_as_the_samples_compute() {
    let s = sample();
    assert_eq!(s.alice.sequence, n(2), "both batches applied");
    assert_eq!(s.bob.sequence, n(1));
    // sample_age_boundary_accept, sample_one_second_early, sample_expiry_boundary
    assert!(eligible(&s, 9, 9));
    assert!(!eligible(&s, 8, 8));
    assert!(!eligible(&s, 20, 20));
    // sample_stale_origin_check_rejected, sample_origin_check_boundary_accepted,
    // sample_future_origin_check_rejected
    assert!(!eligible(&s, 9, 5));
    assert!(eligible(&s, 9, 6));
    assert!(!eligible(&s, 9, 10));
}
