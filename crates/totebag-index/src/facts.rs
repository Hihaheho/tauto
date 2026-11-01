//! What the readers found, as the core's inputs. The core compares
//! identities only for equality, so each one becomes a small number: the
//! same number for the same identity throughout one evaluation, a different
//! number for a different one. An identity of one kind never shares a number
//! with an identity of another kind, even when their bytes are the same.

use std::collections::HashMap;
use std::rc::Rc;

use totebag::index::checkpoint::{Checkpoint, History};
use totebag::index::ledger::{Event, Key, Sha256};
use totebag::spec::Rev;

use crate::core::generated::List;
use crate::core::generated::api::{
    IxBatch, IxEvent, IxKey, IxPoint, IxReceipt, IxState, ix_rebuild, ix_step,
};
use tauto_rt::Nat;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Atom {
    /// A checkpoint's digest; an index is named by its root's.
    Checkpoint(Sha256),
    /// The SHA-256 of a source tree.
    Content(Sha256),
    Project(Sha256),
    /// A package revision, as an index writes it.
    Revision(String),
    /// A Git commit of an index, in its spelled form.
    Commit(String),
    /// Where an index is read from: its URL and branch.
    Origin(String, String),
    /// The SHA-256 of an index's `Index.eure`.
    Config(Sha256),
}

/// The numbers given out in one evaluation.
#[derive(Debug, Default)]
pub struct Atoms {
    numbers: HashMap<Atom, u64>,
}

impl Atoms {
    pub fn of(&mut self, atom: Atom) -> Nat {
        let next = self.numbers.len() as u64 + 1;
        nat(*self.numbers.entry(atom).or_insert(next))
    }

    pub fn key(&mut self, key: &Key) -> IxKey {
        IxKey {
            project: self.of(Atom::Project(key.project)),
            revision: self.of(Atom::Revision(key.rev.clone())),
        }
    }

    pub fn point(&mut self, rev: &Rev, digest: &Sha256) -> IxPoint {
        IxPoint {
            revision: self.of(Atom::Commit(rev.to_string())),
            digest: self.of(Atom::Checkpoint(*digest)),
        }
    }

    pub fn origin(&mut self, url: &str, reference: &str) -> Nat {
        self.of(Atom::Origin(url.to_string(), reference.to_string()))
    }

    pub fn event(&mut self, event: &Event) -> IxEvent {
        match event {
            Event::Observation {
                key,
                source,
                first_seen_at,
            } => IxEvent::IxObserve(
                self.key(key),
                self.of(Atom::Content(*source)),
                nat(*first_seen_at),
            ),
            Event::IndexObservation {
                index,
                repository,
                reference,
                rev,
                sha256,
                first_seen_at,
            } => IxEvent::MkIxWitness(
                IxReceipt {
                    index: self.of(Atom::Checkpoint(*index)),
                    source: self.origin(repository, reference),
                    point: self.point(rev, sha256),
                    first: nat(*first_seen_at),
                }
                .into(),
            ),
            Event::Decision { key, accept, .. } => IxEvent::IxDecide(self.key(key), *accept),
            Event::Withdrawal { key, .. } => IxEvent::IxWithdraw(self.key(key)),
            Event::Retirement { .. } => IxEvent::IxRetire,
        }
    }
}

/// A number of the facts as the core's `nat`.
pub fn nat(n: u64) -> Nat {
    Nat::from_u64(n)
}

/// A `nat` of the core that is a time or a count of the facts.
pub fn small(n: &Nat) -> u64 {
    n.to_u64().unwrap_or(u64::MAX)
}

pub fn list<A>(items: impl IntoIterator<Item = A>) -> List<A> {
    let items: Vec<A> = items.into_iter().collect();
    items
        .into_iter()
        .rev()
        .fold(List::Nil, |rest, a| List::Cons(a, Rc::new(rest).into()))
}

/// The ledger the first `len` checkpoints of `history` hold, every batch
/// applied in order by the core. A batch the core refuses refuses the whole.
pub fn rebuild(history: &History, len: usize, atoms: &mut Atoms) -> Result<IxState, String> {
    let config = atoms.of(Atom::Config(history.config_id()));
    let root = &history.checkpoints[0];
    let mut state = ix_rebuild(
        config.clone(),
        atoms.point(&root.rev, &root.digest),
        nat(root.batch.issued_at),
        nat(root.batch.valid_until),
        List::Nil,
    )
    .ok_or_else(|| say!("totebag-root-invalid", rev = root.rev.short()))?;
    // One step at a time rather than the whole list at once: the same
    // result (`ix_rebuild` is the root and then each `ix_step`), with a
    // history's length kept off the stack.
    for c in &history.checkpoints[1..len] {
        let batch = batch(atoms, config.clone(), &state, c);
        let why = refusal(&state, c);
        state = ix_step(state, batch).ok_or(why)?;
    }
    Ok(state)
}

/// The batch `c` adds after the head of `state`.
pub fn batch(atoms: &mut Atoms, config: Nat, state: &IxState, c: &Checkpoint) -> IxBatch {
    IxBatch {
        sequence: nat(c.batch.sequence),
        issued: nat(c.batch.issued_at),
        until: nat(c.batch.valid_until),
        config,
        parent: state.head.clone(),
        point: atoms.point(&c.rev, &c.digest),
        events: list(c.batch.events.iter().map(|e| atoms.event(e))).into(),
    }
}

/// Why the core would refuse `c` after `state`, in words; the core itself
/// answers only yes or no.
pub fn refusal(state: &IxState, c: &Checkpoint) -> String {
    let why = if state.retired {
        "the index had retired".to_string()
    } else if c.batch.sequence != small(&state.sequence).saturating_add(1) {
        format!(
            "it is numbered {} after {}",
            c.batch.sequence, state.sequence
        )
    } else if c.batch.issued_at < small(&state.issued) {
        "it was issued before the batch it follows".to_string()
    } else {
        "an event in it is not allowed there (a revision observed twice, a decision on one \
         not observed, …)"
            .to_string()
    };
    format!("the batch at {} is refused: {why}", c.rev.short())
}
