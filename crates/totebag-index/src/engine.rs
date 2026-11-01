//! Taking in the indexes a policy trusts, and asking whether a package
//! revision may be adopted: the facts read from Git and kept in the
//! protected state, given to the core.
//!
//! Syncing an index fetches its branch, reads its whole history, and takes
//! in the batches after the prefix already taken in, through
//! `ix_ingest_grounded`: a batch the core refuses freezes the ledger at the
//! prefix before it, and a history that no longer holds that prefix freezes
//! it too. A history that cannot be read changes nothing: the ledger keeps
//! its prefix and the last check of its origin, which ages until it is too
//! old to adopt anything with. The check, the time the head was first seen
//! here and the pin are written only by this machine.

use totebag::git::Mirror;
use totebag::index::checkpoint::{self, Checkpoint, History};
use totebag::index::ledger::{Batch, Key, Sha256};
use totebag::index::policy::{Rule, Trusted, Witness};
use totebag::index::state::{Check, Held, Ledger, Point, State, Store};
use totebag::index::strict::hex_of;
use totebag::spec::Rev;

use crate::core::generated::api::{
    IxLedger, IxLimits, IxOrigin, IxReceipt, IxTrust, IxWitness, ix_advance_pin,
    ix_evaluate_ledgers, ix_ingest_grounded, ix_step,
};
use crate::facts::{self, Atom, Atoms, list, nat};

/// What a sync of one index did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Synced {
    /// The ledger now holds the history through `head`; `taken` batches were new.
    Open { head: Point, taken: usize },
    /// The ledger is frozen at `prefix`, now or before.
    Frozen { prefix: Point, why: String },
}

/// The current time, for syncing and evaluating.
pub fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

fn mirror(store: &Store, t: &Trusted) -> Result<Mirror, String> {
    Mirror::open(store.mirror_dir(&t.url), t.pin.rev.format())
}

fn position(history: &History, p: &Point) -> Option<usize> {
    history
        .checkpoints
        .iter()
        .position(|c| c.rev == p.rev && c.digest == p.digest)
}

fn point_of(history: &History, i: usize) -> Point {
    let c = &history.checkpoints[i];
    Point {
        rev: c.rev.clone(),
        digest: c.digest,
    }
}

fn trust(atoms: &mut Atoms, t: &Trusted, pin: &Point) -> IxTrust {
    IxTrust {
        index: atoms.of(Atom::Checkpoint(t.index)),
        source: atoms.origin(&t.url, &t.reference),
        pin: atoms.point(&pin.rev, &pin.digest),
    }
}

fn origin(atoms: &mut Atoms, l: &Ledger, check: &Check) -> IxOrigin {
    IxOrigin {
        index: atoms.of(Atom::Checkpoint(l.index)),
        source: atoms.origin(&l.url, &l.reference),
        head: atoms.point(&check.head.rev, &check.head.digest),
        checked: nat(check.at),
    }
}

/// Fetches the index `t` and takes in what is new, at `now`. The state is
/// changed in `held`; the caller saves it.
pub fn sync(store: &Store, held: &mut Held, t: &Trusted, now: u64) -> Result<Synced, String> {
    let mirror = mirror(store, t)?;
    let head = mirror.fetch_history(&t.url, &t.reference)?;
    let history = checkpoint::history(&mirror, &head).map_err(|e| {
        say!(
            "totebag-index-unused",
            alias = &t.alias,
            url = &t.url,
            error = e
        )
    })?;
    if history.id() != t.index {
        return Err(say!(
            "totebag-index-other-id",
            alias = &t.alias,
            url = &t.url,
            found = hex_of(&history.id()),
            trusted = hex_of(&t.index)
        ));
    }
    let head = point_of(&history, history.checkpoints.len() - 1);
    let state = &mut held.state;
    let i = match state.ledgers.iter().position(|l| l.index == t.index) {
        Some(i) => i,
        None => {
            if position(&history, &t.pin).is_none() {
                return Err(say!(
                    "totebag-pin-not-in-history",
                    alias = &t.alias,
                    head = head.rev.short(),
                    pin = t.pin.rev.short()
                ));
            }
            state.ledgers.push(Ledger {
                index: t.index,
                url: t.url.clone(),
                reference: t.reference.clone(),
                pin: t.pin.clone(),
                prefix: t.pin.clone(),
                frozen: None,
                checked: None,
            });
            state.ledgers.len() - 1
        }
    };
    let ledger = &mut state.ledgers[i];
    if (&ledger.url, &ledger.reference) != (&t.url, &t.reference) {
        return Err(say!(
            "totebag-index-read-elsewhere",
            alias = &t.alias,
            url = &ledger.url,
            reference = &ledger.reference,
            other_url = &t.url,
            other_reference = &t.reference
        ));
    }
    ledger.checked = Some(Check {
        head: head.clone(),
        at: now,
    });
    if let Some(why) = &ledger.frozen {
        return Ok(Synced::Frozen {
            prefix: ledger.prefix.clone(),
            why: why.clone(),
        });
    }
    let Some(k) = position(&history, &ledger.prefix) else {
        let why = format!(
            "the history at {} no longer holds {}, which was taken in",
            head.rev.short(),
            ledger.prefix.rev.short()
        );
        ledger.frozen = Some(why.clone());
        return Ok(Synced::Frozen {
            prefix: ledger.prefix.clone(),
            why,
        });
    };
    let mut atoms = Atoms::default();
    let config = atoms.of(Atom::Config(history.config_id()));
    let mut taken = IxLedger::IxOpen(facts::rebuild(&history, k + 1, &mut atoms)?.into());
    let mut frozen = None;
    for c in &history.checkpoints[k + 1..] {
        let IxLedger::IxOpen(open) = &taken else {
            unreachable!("a frozen ledger stops the loop")
        };
        let batch = facts::batch(&mut atoms, config.clone(), open, c);
        let why = facts::refusal(open, c);
        taken = ix_ingest_grounded(taken, batch);
        if matches!(taken, IxLedger::IxFrozen(_)) {
            frozen = Some(why);
            break;
        }
    }
    let (IxLedger::IxOpen(open) | IxLedger::IxFrozen(open)) = &taken;
    let prefix = point_of(
        &history,
        history
            .checkpoints
            .iter()
            .position(|c| atoms.point(&c.rev, &c.digest) == open.head)
            .expect("the head is a checkpoint of the history"),
    );
    let taken_count = position(&history, &prefix).unwrap() - k;
    mirror.keep("prefix", &prefix.rev)?;
    ledger.prefix = prefix.clone();
    if let Some(why) = frozen {
        ledger.frozen = Some(why.clone());
        return Ok(Synced::Frozen { prefix, why });
    }
    // The pin moves to the head when the origin answered with it just now.
    let check = ledger.checked.clone().expect("checked above");
    let advanced = ix_advance_pin(
        trust(&mut atoms, t, &ledger.pin),
        (**open).clone(),
        list([origin(&mut atoms, ledger, &check)]),
    );
    if advanced.is_some() {
        ledger.pin = prefix.clone();
    }
    let (index, url, reference) = (ledger.index, ledger.url.clone(), ledger.reference.clone());
    state.receive(index, &url, &reference, prefix.clone(), now);
    Ok(Synced::Open {
        head: prefix,
        taken: taken_count,
    })
}

/// The ledger of `l` as taken in, read again from its mirror.
pub(crate) fn ledger_of(store: &Store, l: &Ledger, atoms: &mut Atoms) -> Result<IxLedger, String> {
    let mirror = Mirror::open(store.mirror_dir(&l.url), l.prefix.rev.format())?;
    let history = checkpoint::history(&mirror, &l.prefix.rev)?;
    let state = facts::rebuild(&history, history.checkpoints.len(), atoms)?;
    Ok(match l.frozen {
        Some(_) => IxLedger::IxFrozen(state.into()),
        None => IxLedger::IxOpen(state.into()),
    })
}

/// Whether the package revision `key` with the source tree `source` may be
/// adopted at `now` under `rule`, from what the state holds. Every
/// evaluation moves the state's time forward, whatever it answers; one at
/// an earlier time than an evaluation before is refused.
pub fn evaluate(
    store: &Store,
    held: &mut Held,
    rule: &Rule,
    now: u64,
    key: &Key,
    source: &Sha256,
) -> Result<bool, String> {
    let state: &State = &held.state;
    if now < state.evaluated_at {
        return Err(say!(
            "totebag-clock-behind-adopting-nothing",
            now = totebag::index::strict::time_text(now),
            last = totebag::index::strict::time_text(state.evaluated_at)
        ));
    }
    let previous = state.evaluated_at;
    let mut atoms = Atoms::default();
    let mut ledgers = Vec::new();
    let mut origins = Vec::new();
    for t in rule.indexes() {
        let Some(l) = state.ledger(&t.index) else {
            continue;
        };
        ledgers.push(ledger_of(store, l, &mut atoms)?);
        if let Some(check) = &l.checked {
            origins.push(origin(&mut atoms, l, check));
        }
    }
    let current = |atoms: &mut Atoms, t: &Trusted| {
        let pin = state.ledger(&t.index).map_or(&t.pin, |l| &l.pin);
        trust(atoms, t, pin)
    };
    let observers: Vec<IxTrust> = rule
        .observers
        .iter()
        .map(|t| current(&mut atoms, t))
        .collect();
    let witnesses: Vec<IxWitness> = rule
        .witnesses
        .iter()
        .map(|w| match w {
            Witness::Local => IxWitness::IxLocal,
            Witness::Remote(t) => IxWitness::IxRemote(current(&mut atoms, t)),
        })
        .collect();
    let receipts: Vec<_> = state
        .receipts
        .iter()
        .map(|r| IxReceipt {
            index: atoms.of(Atom::Checkpoint(r.index)),
            source: atoms.origin(&r.url, &r.reference),
            point: atoms.point(&r.point.rev, &r.point.digest),
            first: nat(r.first_seen_at),
        })
        .collect();
    let limits = IxLimits {
        age: nat(rule.limits.min_age),
        lifetime: nat(rule.limits.max_checkpoint_lifetime),
        source_age: nat(rule.limits.max_source_check_age),
    };
    let key = atoms.key(key);
    let digest = atoms.of(Atom::Content(*source));
    let answer = ix_evaluate_ledgers(
        nat(previous),
        list(observers),
        list(witnesses),
        limits,
        list(ledgers),
        list(origins),
        list(receipts),
        nat(now),
        key,
        digest,
    );
    held.state.evaluated_at = now;
    Ok(answer)
}

/// Runs `f` on a thread with a stack deep enough for a long history: the
/// core walks its lists by recursion.
pub fn on_deep_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn_scoped(s, f)
            .expect("a thread")
            .join()
            .unwrap_or_else(|e| std::panic::resume_unwind(e))
    })
}

/// Whether `batch` may follow the head of `history`, as the core judges it:
/// checked before the commit that publishes it is made.
pub fn check_next(history: &History, batch: &Batch) -> Result<(), String> {
    let mut atoms = Atoms::default();
    let state = facts::rebuild(history, history.checkpoints.len(), &mut atoms)?;
    let config = atoms.of(Atom::Config(history.config_id()));
    // The commit is not made yet; Git's null ID stands for it, which no
    // commit has.
    let head = &history.checkpoints[history.checkpoints.len() - 1].rev;
    let next = Checkpoint {
        rev: Rev::from_git(&"0".repeat(head.hex().len()))?,
        digest: [0; 32],
        batch: batch.clone(),
    };
    let ix = facts::batch(&mut atoms, config, &state, &next);
    let why = facts::refusal(&state, &next);
    ix_step(state, ix).map(|_| ()).ok_or(why)
}
