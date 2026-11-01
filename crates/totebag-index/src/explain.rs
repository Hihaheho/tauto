//! Why a package revision may not be adopted, in words. The core answers
//! only yes or no; this walks the same facts to say what is missing, refused
//! or still waiting. It decides nothing: only the core's answer adopts.

use tauto_message::{Message, msg};
use totebag::index::ledger::{Key, Sha256};
use totebag::index::policy::{Rule, Trusted, Witness};
use totebag::index::state::{State, Store};
use totebag::index::strict::time_text;

use crate::core::generated::List;
use crate::core::generated::api::{IxLedger, IxState};
use crate::engine::ledger_of;
use crate::facts::{Atom, Atoms, small};

fn items<A: Clone>(mut l: &List<A>) -> Vec<A> {
    let mut out = Vec::new();
    while let List::Cons(a, rest) = l {
        out.push(a.clone());
        l = rest;
    }
    out
}

/// A length of time, roughly: `3d 4h`, `2h 5m`, `40s`.
pub fn span(secs: u64) -> String {
    let (d, h, m) = (secs / 86_400, secs % 86_400 / 3_600, secs % 3_600 / 60);
    match (d, h, m) {
        (0, 0, 0) => format!("{secs}s"),
        (0, 0, m) => format!("{m}m"),
        (0, h, m) => format!("{h}h {m}m"),
        (d, h, _) => format!("{d}d {h}h"),
    }
}

struct Explainer<'a> {
    store: &'a Store,
    state: &'a State,
    rule: &'a Rule,
    now: u64,
    atoms: Atoms,
    why: Vec<String>,
}

impl Explainer<'_> {
    /// The state of `t` as taken in, with why the rule may not use it now;
    /// `None` when there is none to look into.
    fn live(&mut self, t: &Trusted) -> Option<IxState> {
        let a = &t.alias;
        let Some(l) = self.state.ledger(&t.index) else {
            self.why.push(say!("totebag-why-not-taken-in", alias = a));
            return None;
        };
        if let Some(why) = &l.frozen {
            self.why.push(say!(
                "totebag-why-stopped",
                alias = a,
                rev = l.prefix.rev.short(),
                why = why
            ));
            return None;
        }
        let s = match ledger_of(self.store, l, &mut self.atoms) {
            Ok(IxLedger::IxOpen(s) | IxLedger::IxFrozen(s)) => s,
            Err(e) => {
                self.why.push(say!("totebag-at", place = a, error = e));
                return None;
            }
        };
        let limits = &self.rule.limits;
        match &l.checked {
            None => {
                self.why
                    .push(say!("totebag-why-origin-unchecked", alias = a));
            }
            Some(c) if c.at > self.now => {
                self.why.push(say!(
                    "totebag-why-origin-future",
                    alias = a,
                    time = time_text(c.at)
                ));
            }
            Some(c) if self.now - c.at > limits.max_source_check_age => {
                self.why.push(say!(
                    "totebag-why-origin-stale",
                    alias = a,
                    ago = span(self.now - c.at),
                    allowed = span(limits.max_source_check_age)
                ));
            }
            Some(c) if c.head != l.prefix => {
                self.why.push(say!(
                    "totebag-why-origin-ahead",
                    alias = a,
                    rev = c.head.rev.short()
                ));
            }
            Some(_) => {}
        }
        if s.retired {
            self.why.push(say!("totebag-why-retired", alias = a));
        } else if self.now < small(&s.issued) || self.now >= small(&s.until) {
            self.why.push(say!(
                "totebag-why-batch-not-valid-now",
                alias = a,
                from = time_text(small(&s.issued)),
                until = time_text(small(&s.until))
            ));
        } else if small(&s.until).saturating_sub(small(&s.issued)) > limits.max_checkpoint_lifetime
        {
            self.why.push(say!(
                "totebag-why-batch-too-long",
                alias = a,
                valid = span(small(&s.until).saturating_sub(small(&s.issued))),
                allowed = span(limits.max_checkpoint_lifetime)
            ));
        }
        Some(tauto_rt::Rc::unwrap_or_clone(s))
    }

    /// The earliest of `firsts` from which the age has passed, or why not.
    fn waited(&mut self, who: Message, what: Message, firsts: Vec<u64>) {
        let age = self.rule.limits.min_age;
        match firsts.into_iter().min() {
            None => self
                .why
                .push(say!("totebag-why-not-yet", who = who, what = what)),
            Some(first) if first > self.now || self.now - first < age => {
                self.why.push(say!(
                    "totebag-why-waits",
                    who = who,
                    what = what,
                    time = time_text(first),
                    until = time_text(first.saturating_add(age))
                ));
            }
            Some(_) => {}
        }
    }
}

/// The reasons the revision `key` with the tree `source` may not be adopted
/// at `now` under `rule`. Empty when none was found.
pub fn explain(
    store: &Store,
    state: &State,
    rule: &Rule,
    now: u64,
    key: &Key,
    source: &Sha256,
) -> Vec<String> {
    let mut e = Explainer {
        store,
        state,
        rule,
        now,
        atoms: Atoms::default(),
        why: Vec::new(),
    };
    if now < state.evaluated_at {
        e.why.push(say!(
            "totebag-clock-behind",
            now = time_text(now),
            last = time_text(state.evaluated_at)
        ));
    }
    let k = e.atoms.key(key);
    let digest = e.atoms.of(Atom::Content(*source));
    for o in &rule.observers {
        let Some(s) = e.live(o) else { continue };
        let a = &o.alias;
        if items(&s.withdrawals).contains(&k) {
            e.why.push(say!("totebag-why-withdrew", alias = a));
            continue;
        }
        let Some(obs) = items(&s.observations).into_iter().find(|ob| ob.key == k) else {
            e.why.push(say!("totebag-why-not-observed", alias = a));
            continue;
        };
        match items(&s.votes).into_iter().find(|v| v.key == k) {
            None => e.why.push(say!("totebag-why-not-decided", alias = a)),
            Some(v) if !v.accept => e.why.push(say!("totebag-why-rejected", alias = a)),
            Some(_) => {}
        }
        if obs.digest != digest {
            e.why.push(say!("totebag-why-conflict", alias = a));
            continue;
        }
        e.waited(
            Message::text(a.as_str()),
            msg!("totebag-observed-it"),
            vec![small(&obs.first)],
        );
        // The checkpoints of `o` holding the observation.
        let covering: Vec<_> = items(&s.checkpoints)
            .into_iter()
            .filter(|c| obs.born <= c.sequence)
            .map(|c| c.point)
            .collect();
        let index = e.atoms.of(Atom::Checkpoint(o.index));
        let origin = e.atoms.origin(&o.url, &o.reference);
        for w in &rule.witnesses {
            match w {
                Witness::Local => {
                    let firsts = state
                        .receipts
                        .iter()
                        .filter(|r| {
                            r.index == o.index && r.url == o.url && r.reference == o.reference
                        })
                        .filter(|r| {
                            let p = e.atoms.point(&r.point.rev, &r.point.digest);
                            covering.contains(&p)
                        })
                        .map(|r| r.first_seen_at)
                        .collect();
                    e.waited(
                        msg!("totebag-this-machine"),
                        msg!("totebag-has-had-record", alias = a),
                        firsts,
                    );
                }
                Witness::Remote(t) => {
                    let Some(ws) = e.live(t) else { continue };
                    let firsts = items(&ws.receipts)
                        .into_iter()
                        .filter(|r| r.index == index && r.source == origin)
                        .filter(|r| covering.contains(&r.point))
                        .map(|r| small(&r.first))
                        .collect();
                    e.waited(
                        Message::text(t.alias.as_str()),
                        msg!("totebag-recorded-record", alias = a),
                        firsts,
                    );
                }
            }
        }
    }
    e.why.dedup();
    e.why
}
