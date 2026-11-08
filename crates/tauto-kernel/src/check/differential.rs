//! Differential test of the two checkers: random theorems, each judged by the
//! named checker (`check.rs`, which hands what it accepts to the core) and by
//! the core (`core.rs`) alone on the term as written. A theorem one of them
//! accepts and the other rejects is a disagreement; the test fails on one and
//! prints it, shrunk.
//!
//! The theorems are about conversion (`Eq(T, a, b)` proved by `Refl`), with
//! the reductions the kernels share (beta, delta of definitions and functions,
//! iota of `Nat::rec`, literal arithmetic), eta of functions, proof irrelevance
//! (two proofs of one proposition inside a type), and typing with mistakes.
//! `KERNELS_DIFF_CASES` sets the number of theorems (default 300) and
//! `KERNELS_DIFF_SEED` the seed; `KERNELS_DIFF_TRACE` prints each theorem
//! before it is judged (to find one that does not finish).

use super::parse_program;
use super::{Kernel, Verdict};
use crate::surface::{Name, Stmt};

#[path = "../../tests/support/differential.rs"]
mod generator;
use generator::E::*;
use generator::*;

#[derive(Clone, Copy, PartialEq, Debug)]
struct Judgement {
    named: bool,
    /// The core on the named checker's elaborated term, when it accepts.
    core_elaborated: Option<bool>,
    core_written: bool,
}

impl Judgement {
    fn disagreement(&self) -> Option<&'static str> {
        match (self.named, self.core_elaborated, self.core_written) {
            (true, Some(false), _) => Some("the named checker accepts, the core rejects its term"),
            (false, _, true) => Some("the core accepts, the named checker rejects"),
            _ => None,
        }
    }
}

fn base() -> Kernel {
    let mut k = Kernel::new();
    let prelude = super::kernel_prelude().unwrap();
    for e in k.declare(&prelude, true) {
        assert!(
            !matches!(e.verdict, Verdict::Failed(_)),
            "prelude: {}",
            e.name
        );
    }
    let prefix = parse_program(&prefix()).unwrap();
    for e in k.declare(&prefix, false) {
        assert!(
            matches!(e.verdict, Verdict::Checked { .. }),
            "prefix: {}: {:?}",
            e.name,
            e.verdict
        );
    }
    k
}

fn judge(base: &Kernel, case: &Case) -> Option<Judgement> {
    let program = parse_program(&case.source("t")).ok()?;
    let Some(Stmt::Theorem(t)) = program.stmts.first() else {
        return None;
    };
    let mut named = base.clone();
    let verdict = named.declare(&program, false).pop()?.verdict;
    let (named, core_elaborated) = match &verdict {
        Verdict::Checked { .. } => (true, Some(true)),
        Verdict::Failed(d) if d.message.id == "kernel-core-rejects" => (true, Some(false)),
        _ => (false, None),
    };
    let mut core = base.clone();
    let written = (|| {
        let statement = core.telescope(&t.params, &t.ty).ok()?;
        let statement = core.shape(&statement).ok()?;
        let lam = core
            .shape(&core.lambda_of(&t.params, t.body.as_ref()?).ok()?)
            .ok()?;
        Some(
            core.core
                .add_decl(&Name::from("t"), &statement, Some(&lam), false)
                .is_ok(),
        )
    })();
    Some(Judgement {
        named,
        core_elaborated,
        core_written: written.unwrap_or(false),
    })
}

/// Every term of the case with one part replaced by something smaller.
fn shrinks(case: &Case) -> Vec<Case> {
    fn smaller(e: &E) -> Vec<E> {
        let mut out = Vec::new();
        match e {
            Num(k) if *k > 0 => {
                out.push(Num(0));
                out.push(Num(k / 2));
                out.push(Num(k - 1));
            }
            App(h, args) => {
                out.extend(args.iter().cloned());
                for i in 0..args.len() {
                    for s in smaller(&args[i]) {
                        let mut args = args.clone();
                        args[i] = s;
                        out.push(App(h.clone(), args));
                    }
                }
            }
            Lam(x, b) => {
                for s in smaller(b) {
                    out.push(Lam(x.clone(), Box::new(s)));
                }
            }
            Op(o, a, b) => {
                out.push((**a).clone());
                out.push((**b).clone());
                for s in smaller(a) {
                    out.push(Op(o, Box::new(s), b.clone()));
                }
                for s in smaller(b) {
                    out.push(Op(o, a.clone(), Box::new(s)));
                }
            }
            _ => {}
        }
        if !matches!(e, Num(0)) {
            out.push(Num(0));
        }
        out
    }
    let mut out = Vec::new();
    for i in 0..case.params.len() {
        let mut c = case.clone();
        c.params.remove(i);
        out.push(c);
    }
    for s in smaller(&case.statement) {
        out.push(Case {
            statement: s,
            ..case.clone()
        });
    }
    for s in smaller(&case.proof) {
        out.push(Case {
            proof: s,
            ..case.clone()
        });
    }
    for i in 0..case.params.len() {
        for s in smaller(&case.params[i].1) {
            let mut c = case.clone();
            c.params[i].1 = s;
            out.push(c);
        }
    }
    out
}

fn shrink(base: &Kernel, case: Case, kind: &str) -> Case {
    let mut case = case;
    'outer: for _ in 0..200 {
        for c in shrinks(&case) {
            if judge(base, &c).and_then(|j| j.disagreement()) == Some(kind) {
                case = c;
                continue 'outer;
            }
        }
        break;
    }
    case
}

#[test]
fn the_two_checkers_agree() {
    with_stack(two_checkers_agree);
}

fn two_checkers_agree() {
    let cases: usize = std::env::var("KERNELS_DIFF_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(300);
    let seed: u64 = std::env::var("KERNELS_DIFF_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0x2545_F491_4F6C_DD1D);
    let base = base();
    let mut g = Gen {
        rng: Rng(seed),
        fresh: 0,
        recs: 0,
    };
    let (mut accepted, mut rejected, mut unreadable) = (0, 0, 0);
    let mut found: Vec<(String, Case)> = Vec::new();
    for _ in 0..cases {
        let case = g.case();
        if std::env::var("KERNELS_DIFF_TRACE").is_ok() {
            eprint!("{}", case.source("t"));
        }
        let Some(j) = judge(&base, &case) else {
            unreadable += 1;
            continue;
        };
        match j.disagreement() {
            Some(kind) => {
                if !found.iter().any(|(k, _)| k == kind) || found.len() < 8 {
                    found.push((kind.to_string(), shrink(&base, case, kind)));
                }
            }
            None if j.named => accepted += 1,
            None => rejected += 1,
        }
    }
    eprintln!(
        "kernels: {accepted} accepted by both, {rejected} rejected by both, {} disagreements, {unreadable} not read",
        found.len()
    );
    let mut report = String::new();
    for (kind, case) in &found {
        report.push_str(&format!("{kind}:\n  {}", case.source("t")));
    }
    assert!(found.is_empty(), "the checkers disagree:\n{report}");
    assert!(
        accepted > cases / 10 && rejected > cases / 20,
        "{accepted} accepted, {rejected} rejected"
    );
}
