//! Where each standard effect that reaches the top level comes from: the set
//! of functions outside the standard library that perform it
//! (`docs/design/host-effects.md`「Origins」).
//!
//! The origin of one `perform` is the function that holds it as written: a
//! lambda's is the named function around it. A `perform` in the standard
//! library is the origin of none: the function outside it that calls into it
//! is. So the origin of each `perform` is fixed where it is written, and a
//! callback passed through a row variable keeps the origin of the function
//! that wrote it. A call to a function of the program adds that function's
//! origins; an arm that answers an effect completely takes away what its
//! body brings of that effect, and what an arm performs is the origin of the
//! function that holds the arm.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use tauto_parol::Span;

use super::{RowReport, label_host_member};
use crate::surface::{
    FnDecl, Handler, Name, PRELUDE_BASE, Program, Stmt, SurfaceTerm, TermKind, walk,
};

/// A function that performs a standard effect, or the top level.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Origin {
    /// The declaration's name as the program spells it; `None` for the top
    /// level.
    pub name: Option<String>,
    /// Where the declaration is written: the driver reads the module from it.
    pub span: Span,
}

type Origins = BTreeMap<String, BTreeSet<Origin>>;

/// The standard effect a row's member asks of the host, as `host_effects`
/// spells it.
fn host_member(e: &Name) -> Option<String> {
    if let Some(member) = label_host_member(e) {
        return Some(member.to_string());
    }
    crate::host::HOST_EFFECTS
        .iter()
        .any(|n| tauto_surface::bindings::is_library(e, n))
        .then(|| e.to_string())
}

fn in_std(span: Span) -> bool {
    span.start >= PRELUDE_BASE
}

struct Walk<'a> {
    report: &'a RowReport,
    fns: HashMap<&'a Name, &'a FnDecl>,
    done: HashMap<&'a Name, Origins>,
    open: BTreeSet<&'a Name>,
}

impl<'a> Walk<'a> {
    /// The origins of `f`'s body, `f` being the origin of what is performed
    /// in it.
    fn function(&mut self, f: &'a FnDecl) -> Origins {
        if let Some(o) = self.done.get(&f.name) {
            return o.clone();
        }
        // A recursive call adds nothing the body does not already.
        if !self.open.insert(&f.name) {
            return Origins::new();
        }
        let me = Origin {
            name: Some(f.name.to_string()),
            span: f.span,
        };
        let found = self.term(&f.body, &me);
        self.open.remove(&f.name);
        self.done.insert(&f.name, found.clone());
        found
    }

    fn callee(&self, t: &SurfaceTerm) -> Option<&'a FnDecl> {
        let TermKind::App { function, .. } = &*t.kind else {
            return None;
        };
        match &*function.kind {
            TermKind::Var(n) => self.fns.get(n).copied(),
            _ => None,
        }
    }

    fn term(&mut self, t: &'a SurfaceTerm, me: &Origin) -> Origins {
        let mut out = Origins::new();
        if let TermKind::Handle { body, handlers } = &*t.kind {
            let handled: BTreeSet<String> = handlers
                .iter()
                .filter_map(|h| match h {
                    Handler::Operation {
                        effect,
                        patterns,
                        guard: None,
                        ..
                    } if patterns.iter().all(super::irrefutable) => Some(effect.to_string()),
                    _ => None,
                })
                .collect();
            for (e, o) in self.term(body, me) {
                if !handled.contains(&e) {
                    out.entry(e).or_default().extend(o);
                }
            }
            for h in handlers {
                let arm = match h {
                    Handler::Operation { body, .. } | Handler::Return { body, .. } => body,
                };
                merge(&mut out, self.term(arm, me));
            }
            return out;
        }
        // A function of the program, called or passed on: what it performs
        // comes from it.
        if let TermKind::Var(n) = &*t.kind
            && let Some(f) = self.fns.get(n).copied()
            && !in_std(f.span)
        {
            return self.function(f);
        }
        // A `perform`, or a call of the standard library (a callback it is
        // given is followed where it is written, below).
        if let Some(row) = self.report.calls.get(&t.id())
            && self.callee(t).is_none_or(|f| in_std(f.span))
        {
            for e in row.iter().filter_map(host_member) {
                out.entry(e).or_default().insert(me.clone());
            }
        }
        // A function written as an argument runs where the callee calls it:
        // what it brings reaches here only as far as the call's row says,
        // since the callee may answer it (`quiet(() => perform stdout(…))`).
        if let TermKind::App {
            function,
            arguments,
        } = &*t.kind
            && let Some(row) = self.report.calls.get(&t.id())
        {
            let asked: BTreeSet<String> = row.iter().filter_map(host_member).collect();
            merge(&mut out, self.term(function, me));
            for a in arguments {
                let mut theirs = self.term(a, me);
                if matches!(&*a.kind, TermKind::Lam { .. } | TermKind::BorrowLam { .. }) {
                    theirs.retain(|e, _| asked.contains(e));
                }
                merge(&mut out, theirs);
            }
            return out;
        }
        walk::visit_children(t, &mut |c| merge(&mut out, self.term(c, me)));
        out
    }
}

fn merge(into: &mut Origins, from: Origins) {
    for (e, o) in from {
        into.entry(e).or_default().extend(o);
    }
}

/// The origins of each of `report.host_effects`, from the top level of
/// `program`. `top` is where the top level is said to be.
pub fn host_origins(program: &Program, report: &RowReport, top: Span) -> Origins {
    let mut fns = HashMap::new();
    for s in &program.stmts {
        if let Stmt::Fn(f) = s {
            fns.insert(&f.name, f);
        }
    }
    let mut w = Walk {
        report,
        fns,
        done: HashMap::new(),
        open: BTreeSet::new(),
    };
    let me = Origin {
        name: None,
        span: top,
    };
    let mut out = Origins::new();
    for s in &program.stmts {
        match s {
            Stmt::Let { value, .. } | Stmt::Var { value, .. } | Stmt::Assign { value, .. } => {
                merge(&mut out, w.term(value, &me));
            }
            Stmt::Expr(e) => merge(&mut out, w.term(e, &me)),
            Stmt::While { condition, body } => {
                merge(&mut out, w.term(condition, &me));
                merge(&mut out, w.term(body, &me));
            }
            _ => {}
        }
    }
    out.retain(|e, _| report.host_effects.contains(e));
    out
}
