//! Where a binding is live: from a point, the program may still read it
//! before a whole write replaces its value (`docs/design/ownership.md`,
//! 「凍結は最後の使用で解ける」). `lin` asks this for the binding that holds
//! a borrow: the owner it borrows stays frozen only while it is live.
//!
//! The walk goes backwards over one function body (or the program's own
//! statements), in the reverse of the evaluation order `lin` walks in, and
//! records for each term and statement the names live right after it. It is
//! by name and errs on the side of live:
//!
//! - a name bound again inside (a pattern, a parameter, a `let` of an inner
//!   block) counts as the outer one where it is read;
//! - only a `let` or `var` statement, and a whole write `x := e` of a name
//!   bound only by `var`, end a name's life;
//! - a closure reads what it captures where it is written and wherever its
//!   name is read, and inside its body everything live where it is written,
//!   or that it captures, is live throughout (it may be called again);
//! - a handler arm may run at any point of the body (each `perform`), and
//!   `k` runs the rest of the body: what the arms read is live throughout
//!   the body, and what the body reads is live throughout the arms;
//! - a loop is walked until its sets no longer change.
//!
//! A point with no record (a span `lin` reports at that no term has) is
//! taken to have every name live, as the rule before this one did.

use std::collections::{BTreeSet, HashMap};

use tauto_parol::Span;

use crate::surface::{FnDecl, Handler, Name, Pattern, Stmt, SurfaceTerm, TermKind};

use super::{free_vars, pattern_names};

type Set = BTreeSet<Name>;

/// The names live after each term and statement of one body, by span.
#[derive(Debug, Default)]
pub struct Live {
    after: HashMap<Span, Set>,
}

impl Live {
    /// The liveness of a function's body: nothing is live after it.
    pub fn of_body(params: &[Name], body: &SurfaceTerm) -> Live {
        let mut w = Walk::new(params, |v| w_term(v, body));
        w.term(body, Set::new());
        w.finish()
    }

    /// The liveness of the program's own statements. The functions it
    /// declares at the top are bodies of their own.
    pub fn of_program(stmts: &[Stmt]) -> Live {
        let mut w = Walk::new(&[], |v| {
            for s in stmts {
                if !matches!(s, Stmt::Fn(_)) {
                    w_stmt(v, s);
                }
            }
        });
        w.stmts(stmts, Set::new(), true);
        w.finish()
    }

    /// Whether `name` may be read after the point `span`: `None` when the
    /// walk recorded no term there.
    pub fn live_after(&self, span: Span, name: &Name) -> Option<bool> {
        self.after.get(&span).map(|s| s.contains(name))
    }
}

struct Walk {
    after: HashMap<Span, Set>,
    /// Names live everywhere in what is walked now: inside a closure's body,
    /// a handler's arm or a handled body.
    extra: Set,
    /// A closure's name, with what it captures: reading it reads them.
    closures: HashMap<Name, Vec<Name>>,
    /// Names bound only by `var` in the body: a whole write ends their life.
    killable: BTreeSet<Name>,
}

/// The names a body binds, and how: `var` or any other way.
#[derive(Default)]
struct Binders {
    vars: BTreeSet<Name>,
    others: BTreeSet<Name>,
    closures: HashMap<Name, Vec<Name>>,
}

fn w_term(b: &mut Binders, t: &SurfaceTerm) {
    match &*t.kind {
        TermKind::Lam { params, body, .. } => {
            b.others.extend(params.iter().cloned());
            w_term(b, body);
        }
        TermKind::Match {
            arms, scrutinee, ..
        } => {
            w_term(b, scrutinee);
            for a in arms {
                let mut names = Vec::new();
                pattern_names(&a.pattern, &mut names);
                b.others.extend(names);
                if let Some(g) = &a.guard {
                    w_term(b, g);
                }
                w_term(b, &a.body);
            }
        }
        TermKind::Handle { body, handlers } => {
            w_term(b, body);
            for h in handlers {
                let (pats, cont, body): (Vec<&Pattern>, Option<&Name>, &SurfaceTerm) = match h {
                    Handler::Return { pattern, body } => (vec![pattern], None, body),
                    Handler::Operation {
                        patterns,
                        cont,
                        body,
                        ..
                    } => (patterns.iter().collect(), cont.as_ref(), body),
                };
                let mut names = Vec::new();
                for p in pats {
                    pattern_names(p, &mut names);
                }
                b.others.extend(names);
                b.others.extend(cont.cloned());
                w_term(b, body);
            }
        }
        TermKind::Block(stmts) => stmts.iter().for_each(|s| w_stmt(b, s)),
        _ => each_child(t, |c| w_term(b, c)),
    }
}

fn w_stmt(b: &mut Binders, s: &Stmt) {
    match s {
        Stmt::Let { name, value, .. } => {
            b.others.insert(name.clone());
            if is_closure(value) {
                b.closures.insert(name.clone(), free_vars(value));
            }
            w_term(b, value);
        }
        Stmt::Var { name, value, .. } => {
            b.vars.insert(name.clone());
            w_term(b, value);
        }
        Stmt::Assign { value, place, .. } => {
            if let Some(p) = place {
                w_term(b, p);
            }
            w_term(b, value);
        }
        Stmt::Fn(f) => {
            b.others.insert(f.name.clone());
            b.others.extend(f.params.iter().cloned());
            b.closures.insert(f.name.clone(), fn_captures(f));
            w_term(b, &f.body);
        }
        Stmt::While { condition, body } => {
            w_term(b, condition);
            w_term(b, body);
        }
        Stmt::Return(Some(e)) | Stmt::Expr(e) => w_term(b, e),
        // `lower_fors` / `lower_loops` expand them where the program is read.
        Stmt::For { .. } | Stmt::Loop { .. } | Stmt::Break(_) | Stmt::Continue => {}
        _ => {}
    }
}

fn is_closure(t: &SurfaceTerm) -> bool {
    match &*t.kind {
        TermKind::Lam { .. } | TermKind::BorrowLam { .. } => true,
        TermKind::Ascribe { term, .. } => is_closure(term),
        _ => false,
    }
}

fn fn_captures(f: &FnDecl) -> Vec<Name> {
    let lam = SurfaceTerm::new(
        TermKind::Lam {
            params: f.params.clone(),
            unused_params: Vec::new(),
            body: Box::new(f.body.clone()),
            types: Vec::new(),
        },
        f.span,
    );
    let mut free = free_vars(&lam);
    free.retain(|n| n != &f.name);
    free
}

/// The direct subterms of `t` in evaluation order, for the kinds whose
/// walk needs nothing more.
fn each_child(t: &SurfaceTerm, mut f: impl FnMut(&SurfaceTerm)) {
    match &*t.kind {
        TermKind::App {
            function,
            arguments,
        } => {
            f(function);
            arguments.iter().for_each(f);
        }
        TermKind::BorrowLam { lam, .. } => f(lam),
        TermKind::If {
            condition,
            then,
            otherwise,
        } => {
            f(condition);
            f(then);
            if let Some(o) = otherwise {
                f(o);
            }
        }
        TermKind::Field { base, .. } => f(base),
        TermKind::Ascribe { term, .. }
        | TermKind::Tagged { term, .. }
        | TermKind::Borrow { term, .. } => f(term),
        TermKind::Union(items) => items.iter().for_each(f),
        TermKind::Record { fields, base, .. } => {
            fields.iter().for_each(|(_, v)| f(v));
            if let Some(b) = base {
                f(b);
            }
        }
        TermKind::Perform { args, .. } => args.iter().for_each(f),
        TermKind::Budget { steps, body, .. } => {
            f(steps);
            f(body);
        }
        _ => {}
    }
}

impl Walk {
    fn new(params: &[Name], collect: impl FnOnce(&mut Binders)) -> Walk {
        let mut b = Binders::default();
        b.others.extend(params.iter().cloned());
        collect(&mut b);
        let killable = b.vars.difference(&b.others).cloned().collect();
        Walk {
            after: HashMap::new(),
            extra: Set::new(),
            closures: b.closures,
            killable,
        }
    }

    fn finish(self) -> Live {
        Live { after: self.after }
    }

    fn record(&mut self, span: Span, out: &Set) {
        let entry = self.after.entry(span).or_default();
        entry.extend(out.iter().cloned());
        entry.extend(self.extra.iter().cloned());
    }

    /// Reading `name`: it, and what it captures when it is a closure.
    fn gen_name(&self, name: &Name, live: &mut Set) {
        let mut todo = vec![name.clone()];
        while let Some(n) = todo.pop() {
            if live.insert(n.clone())
                && let Some(caps) = self.closures.get(&n)
            {
                todo.extend(caps.iter().cloned());
            }
        }
    }

    /// Walks `body` with `inside` live throughout it, as a closure's body or
    /// an arm is: what is live after it is `inside` alone.
    fn throughout(&mut self, inside: &Set, f: impl FnOnce(&mut Self, Set) -> Set) -> Set {
        let outer = std::mem::take(&mut self.extra);
        self.extra = outer.union(inside).cloned().collect();
        let extra = self.extra.clone();
        let live_in = f(self, extra);
        self.extra = outer;
        live_in
    }

    /// The names live before `t`, given those live after it.
    fn term(&mut self, t: &SurfaceTerm, out: Set) -> Set {
        self.record(t.span, &out);
        match &*t.kind {
            TermKind::Var(n) => {
                let mut live = out;
                self.gen_name(n, &mut live);
                live
            }
            TermKind::App {
                function,
                arguments,
            } => {
                let mut live = out;
                for a in arguments.iter().rev() {
                    live = self.term(a, live);
                }
                self.term(function, live)
            }
            TermKind::Lam { .. } | TermKind::BorrowLam { .. } => {
                let mut live = out.clone();
                for n in free_vars(t) {
                    self.gen_name(&n, &mut live);
                }
                let inside = live.clone();
                let body = match &*t.kind {
                    TermKind::BorrowLam { lam, .. } => match &*lam.kind {
                        TermKind::Lam { body, .. } => {
                            self.record(lam.span, &out);
                            body
                        }
                        _ => return live,
                    },
                    TermKind::Lam { body, .. } => body,
                    _ => unreachable!(),
                };
                self.throughout(&inside, |w, extra| w.term(body, extra));
                live
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                let mut live = self.term(then, out.clone());
                match otherwise {
                    Some(o) => live.extend(self.term(o, out)),
                    None => live.extend(out),
                }
                self.term(condition, live)
            }
            TermKind::Block(stmts) => self.stmts(stmts, out, false),
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                let mut live = Set::new();
                for a in arms {
                    let mut l = self.term(&a.body, out.clone());
                    if let Some(g) = &a.guard {
                        l = self.term(g, l);
                    }
                    live.extend(l);
                }
                if arms.is_empty() {
                    live = out;
                }
                self.term(scrutinee, live)
            }
            TermKind::Handle { body, handlers } => {
                // What the body reads anywhere is live in the arms (`k`
                // resumes it), and what the arms read is live anywhere in
                // the body (each `perform` may run one).
                let mut body_reads = Set::new();
                for n in free_vars(body) {
                    self.gen_name(&n, &mut body_reads);
                }
                let in_arms: Set = out.union(&body_reads).cloned().collect();
                let mut arm_reads = Set::new();
                for h in handlers {
                    let (guard, body) = match h {
                        Handler::Return { body, .. } => (None, body),
                        Handler::Operation { guard, body, .. } => (guard.as_ref(), body),
                    };
                    let live = self.throughout(&in_arms, |w, extra| {
                        let l = w.term(body, extra);
                        match guard {
                            Some(g) => w.term(g, l),
                            None => l,
                        }
                    });
                    arm_reads.extend(live);
                }
                self.throughout(&arm_reads, |w, extra| {
                    let after: Set = out.union(&extra).cloned().collect();
                    w.term(body, after)
                })
            }
            _ => {
                let mut children = Vec::new();
                each_child(t, |c| children.push(c.clone()));
                let mut live = out;
                for c in children.iter().rev() {
                    live = self.term(c, live);
                }
                live
            }
        }
    }

    /// The names live before the statements, given those live after them.
    /// The names a block binds are its own: one live after the block is the
    /// outer binding of that name, which the block does not end.
    fn stmts(&mut self, stmts: &[Stmt], out: Set, root: bool) -> Set {
        let mut live = out.clone();
        let mut bound = Vec::new();
        for s in stmts.iter().rev() {
            if root && matches!(s, Stmt::Fn(_)) {
                continue;
            }
            live = self.stmt(s, live, &mut bound);
        }
        for n in bound {
            if out.contains(&n) {
                live.insert(n);
            }
        }
        live
    }

    fn stmt(&mut self, s: &Stmt, out: Set, bound: &mut Vec<Name>) -> Set {
        self.record(super::stmt_span(s), &out);
        match s {
            Stmt::Let { name, value, .. } | Stmt::Var { name, value, .. } => {
                let mut live = out;
                live.remove(name);
                bound.push(name.clone());
                self.term(value, live)
            }
            Stmt::Assign {
                name,
                place,
                value,
                deref,
            } => {
                let mut live = out;
                match place {
                    // `x.f := e` writes into the value: it reads `x`.
                    Some(p) => {
                        self.gen_name(name, &mut live);
                        live = self.term(p, live);
                    }
                    // `x := e` of a `var` replaces its value; `*x := e`
                    // writes through it, which reads it.
                    None if deref.is_none() && self.killable.contains(name) => {
                        live.remove(name);
                    }
                    // A whole write through a `&mut` binding.
                    None => self.gen_name(name, &mut live),
                }
                self.term(value, live)
            }
            Stmt::Fn(f) => {
                let mut live = out;
                live.remove(&f.name);
                bound.push(f.name.clone());
                let caps = self.closures.get(&f.name).cloned().unwrap_or_default();
                for n in &caps {
                    self.gen_name(n, &mut live);
                }
                let inside = live.clone();
                self.throughout(&inside, |w, extra| w.term(&f.body, extra));
                live
            }
            Stmt::While { condition, body } => {
                // Before the condition: what is live after the loop, and
                // what the body reads before it comes back here.
                let mut head = out.clone();
                loop {
                    let after_body = head.clone();
                    let before_body = self.term(body, after_body);
                    let after_cond: Set = out.union(&before_body).cloned().collect();
                    let before_cond = self.term(condition, after_cond);
                    let next: Set = head.union(&before_cond).cloned().collect();
                    if next == head {
                        break head;
                    }
                    head = next;
                }
            }
            Stmt::Return(e) => match e {
                Some(e) => self.term(e, Set::new()),
                None => Set::new(),
            },
            Stmt::Expr(e) => self.term(e, out),
            // `lower_fors` / `lower_loops` expand them where the program is read.
            Stmt::For { .. } | Stmt::Loop { .. } | Stmt::Break(_) | Stmt::Continue => out,
            _ => out,
        }
    }
}
