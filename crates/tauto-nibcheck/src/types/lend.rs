//! The expansion of lending: where the checker read `&x` of a type
//! with `struct &T` as the lent `&T`, the lending is written out as
//! `Lend::lend(&orig x)`. What follows (the class expansion, the borrow check,
//! the backends) sees an ordinary call that builds an ordinary struct.
//!
//! `&rc` is written out here too: a `T` given where a `&rc T` is wanted is
//! `&rc e`, and a `&rc T` read as a borrow of its contents is `&orig e`
//! (then lent like any `&orig`).

use std::cell::RefCell;
use std::collections::HashSet;
use std::sync::Arc;

use tauto_parol::Span;

use super::{Ty, TypeReport};
use super::{check_program_in, prelude_source_for};
use crate::surface::walk;
use crate::surface::{Name, Program, Stmt, SurfaceTerm, TermKind};

/// Whether a program writes `&rc`, in a type or a term: only then may a
/// value be boxed or read where the checker found one.
fn writes_rc(stmts: &[Stmt]) -> bool {
    let mut found = false;
    for s in stmts {
        match s {
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => found |= writes_rc(items),
            _ => walk::visit_roots(s, &mut |t| {
                found |= !walk::visit(t, &mut |t| {
                    !matches!(&*t.kind, TermKind::Borrow { rc: true, .. })
                })
            }),
        }
    }
    found
}

fn declares_lent(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Struct(d) => d.borrowed,
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => declares_lent(items),
        _ => false,
    })
}

/// `program`, and the statements of each file alike, with every lending
/// written as a call of `Lend::lend`. A program that does not check is left as
/// it is, for the checker to report on.
pub fn expand_lends(program: &mut Program, per_file: &mut [Vec<Stmt>]) {
    let rc = writes_rc(&program.stmts);
    if !declares_lent(&program.stmts) && !rc {
        return;
    }
    let report = check_program_in(program, prelude_source_for(program));
    // An instance the class expansion derives (`Debug` of a struct) is not
    // there yet; the check after the expansion reports one that is missing.
    if report
        .errors
        .iter()
        .any(|e| e.message.id != "nibcheck-no-instance")
    {
        return;
    }
    let class = report
        .classes
        .keys()
        .find(|n| n.as_str() == "Lend")
        .cloned();
    if class.is_none() && !rc {
        return;
    }
    let e = Expander {
        report: &report,
        class,
        copies: RefCell::new(report.lent_copies.clone()),
        lends: RefCell::new(report.orig_lends.clone()),
        rc_reads: RefCell::new(report.rc_reads.clone()),
        rc_boxes: RefCell::new(report.rc_boxes.clone()),
        rc_copies: RefCell::new(report.rc_copies.clone()),
    };
    for s in program.stmts.iter_mut() {
        e.stmt(s);
    }
    for file in per_file {
        for s in file.iter_mut() {
            e.stmt(s);
        }
    }
}

struct Expander<'a> {
    report: &'a TypeReport,
    class: Option<Name>,
    /// The spans not yet written: each is written once, at the first term
    /// of that span the walk finishes.
    copies: RefCell<HashSet<Span>>,
    lends: RefCell<HashSet<Span>>,
    rc_reads: RefCell<HashSet<Span>>,
    rc_boxes: RefCell<HashSet<Span>>,
    rc_copies: RefCell<HashSet<Span>>,
}

impl Expander<'_> {
    fn stmt(&self, s: &mut Stmt) {
        match s {
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for i in items {
                    self.stmt(i);
                }
                return;
            }
            Stmt::Assign {
                place: Some(place), ..
            } => self.term(place),
            _ => {}
        }
        walk::roots(s, &mut |t| self.term(t));
    }

    fn is_lent(&self, t: &Ty) -> bool {
        matches!(t, Ty::Named(n, _) if self.report.datas.lent_of.values().any(|l| l == n))
    }

    fn term(&self, t: &mut SurfaceTerm) {
        let lends = match &*t.kind {
            TermKind::Borrow {
                mutable: false,
                orig: false,
                rc: false,
                term,
            } => {
                !matches!(&*term.kind, TermKind::Record { .. })
                    && self.report.terms.get(&t.id()).is_some_and(|ty| self.is_lent(ty))
                    // Lending a lent value is the value itself.
                    && !self.report.terms.get(&term.id()).is_some_and(|ty| self.is_lent(ty))
            }
            _ => false,
        };
        match Arc::make_mut(&mut t.kind) {
            TermKind::Block(stmts) => {
                for s in stmts {
                    self.stmt(s);
                }
            }
            _ => walk::children(t, &mut |c| self.term(c)),
        }
        // `&T { f: e }` is a record of the `struct &T`.
        if let TermKind::Borrow {
            mutable: false,
            orig: false,
            rc: false,
            term,
        } = &*t.kind
            && let TermKind::Record { .. } = &*term.kind
            && let Some(Ty::Named(lent, _)) = self.report.terms.get(&t.id())
            && let Some(ctor) = self
                .report
                .datas
                .decls
                .get(lent)
                .filter(|_| self.report.datas.lent_of.values().any(|l| l == lent))
                .and_then(|d| d.constructors.first())
                .map(|c| c.name.clone())
        {
            let mut record = (**term).clone();
            if let TermKind::Record { name, .. } = Arc::make_mut(&mut record.kind) {
                *name = ctor;
            }
            *t = record;
            return;
        }
        // A `&rc T` read as a borrow of its contents, and a `T` given as a
        // `&rc T`, are written as the terms that do so.
        if self.rc_reads.borrow_mut().remove(&t.span) {
            *t = Self::orig(t);
        } else if self.rc_copies.borrow_mut().remove(&t.span) {
            Self::copy(t);
        } else if self.rc_boxes.borrow_mut().remove(&t.span) {
            *t = Self::boxed(t);
        }
        if lends {
            if let TermKind::Borrow { orig, .. } = Arc::make_mut(&mut t.kind) {
                *orig = true;
            }
            *t = self.call("lend", t);
        } else if self.lends.borrow_mut().remove(&t.span) {
            // `&orig x` given as `&T`.
            *t = self.call("lend", t);
        }
        // A `&T` given as a duplicable `T` is copied by `owned`.
        if self.copies.borrow_mut().remove(&t.span) {
            *t = self.call("owned", t);
        }
    }

    /// `&orig t`: the borrow of the contents of the `&rc T` `t`.
    fn orig(t: &SurfaceTerm) -> SurfaceTerm {
        SurfaceTerm::new(
            TermKind::Borrow {
                mutable: false,
                orig: true,
                rc: false,
                term: Box::new(t.clone()),
            },
            t.span,
        )
    }

    /// `t`, a `&rc T` of a duplicable `T`, copied out: `clone(&orig t)`,
    /// and for a `match`, an `if` or a block, the same in each value it may
    /// end with, so that each copy is made where what it borrows lives.
    fn copy(t: &mut SurfaceTerm) {
        let span = t.span;
        match Arc::make_mut(&mut t.kind) {
            TermKind::Match { arms, .. } => arms.iter_mut().for_each(|a| Self::copy(&mut a.body)),
            TermKind::If {
                then,
                otherwise: Some(otherwise),
                ..
            } => {
                Self::copy(then);
                Self::copy(otherwise);
            }
            TermKind::Block(stmts) if matches!(stmts.last(), Some(Stmt::Expr(_))) => {
                if let Some(Stmt::Expr(last)) = stmts.last_mut() {
                    Self::copy(last);
                }
            }
            _ => {
                let clone = tauto_surface::bindings::library_name("clone");
                *t = SurfaceTerm::new(
                    TermKind::App {
                        function: Box::new(SurfaceTerm::new(TermKind::Var(clone), span)),
                        arguments: vec![Self::orig(t)],
                    },
                    span,
                )
            }
        }
    }

    /// `&rc t`.
    fn boxed(t: &SurfaceTerm) -> SurfaceTerm {
        SurfaceTerm::new(
            TermKind::Borrow {
                mutable: false,
                orig: false,
                rc: true,
                term: Box::new(t.clone()),
            },
            t.span,
        )
    }

    /// `Lend::method(t)`. Without the class (a program read without the
    /// prelude) nothing is lent, and `t` stays.
    fn call(&self, method: &str, t: &SurfaceTerm) -> SurfaceTerm {
        let Some(class) = &self.class else {
            return t.clone();
        };
        let span = t.span;
        let function = SurfaceTerm::new(
            TermKind::Field {
                base: Box::new(SurfaceTerm::new(TermKind::Var(class.clone()), span)),
                name: method.into(),
            },
            span,
        );
        SurfaceTerm::new(
            TermKind::App {
                function: Box::new(function),
                arguments: vec![t.clone()],
            },
            span,
        )
    }
}
