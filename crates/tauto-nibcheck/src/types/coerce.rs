//! The expansion of `coerce` fields: where the checker read a struct through
//! its `coerce` field (`docs/design/ownership.md`「Coercing structs (`coerce`)」),
//! the field is written out. `&w` passed as `&T` becomes `&w.value`, the base
//! `w` of `w.x` becomes `w.value`, `w` passed as `T` is taken apart by a `match`, and
//! `w.Placed::at` becomes `w.at`. The structs then lose their `coerce`, so
//! what follows (the borrow check, the backends, the kernel) sees fields
//! only, read as they are written.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use tauto_parol::Span;

use super::Datas;
use super::{check_program_in, prelude_source_for};
use crate::surface::walk;
use crate::surface::{MatchArm, Name, Pattern, Program, Stmt, SurfaceTerm, TermKind};

/// Whether a struct of the statements has a `coerce` field.
fn declares_coerce(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Struct(d) => d.coerce.is_some(),
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => declares_coerce(items),
        _ => false,
    })
}

/// `program`, and the statements of each file alike, with every coercion
/// written as a field. A program that does not check is left as it is, for
/// the checker to report on.
pub fn expand_coercions(program: &mut Program, per_file: &mut [Vec<Stmt>]) {
    // A struct of the prelude may have one too (`std/builtin/region.taut`).
    if !declares_coerce(&program.stmts) && !declares_coerce(&prelude_source_for(program).stmts) {
        return;
    }
    let report = check_program_in(program, prelude_source_for(program));
    if !report.errors.is_empty() {
        return;
    }
    let expand = |stmts: &mut Vec<Stmt>| {
        let mut e = Expander {
            coercions: report.coercions.clone(),
            qualified: report.qualified_fields.clone(),
            moves: report.coercion_moves.clone(),
            datas: &report.datas,
            next: 0,
        };
        for s in stmts.iter_mut() {
            e.stmt(s);
        }
    };
    expand(&mut program.stmts);
    for file in per_file {
        expand(file);
    }
}

struct Expander<'a> {
    coercions: HashMap<Span, Vec<(Name, String)>>,
    qualified: HashMap<Span, String>,
    moves: HashSet<Span>,
    datas: &'a Datas,
    /// The number of the next name a taking apart binds.
    next: usize,
}

impl Expander<'_> {
    fn stmt(&mut self, s: &mut Stmt) {
        match s {
            Stmt::Struct(d) => d.coerce = None,
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

    fn term(&mut self, t: &mut SurfaceTerm) {
        match Arc::make_mut(&mut t.kind) {
            // The statements of a block, with the places their assignments write.
            TermKind::Block(stmts) => {
                for s in stmts {
                    self.stmt(s);
                }
            }
            _ => walk::children(t, &mut |c| self.term(c)),
        }
        if let Some(field) = self.qualified.remove(&t.span)
            && let TermKind::Field { name, .. } = Arc::make_mut(&mut t.kind)
        {
            *name = field;
            *t = t.clone().own_field();
        }
        let Some(steps) = self.coercions.remove(&t.span) else {
            return;
        };
        if self.moves.contains(&t.span) {
            *t = self.take_apart(t, &steps);
            return;
        }
        match Arc::make_mut(&mut t.kind) {
            // `&w` read as `&T` lends `w.value`.
            TermKind::Borrow { term, .. } => **term = project(term, &steps),
            _ => *t = project(t, &steps),
        }
    }

    /// `W` given as `T`: `match w { W { value: v, at: _ } => v }` for each
    /// step. A field is not moved out of a value on its own, so the value is
    /// taken apart, and its other fields are dropped as a pattern drops them.
    fn take_apart(&mut self, e: &SurfaceTerm, steps: &[(Name, String)]) -> SurfaceTerm {
        steps.iter().fold(e.clone(), |value, (data, field)| {
            let span = value.span;
            let bound: Name = format!("coerce#{}", self.next).into();
            self.next += 1;
            let fields = self
                .datas
                .decls
                .get(data)
                .map(|d| d.constructors[0].fields.clone())
                .unwrap_or_default()
                .into_iter()
                .filter_map(|(n, _)| n)
                .map(|n| {
                    let p = if &n == field {
                        Pattern::bind(bound.clone())
                    } else {
                        Pattern::Wild
                    };
                    (n, p)
                })
                .collect();
            SurfaceTerm::new(
                TermKind::Match {
                    scrutinee: Box::new(value),
                    result: None,
                    binder: None,
                    binder_unused: None,
                    arms: vec![MatchArm {
                        pattern: Pattern::Record {
                            name: data.clone(),
                            fields,
                        },
                        guard: None,
                        goal: None,
                        body: SurfaceTerm::new(TermKind::Var(bound), span),
                    }],
                },
                span,
            )
        })
    }
}

/// `e.f.g`: the `coerce` field of each step, at the span of `e`.
fn project(e: &SurfaceTerm, steps: &[(Name, String)]) -> SurfaceTerm {
    steps.iter().fold(e.clone(), |base, (_, field)| {
        let span = base.span;
        SurfaceTerm::new(
            TermKind::Field {
                base: Box::new(base),
                name: field.clone(),
            },
            span,
        )
        .own_field()
    })
}
