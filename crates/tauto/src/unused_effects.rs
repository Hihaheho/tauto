//! Unused effects in written rows, and `^` unused assertions on them.
//!
//! A name in a function's row that the body never performs is unused. An
//! effect set (`Host`) is unused only when none of its members are performed;
//! naming the set while using some members is fine. `^name` suppresses the
//! unused warning when confirmed unused, and is an error when the name is used.

use tauto_message::msg;
use tauto_surface::identity::DeclRef;

use crate::deadcode::Warning;
use crate::rows::{Row, RowReport};
use crate::surface::{FnDecl, Name, Program, Stmt, SurfaceTerm, TermKind, WrittenRowEffect};

/// Warnings and marker errors for unused effects in the program's written rows.
pub fn analyze(program: &Program, rows: &RowReport) -> Vec<Warning> {
    let by_body: std::collections::HashMap<_, &Row> = rows
        .declarations
        .iter()
        .map(|d| (d.body, &d.inferred))
        .collect();
    let mut out = Vec::new();
    for f in all_fns(program) {
        let Some(inferred) = by_body.get(&f.body.id()) else {
            continue;
        };
        let Some(entries) = &f.written_effects else {
            continue;
        };
        let contract = f.effects.as_deref();
        for entry in entries {
            check_entry(entry, inferred, contract, &mut out);
        }
    }
    out
}

fn check_entry(
    entry: &WrittenRowEffect,
    inferred: &Row,
    contract: Option<&[Name]>,
    out: &mut Vec<Warning>,
) {
    // A row variable is a capability the caller fills; it is not an unused
    // effect of this body.
    if entry.name.row_variable().is_some() || entry.name.starts_with('|') {
        return;
    }
    let used = effect_used(entry, inferred, contract);
    match (entry.unused, used) {
        (None, false) => out.push(Warning {
            code: "unused_effect",
            message: msg!("tauto-unused-effect", name = entry.name.to_string()),
            span: entry.span,
        }),
        (Some(span), true) => out.push(Warning {
            code: "unused_marker_used",
            message: msg!(
                "tauto-unused-effect-marker-used",
                name = entry.name.to_string()
            ),
            span,
        }),
        (Some(_), false) | (None, true) => {}
    }
}

/// Whether the written entry is used by the body: for a set, whether any
/// member is performed; for an atomic effect, whether that effect is.
fn effect_used(entry: &WrittenRowEffect, inferred: &Row, contract: Option<&[Name]>) -> bool {
    if let Some(members) = &entry.members {
        // Set members may still be applied forms (`log(Text)`); resolve them
        // through the function's indexed contract as for a written atom.
        return members
            .iter()
            .any(|member| name_used(member, inferred, contract));
    }
    name_used(&entry.name, inferred, contract)
}

fn name_used(written: &Name, inferred: &Row, contract: Option<&[Name]>) -> bool {
    if row_has(inferred, written) {
        return true;
    }
    let Some(contract) = contract else {
        return false;
    };
    contract_entries(contract, written)
        .into_iter()
        .any(|indexed| row_has(inferred, indexed))
}

fn row_has(row: &Row, effect: &Name) -> bool {
    row.contains(effect) || row.iter().any(|e| e == effect)
}

/// Contract entries that are the indexed form of a written row name: same
/// resolved operation, and for a concrete application the same type arguments
/// (via the specialization key), including a universal's family head and any
/// of its instances.
fn contract_entries<'a>(contract: &'a [Name], written: &Name) -> Vec<&'a Name> {
    let exact: Vec<&Name> = contract.iter().filter(|n| *n == written).collect();
    if !exact.is_empty() {
        return exact;
    }
    let Name::Effect(effect) = written else {
        return Vec::new();
    };
    let op = effect.effect();
    if effect.is_universal() {
        return contract
            .iter()
            .filter(|entry| family_member(op, entry))
            .collect();
    }
    let specialized: Vec<&Name> = contract
        .iter()
        .filter(|entry| specialized_instance(op, effect.argument_key(), entry))
        .collect();
    if !specialized.is_empty() {
        return specialized;
    }
    // `log(() -> Unit)` and similar: indexing collapses some applications to
    // the bare operation in the contract while the written entry stays applied.
    contract
        .iter()
        .filter(|entry| {
            matches!(
                entry,
                Name::Global(g) if g.origin().is_none() && same_operation(op, g)
            )
        })
        .collect()
}

/// Whether `entry` is the bare operation or one of its specialized instances.
fn family_member(op: &DeclRef, entry: &Name) -> bool {
    match entry {
        Name::Global(g) => {
            same_operation(op, g) || g.origin().is_some_and(|origin| same_operation(op, origin))
        }
        Name::Effect(effect) => same_operation(op, effect.effect()),
        _ => false,
    }
}

/// Whether `entry` is `op` specialized at `argument_key` (same applied args).
fn specialized_instance(op: &DeclRef, argument_key: &str, entry: &Name) -> bool {
    let Name::Global(specialized) = entry else {
        return false;
    };
    let Some(origin) = specialized.origin() else {
        return false;
    };
    // Index labels use `@^`; they are not applied type arguments.
    if specialized.display().contains("@^") {
        return false;
    }
    if !same_operation(op, origin) {
        return false;
    }
    // Specialize the contract's origin with the written entry's argument key:
    // the same key yields the same specialized declaration.
    &origin.specialize(argument_key, specialized.display()) == specialized
}

/// Whether two declaration references are the same operation: equal, or one is
/// a path-qualified spelling of the other (`fail` vs `module::fail`).
fn same_operation(a: &DeclRef, b: &DeclRef) -> bool {
    a == b
        || (a.source_display() == b.source_display()
            && (a.display() == b.display()
                || a.display().ends_with(b.display())
                || b.display().ends_with(a.display())))
}

fn all_fns(program: &Program) -> Vec<&FnDecl> {
    let mut out = Vec::new();
    collect_fns(&program.stmts, &mut out);
    out
}

fn collect_fns<'a>(stmts: &'a [Stmt], out: &mut Vec<&'a FnDecl>) {
    for s in stmts {
        match s {
            Stmt::Fn(d) => {
                out.push(d);
                collect_term_fns(&d.body, out);
            }
            Stmt::Class(c) => {
                for m in &c.methods {
                    out.push(m);
                    collect_term_fns(&m.body, out);
                }
            }
            Stmt::Instance(i) => {
                for m in &i.methods {
                    out.push(m);
                    collect_term_fns(&m.body, out);
                }
            }
            Stmt::Extern { fns, .. } => {
                for m in fns {
                    out.push(m);
                    collect_term_fns(&m.body, out);
                }
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => collect_fns(items, out),
            Stmt::Attributed { stmt, .. } => collect_fns(std::slice::from_ref(stmt), out),
            Stmt::Let { value, .. } | Stmt::Var { value, .. } => collect_term_fns(value, out),
            _ => {}
        }
    }
}

fn collect_term_fns<'a>(t: &'a SurfaceTerm, out: &mut Vec<&'a FnDecl>) {
    match &*t.kind {
        TermKind::Block(stmts) => collect_fns(stmts, out),
        TermKind::Lam { body, .. }
        | TermKind::Pi {
            result: body, ..
        }
        | TermKind::Exists { body, .. }
        | TermKind::Budget { body, .. } => collect_term_fns(body, out),
        TermKind::App {
            function,
            arguments,
        } => {
            collect_term_fns(function, out);
            for a in arguments {
                collect_term_fns(a, out);
            }
        }
        TermKind::Match {
            scrutinee, arms, ..
        } => {
            collect_term_fns(scrutinee, out);
            for arm in arms {
                collect_term_fns(&arm.body, out);
            }
        }
        TermKind::Handle { body, handlers } => {
            collect_term_fns(body, out);
            for h in handlers {
                match h {
                    crate::surface::Handler::Return { body, .. }
                    | crate::surface::Handler::Operation { body, .. } => {
                        collect_term_fns(body, out);
                    }
                }
            }
        }
        TermKind::If {
            condition,
            then,
            otherwise,
        } => {
            collect_term_fns(condition, out);
            collect_term_fns(then, out);
            if let Some(e) = otherwise {
                collect_term_fns(e, out);
            }
        }
        TermKind::Ascribe { term, .. } | TermKind::Field { base: term, .. } => {
            collect_term_fns(term, out);
        }
        _ => {}
    }
}
