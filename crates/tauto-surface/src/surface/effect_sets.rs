//! `effect Host {div, stdout}` names a set of effects. A row that writes
//! the name means the effects of the set: this pass writes them in its place,
//! in every row of the program, and drops the declaration. The checkers and
//! the backends see only the effects, so the name adds nothing to what they
//! trust.
//!
//! A program sees the prelude's sets, and its own. Its own declaration of an
//! effect hides the prelude's set of that name.

use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

use crate::span::Span;
use tauto_message::{Message, msg};

use super::program::{FnDecl, Stmt};
use super::{TermKind, walk};

/// Each set, by its name: the effects as written.
pub type Sets = HashMap<String, (Vec<super::Name>, Span)>;

/// The prelude's sets, each written out to effects only.
pub fn prelude_sets() -> &'static HashMap<String, Vec<super::Name>> {
    static SETS: OnceLock<HashMap<String, Vec<super::Name>>> = OnceLock::new();
    SETS.get_or_init(|| {
        let Ok(program) = super::program::parse_builtin_at(crate::nibstd::PRELUDE, 0) else {
            return HashMap::new();
        };
        let mut sets = Sets::new();
        collect(&program.stmts, &mut sets);
        let mut errors = Vec::new();
        written_out(&sets, &HashMap::new(), &mut errors)
    })
}

/// The sets `stmts` declares, at the top or in a `module` or `mutual`.
pub fn collect(stmts: &[Stmt], out: &mut Sets) {
    for s in stmts {
        match s {
            Stmt::Effect(e) if e.generics.is_empty() => {
                if let Some(set) = &e.set {
                    out.insert(e.name.to_string(), (set.clone(), e.span));
                }
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => collect(items, out),
            _ => {}
        }
    }
}

/// Writes each set of `stmts` and of the prelude out in every row of
/// `stmts`, and drops the sets' declarations. `others` are the sets other
/// files declare, which a file may name too.
pub fn expand(stmts: &mut Vec<Stmt>, others: &Sets) -> Vec<(Message, Span)> {
    expand_resolving(stmts, others, &mut |_| {})
}

/// Resolves the effects inserted by a set in the declaration environment.
/// References already written in a row retain their source visibility checks.
pub fn expand_resolving(
    stmts: &mut Vec<Stmt>,
    others: &Sets,
    resolve: &mut dyn FnMut(&mut super::Name),
) -> Vec<(Message, Span)> {
    let mut errors = Vec::new();
    generic_sets(stmts, &mut errors);
    let mut own = Sets::new();
    collect(stmts, &mut own);
    let mut declared = HashSet::new();
    effects_declared(stmts, &mut declared);
    let prelude = prelude_sets();
    let any_named = !own.is_empty()
        || others.keys().any(|n| !declared.contains(n))
        || prelude.keys().any(|n| !declared.contains(n));
    if !any_named {
        drop_sets(stmts);
        return errors;
    }
    let mut sets: Sets = others
        .iter()
        .filter(|(n, _)| !declared.contains(*n))
        .map(|(n, s)| (n.clone(), s.clone()))
        .collect();
    sets.extend(own);
    // A set of the prelude means the effects the prelude declares, by their
    // references: a file that names the set does not name, or import, each
    // of its members.
    let mut outer: HashMap<String, Vec<super::Name>> = prelude
        .iter()
        .filter(|(n, _)| !declared.contains(*n) && !sets.contains_key(*n))
        .map(|(n, s)| {
            let members = s
                .iter()
                .map(|m| match m {
                    // `∀ T. spawn(() -> T ! {})`: its terms are read where
                    // it is written, its effect is the library's, by its
                    // full name.
                    super::Name::Written(w)
                        if crate::bindings::library_effect(w.head()).is_some() =>
                    {
                        super::Name::Written(std::sync::Arc::new(w.edited(
                            |head| {
                                *head = format!(
                                    "{}{}{head}",
                                    super::qualify::PRELUDE_MODULE,
                                    super::qualify::SEPARATOR
                                )
                            },
                            |_| {},
                        )))
                    }
                    _ => m
                        .spelling()
                        .and_then(crate::bindings::library_effect)
                        .map(|r| super::Name::Global(r.clone()))
                        .unwrap_or_else(|| m.clone()),
                })
                .collect();
            (n.clone(), members)
        })
        .collect();
    outer.extend(written_out(&sets, &outer, &mut errors));
    drop_sets(stmts);
    if outer.is_empty() {
        return errors;
    }
    let resolved: HashMap<String, Vec<super::Name>> = outer
        .iter()
        .map(|(name, effects)| {
            let effects = effects
                .iter()
                .map(|effect| {
                    let mut effect = effect.clone();
                    resolve(&mut effect);
                    effect
                })
                .collect();
            (name.clone(), effects)
        })
        .collect();
    // A set of the prelude written by its full name (`std::builtin::os::Host`,
    // `std::prelude::Host`) is that set: the module says which declaration,
    // and only the file of the prelude that declares it gives it that name.
    let mut resolved = resolved;
    let mut outer = outer;
    let named: Vec<String> = prelude
        .keys()
        .filter(|n| outer.contains_key(*n) && !sets.contains_key(*n))
        .cloned()
        .collect();
    for name in &named {
        let mut fulls = vec![format!("{}{}{name}", super::qualify::PRELUDE_MODULE, super::qualify::SEPARATOR)];
        for map in [super::qualify::hidden_prelude(), super::qualify::core_prelude()] {
            for key in [name.clone(), format!("!{name}")] {
                for file in map.get(&key).into_iter().flatten() {
                    fulls.push(format!(
                        "{}{}{name}",
                        super::qualify::prelude_file_module(file),
                        super::qualify::SEPARATOR
                    ));
                }
            }
        }
        for full in fulls {
            let members = resolved[name].clone();
            resolved.insert(full.clone(), members);
            let members = outer[name].clone();
            outer.insert(full, members);
        }
    }
    // A bound reads a member written for every instance (`∀ T. spawn(T)`)
    // as the effect a row names once its instances are read (`spawn`).
    let bounds: HashMap<String, Vec<super::Name>> = outer
        .iter()
        .map(|(name, effects)| {
            let effects = effects
                .iter()
                .map(|effect| {
                    let mut effect = forall_head(effect);
                    resolve(&mut effect);
                    effect
                })
                .collect();
            (name.clone(), effects)
        })
        .collect();
    for s in stmts.iter_mut() {
        rows_of_stmt(
            s,
            &mut |row| write_row(row, &resolved),
            &mut |written| fill_written_members(written, &resolved),
            &mut |bound| {
                let name = bound.as_ref().to_string();
                if let Some(effects) = outer.get(&name) {
                    bound.edit_spelling(&mut |written| *written = bound_of_set(&name, effects));
                    if let Some(members) = bound.effects_mut() {
                        *members = bounds[&name].clone();
                    }
                }
            },
        );
    }
    errors
}

/// Record which effects a written set name expands to, for unused-effect checks.
fn fill_written_members(
    written: &mut [super::program::WrittenRowEffect],
    sets: &HashMap<String, Vec<super::Name>>,
) {
    for entry in written {
        if entry.members.is_some() {
            continue;
        }
        if let Some(name) = entry.name.spelling()
            && let Some(effects) = sets.get(name)
        {
            entry.members = Some(effects.clone());
        }
    }
}

/// `spawn` for `∀ T. spawn(T)`; any other member as written.
fn forall_head(effect: &super::Name) -> super::Name {
    match effect {
        super::Name::Written(w) if w.is_universal() => super::Name::from(w.head()),
        _ => effect.clone(),
    }
}

/// A set with type parameters (`effect State(T: Type) { Get(T), Put(T) }`) would
/// need its arguments put in its effects; it is not read yet.
fn generic_sets(stmts: &[Stmt], errors: &mut Vec<(Message, Span)>) {
    for s in stmts {
        match s {
            Stmt::Effect(e) if e.set.is_some() && !e.generics.is_empty() => errors.push((
                msg!("surface-effect-set-generic", name = e.name.as_str()),
                e.span,
            )),
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => generic_sets(items, errors),
            _ => {}
        }
    }
}

/// The effects `stmts` declares that are not sets: a set of the same name
/// in the prelude does not reach them.
fn effects_declared(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        match s {
            Stmt::Effect(e) if e.set.is_none() => {
                out.insert(e.name.to_string());
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => effects_declared(items, out),
            _ => {}
        }
    }
}

/// Each of `sets` written out to effects, through the sets it names and
/// those of `outer`. A set that names itself, through others or not, is an
/// error, and so is one with type parameters.
fn written_out(
    sets: &Sets,
    outer: &HashMap<String, Vec<super::Name>>,
    errors: &mut Vec<(Message, Span)>,
) -> HashMap<String, Vec<super::Name>> {
    fn go(
        name: &str,
        sets: &Sets,
        outer: &HashMap<String, Vec<super::Name>>,
        done: &mut HashMap<String, Vec<super::Name>>,
        on: &mut Vec<String>,
        errors: &mut Vec<(Message, Span)>,
    ) -> Vec<super::Name> {
        if let Some(d) = done.get(name) {
            return d.clone();
        }
        let Some((members, span)) = sets.get(name) else {
            return outer
                .get(name)
                .cloned()
                .unwrap_or_else(|| vec![super::Name::from(name)]);
        };
        if on.iter().any(|n| n == name) {
            errors.push((
                msg!(
                    "surface-effect-set-names-itself",
                    name = name,
                    path = on.join(" -> ")
                ),
                *span,
            ));
            return Vec::new();
        }
        on.push(name.to_string());
        let mut out = Vec::new();
        for m in members {
            let set = m
                .spelling()
                .filter(|m| sets.contains_key(*m) || outer.contains_key(*m));
            let effects = if let Some(m) = set {
                go(m, sets, outer, done, on, errors)
            } else {
                vec![m.clone()]
            };
            for e in effects {
                if !out.contains(&e) {
                    out.push(e);
                }
            }
        }
        on.pop();
        done.insert(name.to_string(), out.clone());
        out
    }
    let mut done = HashMap::new();
    let mut names: Vec<&String> = sets.keys().collect();
    names.sort();
    for n in names {
        go(n, sets, outer, &mut done, &mut Vec::new(), errors);
    }
    done
}

fn drop_sets(stmts: &mut Vec<Stmt>) {
    stmts.retain(|s| !matches!(s, Stmt::Effect(e) if e.set.is_some()));
    for s in stmts.iter_mut() {
        if let Stmt::Mutual { items, .. } | Stmt::Module { items, .. } = s {
            drop_sets(items);
        }
    }
}

/// A row with each set's name replaced by its effects, each effect once.
fn write_row(row: &mut Vec<super::Name>, sets: &HashMap<String, Vec<super::Name>>) {
    // An entry with arguments (`∀ T. spawn(() -> T ! {cells})`) writes rows
    // in its terms: a set named there means its effects too.
    for e in row.iter_mut() {
        if let super::Name::Written(w) = e {
            let edited = w.edited(
                |_| {},
                |argument| {
                    walk::term(argument, &mut |t| {
                        match std::sync::Arc::make_mut(&mut t.kind) {
                            TermKind::Pi {
                                effects: Some(row), ..
                            }
                            | TermKind::Row(row) => write_row(row, sets),
                            _ => {}
                        }
                    })
                },
            );
            *e = super::Name::Written(std::sync::Arc::new(edited));
        }
    }
    if !row
        .iter()
        .any(|e| e.spelling().is_some_and(|s| sets.contains_key(s)))
    {
        return;
    }
    let mut out: Vec<super::Name> = Vec::new();
    for e in row.drain(..) {
        match e.spelling().and_then(|s| sets.get(s)) {
            Some(effects) => {
                for e in effects {
                    if !out.contains(e) {
                        out.push(e.clone());
                    }
                }
            }
            None => {
                if !out.contains(&e) {
                    out.push(e);
                }
            }
        }
    }
    // The row variable stays last.
    out.sort_by_key(|e| e.starts_with('|'));
    *row = out;
}

/// `f` on every row `s` writes: a function's effects, and those of each
/// function type and row argument in its terms, in nested statements too.
/// `written` fills set membership on a function's written row entries.
/// `bound` on each bound of a function's generics.
fn rows_of_stmt(
    s: &mut Stmt,
    f: &mut dyn FnMut(&mut Vec<super::Name>),
    written: &mut dyn FnMut(&mut [super::program::WrittenRowEffect]),
    bound: &mut dyn FnMut(&mut super::program::GenericBound),
) {
    fns_of_decl(s, &mut |d| {
        if let Some(row) = &mut d.effects {
            f(row);
        }
        if let Some(entries) = &mut d.written_effects {
            written(entries);
        }
        d.bounds.iter_mut().flatten().for_each(&mut *bound);
    });
    walk::stmt(s, &mut |t| match std::sync::Arc::make_mut(&mut t.kind) {
        TermKind::Pi {
            effects: Some(row), ..
        } => f(row),
        TermKind::Row(row) => f(row),
        TermKind::Block(stmts) => stmts.iter_mut().for_each(|s| {
            fns_of_decl(s, &mut |d| {
                if let Some(row) = &mut d.effects {
                    f(row);
                }
                if let Some(entries) = &mut d.written_effects {
                    written(entries);
                }
                d.bounds.iter_mut().flatten().for_each(&mut *bound);
            })
        }),
        _ => {}
    });
}

/// `f` on each function a declaration holds outside its terms.
fn fns_of_decl(s: &mut Stmt, f: &mut dyn FnMut(&mut FnDecl)) {
    match s {
        Stmt::Fn(d) => f(d),
        Stmt::Class(c) => c.methods.iter_mut().for_each(|d| f(d)),
        Stmt::Instance(i) => i.methods.iter_mut().for_each(|d| f(d)),
        Stmt::Extern { fns, .. } => fns.iter_mut().for_each(|d| f(d)),
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            items.iter_mut().for_each(|i| fns_of_decl(i, f))
        }
        Stmt::Attributed { stmt, .. } => fns_of_decl(stmt, f),
        _ => {}
    }
}

/// A row variable bounded by a set (`<!h: Host>`) stands for some of the set's
/// effects only. The bound is written as the set's name and its effects,
/// `Host{div, stdout}` (a member for every instance by its name, `spawn`), for the row checks (`rows`), which read a bound
/// with `{` in it so.
pub fn bound_of_set(name: &str, effects: &[super::Name]) -> String {
    let effects: Vec<String> = effects.iter().map(|e| forall_head(e).to_string()).collect();
    format!("{name}{{{}}}", effects.join(", "))
}

/// The set's name and its effects, of a bound written by [`bound_of_set`].
pub fn set_of_bound(bound: &str) -> Option<(&str, Vec<String>)> {
    let (name, rest) = bound.split_once('{')?;
    let inner = rest.strip_suffix('}')?;
    let effects = inner
        .split(',')
        .map(str::trim)
        .filter(|e| !e.is_empty())
        .map(str::to_string)
        .collect();
    Some((name, effects))
}
