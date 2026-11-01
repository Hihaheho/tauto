//! `effect Host {Div, stdout}` names a set of effects. A row that writes
//! the name means the effects of the set: this pass writes them in its place,
//! in every row of the program, and drops the declaration. The checkers and
//! the backends see only the effects, so the name adds nothing to what they
//! trust.
//!
//! A program sees the prelude's sets, and its own. Its own declaration of an
//! effect hides the prelude's set of that name.

use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

use tauto_message::msg;
use tauto_parol::Span;

use super::program::{FnDecl, Stmt};
use super::{TermKind, walk};

/// Each set, by its name: the effects as written.
pub type Sets = HashMap<String, (Vec<String>, Span)>;

/// The prelude's sets, each written out to effects only.
pub fn prelude_sets() -> &'static HashMap<String, Vec<String>> {
    static SETS: OnceLock<HashMap<String, Vec<String>>> = OnceLock::new();
    SETS.get_or_init(|| {
        let Ok(program) = super::program::parse_program_unresolved_at(crate::nibstd::PRELUDE, 0)
        else {
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
                    out.insert(e.name.clone(), (set.clone(), e.span));
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
pub fn expand(stmts: &mut Vec<Stmt>, others: &Sets) -> Vec<(String, Span)> {
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
    let mut outer: HashMap<String, Vec<String>> = prelude
        .iter()
        .filter(|(n, _)| !declared.contains(*n) && !sets.contains_key(*n))
        .map(|(n, s)| (n.clone(), s.clone()))
        .collect();
    outer.extend(written_out(&sets, &outer, &mut errors));
    drop_sets(stmts);
    if outer.is_empty() {
        return errors;
    }
    for s in stmts.iter_mut() {
        rows_of_stmt(s, &mut |row| write_row(row, &outer), &mut |b| {
            if let Some(effects) = outer.get(b.as_str()) {
                *b = bound_of_set(b, effects);
            }
        });
    }
    errors
}

/// A set with type parameters (`effect State(T: Type) { Get(T), Put(T) }`) would
/// need its arguments put in its effects; it is not read yet.
fn generic_sets(stmts: &[Stmt], errors: &mut Vec<(String, Span)>) {
    for s in stmts {
        match s {
            Stmt::Effect(e) if e.set.is_some() && !e.generics.is_empty() => errors.push((
                msg!("surface-effect-set-generic", name = &e.name).to_string(),
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
                out.insert(e.name.clone());
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
    outer: &HashMap<String, Vec<String>>,
    errors: &mut Vec<(String, Span)>,
) -> HashMap<String, Vec<String>> {
    fn go(
        name: &str,
        sets: &Sets,
        outer: &HashMap<String, Vec<String>>,
        done: &mut HashMap<String, Vec<String>>,
        on: &mut Vec<String>,
        errors: &mut Vec<(String, Span)>,
    ) -> Vec<String> {
        if let Some(d) = done.get(name) {
            return d.clone();
        }
        let Some((members, span)) = sets.get(name) else {
            return outer
                .get(name)
                .cloned()
                .unwrap_or_else(|| vec![name.to_string()]);
        };
        if on.iter().any(|n| n == name) {
            errors.push((
                msg!(
                    "surface-effect-set-names-itself",
                    name = name,
                    path = on.join(" -> ")
                )
                .to_string(),
                *span,
            ));
            return Vec::new();
        }
        on.push(name.to_string());
        let mut out = Vec::new();
        for m in members {
            let effects = if sets.contains_key(m.as_str()) || outer.contains_key(m.as_str()) {
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
fn write_row(row: &mut Vec<String>, sets: &HashMap<String, Vec<String>>) {
    if !row.iter().any(|e| sets.contains_key(e.as_str())) {
        return;
    }
    let mut out: Vec<String> = Vec::new();
    for e in row.drain(..) {
        match sets.get(e.as_str()) {
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
/// `bound` on each bound of a function's generics.
fn rows_of_stmt(
    s: &mut Stmt,
    f: &mut dyn FnMut(&mut Vec<String>),
    bound: &mut dyn FnMut(&mut String),
) {
    fns_of_decl(s, &mut |d| {
        if let Some(row) = &mut d.effects {
            f(row);
        }
        d.bounds.iter_mut().flatten().for_each(|b| bound(b));
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
                d.bounds.iter_mut().flatten().for_each(|b| bound(b));
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
/// `Host{Div, stdout}`, for the row checks (`rows`), which read a bound
/// with `{` in it so.
pub fn bound_of_set(name: &str, effects: &[String]) -> String {
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

#[cfg(test)]
mod tests {
    use super::super::program::{Stmt, parse_program_as_written};

    fn read(source: &str) -> (Vec<Stmt>, Vec<String>) {
        tauto_messages::install();
        let program = parse_program_as_written(source).unwrap();
        let errors = program.errors.iter().map(|(m, _)| m.clone()).collect();
        (program.stmts, errors)
    }

    fn row_of(stmts: &[Stmt], name: &str) -> Vec<String> {
        stmts
            .iter()
            .find_map(|s| match s {
                Stmt::Fn(f) if f.name == name => f.effects.clone(),
                _ => None,
            })
            .unwrap()
    }

    #[test]
    fn a_set_is_written_out_once_in_each_row_and_dropped() {
        let (stmts, errors) = read(
            "effect log(m: Text): () resume 1\neffect Inner {log}\neffect Talk {Inner, stdout}\nfn f(): () ! {Talk, log} ∪ e { () }",
        );
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(row_of(&stmts, "f"), ["log", "stdout", "|e"]);
        assert!(
            !stmts
                .iter()
                .any(|s| matches!(s, Stmt::Effect(e) if e.set.is_some()))
        );
    }

    #[test]
    fn the_prelude_set_host_is_seen_and_bounds_a_row_variable() {
        let (stmts, errors) = read("fn f<!h: Host>(): () ! {Host} { () }");
        assert!(errors.is_empty(), "{errors:?}");
        assert!(row_of(&stmts, "f").contains(&"net".to_string()));
        let Some(Stmt::Fn(f)) = stmts.iter().find(|s| matches!(s, Stmt::Fn(_))) else {
            unreachable!()
        };
        let bound = f.bounds[0].as_deref().unwrap();
        let (name, set) = super::set_of_bound(bound).unwrap();
        assert_eq!(name, "Host");
        assert!(set.contains(&"stdout".to_string()));
    }

    #[test]
    fn a_set_that_names_itself_is_an_error() {
        let (_, errors) = read("effect A1 {B1}\neffect B1 {A1}");
        assert!(
            errors
                .iter()
                .any(|e| e == "the effect set A1 names itself: A1 -> B1 -> A1"),
            "{errors:?}"
        );
    }

    #[test]
    fn a_set_with_type_parameters_is_an_error() {
        let (_, errors) = read("effect S(T: Type) { stdout }");
        assert!(
            errors.iter().any(|e| e.contains("has type parameters")),
            "{errors:?}"
        );
    }

    #[test]
    fn an_own_effect_hides_the_prelude_set() {
        let (stmts, _) = read(
            "effect Host(): i64 resume 1
fn f(): i64 ! {Host} { perform Host() }",
        );
        assert_eq!(row_of(&stmts, "f"), ["Host"]);
    }
}
