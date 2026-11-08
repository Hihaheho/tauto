//! Effects indexed by type: a row that writes an effect with type arguments
//! (`! {res(Pos), res(Vel)}`) names two effects, `res(Pos)` and `res(Vel)`.
//!
//! The expansion gives each instance a name of its own (`res@Pos`, which no
//! program can write) and a declaration without generics, and renames each
//! `perform` and arm of the effect after the type arguments it was checked
//! with. A function whose own generic is such an argument (`res(C)`) is
//! copied for each type a call gives it. What follows sees ordinary effects,
//! matched by name, and checks the result as it checks any program: no rule
//! is added to the checkers, the kernel or a backend.

use crate::surface::Name;
use std::collections::{HashMap, HashSet};

use super::{
    ROW_TAIL, ROW_TYPE, Ty, TypeReport, check_program_in, prelude, prelude_for, prelude_report_for,
};
use crate::surface::walk;
use crate::surface::{EffectDecl, FnDecl, Handler, Program, Stmt, SurfaceTerm, TermKind};
use tauto_parol::Span;

/// Effects the host answers by their names; they are never indexed.
const HOST: &[&str] = &["show", "exceeded"];

/// The declaration and arguments of an indexed row entry.
pub(super) fn application(entry: &Name) -> Option<(Name, Vec<SurfaceTerm>)> {
    match entry {
        Name::Effect(effect) if !effect.is_universal() => {
            Some((effect.effect().clone().into(), effect.arguments().to_vec()))
        }
        Name::Spelled(text) => {
            if text.starts_with(['|', '?', '∀']) || text.contains('@') {
                return None;
            }
            let (head, arguments) = text.split_once('(')?;
            let arguments = split_top(arguments.strip_suffix(')')?)
                .into_iter()
                .map(|arg| parse_argument(arg, Span::new(0, 0)))
                .collect::<Option<Vec<_>>>()?;
            Some((Name::from(head.trim()), arguments))
        }
        _ => None,
    }
}

/// The instance a row entry of a data declaration (`res(A)`) names once the data's generics
/// are known. The expansion copies functions, not data, so the field's row still writes `A`.
pub(crate) fn instance_of_entry(entry: &Name, map: &HashMap<Name, SurfaceTerm>) -> Option<Name> {
    let (head, mut arguments) = application(entry)?;
    if host(&head)
        || argument_names(&arguments)
            .iter()
            .all(|n| !map.contains_key(n))
    {
        return None;
    }
    for argument in &mut arguments {
        replace_vars(argument, map);
    }
    Some(specialize(&head, &arguments))
}

/// Whether a function type in `ty` writes an effect with type arguments.
pub(crate) fn writes_indexed_row(ty: &SurfaceTerm) -> bool {
    let mut found = false;
    let mut ty = ty.clone();
    walk::term(&mut ty, &mut |t| {
        if let TermKind::Pi {
            effects: Some(row), ..
        } = &*t.kind
            && row.iter().any(|entry| application(entry).is_some())
        {
            found = true;
        }
    });
    found
}

/// A checked type as the term that writes it.
pub(crate) fn type_term(ty: &Ty, span: Span) -> Option<SurfaceTerm> {
    surface_of(ty, span)
}

fn host(effect: &Name) -> bool {
    HOST.iter()
        .any(|name| effect == &tauto_surface::bindings::library_name(name))
        || matches!(effect, Name::Spelled(text) if HOST.contains(&text.as_str()))
}

fn argument_names(arguments: &[SurfaceTerm]) -> HashSet<Name> {
    let mut found = HashSet::new();
    for argument in arguments {
        walk::term(&mut argument.clone(), &mut |term| {
            if let TermKind::Var(name) = &*term.kind {
                found.insert(name.clone());
            }
        });
    }
    found
}

/// Every row of the statement: the written rows of its functions (local ones
/// too) and of the function types in it.
fn rows_mut(s: &mut Stmt, f: &mut dyn FnMut(&mut Vec<Name>)) {
    fn fn_rows(d: &mut FnDecl, f: &mut dyn FnMut(&mut Vec<Name>)) {
        if let Some(row) = &mut d.effects {
            f(row);
        }
    }
    fn stmt_rows(s: &mut Stmt, f: &mut dyn FnMut(&mut Vec<Name>)) {
        match s {
            Stmt::Fn(d) => fn_rows(d, f),
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                items.iter_mut().for_each(|i| stmt_rows(i, f))
            }
            Stmt::Attributed { stmt, .. } => stmt_rows(stmt, f),
            Stmt::Extern { fns, .. } => fns.iter_mut().for_each(|d| fn_rows(d, f)),
            _ => {}
        }
    }
    stmt_rows(s, f);
    walk::stmt(s, &mut |t| match std::sync::Arc::make_mut(&mut t.kind) {
        TermKind::Pi {
            effects: Some(row), ..
        } => f(row),
        TermKind::Block(stmts) => stmts.iter_mut().for_each(|s| stmt_rows(s, f)),
        _ => {}
    });
}

/// The effects some row of the program writes with type arguments, or an
/// arm answers one instance of (`res<Pos>()`).
pub(super) fn indexed_effects(program: &Program) -> HashSet<Name> {
    let mut found = HashSet::new();
    for s in &program.stmts {
        let mut s = s.clone();
        rows_mut(&mut s, &mut |row| {
            for entry in row.iter() {
                if let Some((head, _)) = application(entry)
                    && !host(&head)
                {
                    found.insert(head);
                }
            }
        });
        walk::stmt(&mut s, &mut |t| {
            if let TermKind::Handle { handlers, .. } = &*t.kind {
                for h in handlers {
                    if let Handler::Operation {
                        effect, instance, ..
                    } = h
                        && instance.forall.is_empty()
                        && !instance.args.is_empty()
                        && !host(effect)
                    {
                        found.insert(effect.clone());
                    }
                }
            }
        });
    }
    found
}

/// The generics of each operation that its values mention, by the
/// operation's name: what a row entry and an arm write the instance with. A
/// row's generic (`test<e>`) is not one.
fn typed_generics(programs: &[&Program]) -> HashMap<Name, Vec<Name>> {
    fn mentions(t: &SurfaceTerm, name: &Name) -> bool {
        let mut found = false;
        let mut t = t.clone();
        walk::term(&mut t, &mut |x| {
            if matches!(&*x.kind, TermKind::Var(v) if v == name) {
                found = true;
            }
        });
        found
    }
    fn collect(stmts: &[Stmt], out: &mut HashMap<Name, Vec<Name>>) {
        for s in stmts {
            match s {
                Stmt::Effect(e) => {
                    let typed = e
                        .generics
                        .iter()
                        .filter(|g| {
                            e.params
                                .iter()
                                .flatten()
                                .chain(&e.result)
                                .any(|t| mentions(t, g))
                        })
                        .cloned()
                        .collect();
                    out.insert(e.name.clone(), typed);
                }
                Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => collect(items, out),
                Stmt::Attributed { stmt, .. } => collect(std::slice::from_ref(stmt), out),
                _ => {}
            }
        }
    }
    // The host declares `show<A>: (name: Text, value: A) -> ()`.
    let mut out = HashMap::from([
        (Name::from("show"), vec![Name::from("A")]),
        (
            tauto_surface::bindings::library_name("show"),
            vec![Name::from("A")],
        ),
    ]);
    for p in programs {
        collect(&p.stmts, &mut out);
    }
    out
}

/// Whether `program`, which writes no indexed effect of its own, could still
/// meet one of the prelude's: it performs or handles an effect, or names a
/// prelude function that does, or one that calls such a function. One that
/// cannot is left as it is without being checked, which is most of the cost
/// of loading a small program.
fn touches_indexed(program: &Program) -> bool {
    let touched = prelude_touched(program);
    program.stmts.iter().any(|s| {
        let mut s = s.clone();
        let mut found = false;
        walk::stmt(&mut s, &mut |t| match &*t.kind {
            TermKind::Perform { .. } | TermKind::Handle { .. } => found = true,
            TermKind::Var(n) if touched.contains(n) => found = true,
            _ => {}
        });
        found
    })
}

/// The prelude's functions that perform, handle or write in a row one of its
/// indexed effects, the effects themselves, and the functions that call any
/// of these.
fn prelude_touched(program: &Program) -> &'static HashSet<Name> {
    static SOURCE: std::sync::OnceLock<HashSet<Name>> = std::sync::OnceLock::new();
    static RESOLVED: std::sync::OnceLock<HashSet<Name>> = std::sync::OnceLock::new();
    let library = prelude_for(program);
    let cache = if std::ptr::eq(library, prelude()) {
        &SOURCE
    } else {
        &RESOLVED
    };
    cache.get_or_init(|| {
        let indexed = indexed_effects(library);
        let mut touched: HashSet<Name> = indexed.clone();
        let mut fns: Vec<(Name, Stmt)> = Vec::new();
        fn collect(stmts: &[Stmt], out: &mut Vec<(Name, Stmt)>) {
            for s in stmts {
                match s {
                    Stmt::Fn(f) => out.push((f.name.clone(), s.clone())),
                    Stmt::Extern { fns, .. } => {
                        out.extend(fns.iter().map(|f| (f.name.clone(), Stmt::Fn(f.clone()))))
                    }
                    Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => collect(items, out),
                    Stmt::Attributed { stmt, .. } => collect(std::slice::from_ref(stmt), out),
                    _ => {}
                }
            }
        }
        collect(&library.stmts, &mut fns);
        loop {
            let mut changed = false;
            for (name, s) in &fns {
                if touched.contains(name) {
                    continue;
                }
                let mut s = s.clone();
                let mut found = false;
                rows_mut(&mut s, &mut |row| {
                    if row.iter().any(|e| {
                        application(e).is_some_and(|(head, _)| indexed.contains(&head))
                            || indexed.contains(e)
                    }) {
                        found = true;
                    }
                });
                walk::stmt(&mut s, &mut |t| match &*t.kind {
                    TermKind::Perform { .. } | TermKind::Handle { .. } => found = true,
                    TermKind::Var(n) if touched.contains(n) => found = true,
                    _ => {}
                });
                if found {
                    touched.insert(name.clone());
                    changed = true;
                }
            }
            if !changed {
                return touched;
            }
        }
    })
}

/// Reads the rows as the checks after it do: `∀ A. res(A)`, every instance
/// of `res`, becomes the bare `res` they read so, and a bare entry of an
/// operation with type arguments is an error, since it does not say which
/// instance it means.
pub(super) fn every_instance(program: &mut Program, per_file: &mut [Vec<Stmt>], is_prelude: bool) {
    let generics = if is_prelude {
        typed_generics(&[program])
    } else {
        typed_generics(&[prelude_for(program), program])
    };
    let mut errors = Vec::new();
    for s in &mut program.stmts {
        let span = stmt_span(s).unwrap_or(Span::new(0, 0));
        rows_mut(s, &mut |row| {
            for entry in row.iter_mut() {
                if let Err(why) = read_entry(entry, &generics) {
                    errors.push((why, span));
                }
            }
        });
    }
    for file in per_file.iter_mut() {
        for s in file.iter_mut() {
            rows_mut(s, &mut |row| {
                for entry in row.iter_mut() {
                    let _ = read_entry(entry, &generics);
                }
            });
        }
    }
    program.errors.extend(
        errors
            .into_iter()
            .map(|(t, s): (String, Span)| (t.into(), s)),
    );
}

/// One entry of [`every_instance`].
fn read_entry(entry: &mut Name, generics: &HashMap<Name, Vec<Name>>) -> Result<(), String> {
    if let Name::Effect(effect) = entry {
        if !effect.is_universal() {
            return Ok(());
        }
        let head: Name = effect.effect().clone().into();
        let typed = generics.get(&head).map(Vec::as_slice).unwrap_or_default();
        let names = effect.parameters();
        let distinct = names.iter().collect::<HashSet<_>>().len() == names.len();
        let ordered = names.len() == effect.arguments().len() && names.iter().zip(effect.arguments())
            .all(|(name, argument)| matches!(&*argument.kind, TermKind::Var(reference) if reference.as_local() == Some(name)));
        if typed.is_empty() || !distinct || !ordered || names.len() != typed.len() {
            let want = typed
                .iter()
                .map(Name::as_str)
                .collect::<Vec<_>>()
                .join(", ");
            return Err(format!(
                "`{entry}`: every instance of `{head}` binds each type argument in order: `∀ {want}. {head}({want})`"
            ));
        }
        *entry = head;
        return Ok(());
    }
    if let Name::Spelled(text) = &*entry
        && let Some(rest) = text.strip_prefix('∀')
    {
        let Some((names, written)) = rest.split_once('.') else {
            return Err(format!("`{entry}`: write `∀ A. res(A)`"));
        };
        let names: Vec<&str> = names.split(',').map(str::trim).collect();
        let written = written.trim();
        let (head, args) = match written.split_once('(') {
            Some((head, args)) => (head.trim(), args.strip_suffix(')').unwrap_or(args)),
            None => (written, ""),
        };
        let args: Vec<&str> = split_top(args).into_iter().map(str::trim).collect();
        let typed = generics
            .get(&Name::from(head))
            .map(Vec::as_slice)
            .unwrap_or_default();
        let distinct = names.iter().collect::<HashSet<_>>().len() == names.len();
        if typed.is_empty() || !distinct || names != args || args.len() != typed.len() {
            let want = typed
                .iter()
                .map(Name::as_str)
                .collect::<Vec<_>>()
                .join(", ");
            return Err(format!(
                "`{entry}`: every instance of `{head}` binds each type argument in order: `∀ {want}. {head}({want})`"
            ));
        }
        *entry = Name::from(head);
        return Ok(());
    }
    if entry.starts_with(['|', '?']) || entry.contains(['(', '@']) {
        return Ok(());
    }
    match generics.get(entry) {
        Some(typed) if !typed.is_empty() => {
            let want = typed
                .iter()
                .map(Name::as_str)
                .collect::<Vec<_>>()
                .join(", ");
            // A host operation is never read by instance, so the only row
            // that names it is the one for every instance.
            if host(entry) {
                return Err(format!(
                    "write `∀ {want}. {entry}({want})`: a row names every instance of the host's `{entry}`"
                ));
            }
            Err(format!(
                "write the instance of `{entry}` the row means: `{entry}(…)`, or `∀ {want}. {entry}({want})` for every one"
            ))
        }
        _ => Ok(()),
    }
}

/// For each top-level function, its generics that a row it writes uses as
/// an index (`catch`'s `E`): the expansion, not the types, determines them.
pub(super) fn index_generics(program: &Program) -> HashMap<Name, HashSet<Name>> {
    let indexed = indexed_effects(program);
    let mut out = HashMap::new();
    for (name, f) in functions(&program.stmts) {
        let mut found = HashSet::new();
        let mut s = Stmt::Fn(f.clone());
        rows_mut(&mut s, &mut |row| {
            for entry in row.iter() {
                if let Some((head, arguments)) = application(entry)
                    && indexed.contains(&head)
                {
                    found.extend(
                        argument_names(&arguments)
                            .into_iter()
                            .filter(|name| f.generics.contains(name)),
                    );
                }
            }
        });
        if !found.is_empty() {
            out.insert(name, found);
        }
    }
    out
}

fn surface_of(t: &Ty, span: Span) -> Option<SurfaceTerm> {
    match t {
        Ty::Int(_) | Ty::Bool | Ty::Text | Ty::Decimal | Ty::Float | Ty::Float32 => Some(
            SurfaceTerm::var(&tauto_surface::bindings::library_name(&t.to_string()), span),
        ),
        Ty::Named(n, args) if args.is_empty() => Some(SurfaceTerm::var(n, span)),
        Ty::Named(n, args) => {
            let args = args
                .iter()
                .map(|a| surface_of(a, span))
                .collect::<Option<Vec<_>>>()?;
            Some(SurfaceTerm::app(n, args, span))
        }
        _ => None,
    }
}

fn parse_argument(text: &str, span: Span) -> Option<SurfaceTerm> {
    let text = text.trim();
    // A name may be a path: the checker writes a type of a module as
    // `main.IoError`.
    let ident = |s: &str| {
        !s.is_empty()
            && s.chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == ':' || c == '.')
    };
    match text.split_once('(') {
        None if ident(text) => Some(SurfaceTerm::var(text, span)),
        Some((head, rest)) if ident(head.trim()) => {
            let inner = rest.strip_suffix(')')?;
            let args = split_top(inner)
                .into_iter()
                .map(|a| parse_argument(a, span))
                .collect::<Option<Vec<_>>>()?;
            Some(SurfaceTerm::app(head.trim(), args, span))
        }
        _ => None,
    }
}

/// `a, f(b, c)` → `a`, `f(b, c)`.
fn split_top(text: &str) -> Vec<&str> {
    let (mut depth, mut start, mut parts) = (0usize, 0usize, Vec::new());
    for (i, c) in text.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                parts.push(&text[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    if !text[start..].trim().is_empty() {
        parts.push(&text[start..]);
    }
    parts
}

/// Whether `t` holds a type variable that has a solution.
fn mentions_solved(t: &Ty, solved: &HashMap<usize, SurfaceTerm>) -> bool {
    match t {
        Ty::Var(n) => solved.contains_key(n),
        Ty::Named(_, ts) | Ty::Union(ts) => ts.iter().any(|t| mentions_solved(t, solved)),
        Ty::Fn(ps, r, _) => {
            ps.iter().any(|t| mentions_solved(t, solved)) || mentions_solved(r, solved)
        }
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Poly(_, t) => {
            mentions_solved(t, solved)
        }
        Ty::App(h, x) => mentions_solved(h, solved) || mentions_solved(x, solved),
        _ => false,
    }
}

/// A type argument as text, the same for a written one and an inferred one.
fn print(t: &SurfaceTerm) -> String {
    match &*t.kind {
        TermKind::Var(n) => n.to_string(),
        TermKind::App {
            function,
            arguments,
        } => {
            let args: Vec<String> = arguments.iter().map(print).collect();
            format!("{}({})", print(function), args.join(","))
        }
        TermKind::Row(names) => {
            let names: Vec<String> = names.iter().map(|n| n.to_string()).collect();
            format!("!{{{}}}", names.join(","))
        }
        _ => "?".into(),
    }
}

fn label(effect: &str, args: &[SurfaceTerm]) -> String {
    let args: Vec<String> = args.iter().map(print).collect();
    format!("{effect}@{}", args.join(","))
}

fn specialize(owner: &Name, arguments: &[SurfaceTerm]) -> Name {
    match owner {
        Name::Global(reference) => reference
            .specialize(
                &tauto_surface::bindings::argument_key(arguments),
                label(owner, arguments),
            )
            .into(),
        Name::Spelled(_) => Name::from(label(owner, arguments)),
        _ => panic!("only a declaration can be specialized"),
    }
}

/// `t` with each name in `map` replaced, where it stands as a term.
fn replace_vars(t: &mut SurfaceTerm, map: &HashMap<Name, SurfaceTerm>) {
    walk::term(t, &mut |x| {
        if let TermKind::Var(n) = &*x.kind
            && let Some(r) = map.get(n)
        {
            *x = x.with_kind((*r.kind).clone(), x.span);
        }
    });
}

/// Every term of the statement made a distinct occurrence.
fn freshen(s: &mut Stmt) {
    walk::stmt(s, &mut |t| t.freshen());
}

/// The generic names a type mentions.
fn params_in(t: &Ty, out: &mut HashSet<Name>) {
    match t {
        Ty::Param(p, _) => {
            out.insert(p.name.clone());
        }
        Ty::Fn(ps, r, _) => {
            ps.iter().for_each(|p| params_in(p, out));
            params_in(r, out);
        }
        Ty::Union(ts) | Ty::Named(_, ts) => ts.iter().for_each(|t| params_in(t, out)),
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Poly(_, t) => params_in(t, out),
        Ty::App(h, x) => {
            params_in(h, out);
            params_in(x, out);
        }
        _ => {}
    }
}

/// The top-level functions, by name.
fn functions(stmts: &[Stmt]) -> HashMap<Name, FnDecl> {
    let mut out = HashMap::new();
    for s in stmts {
        match s {
            Stmt::Fn(f) => {
                out.insert(f.name.clone(), f.clone());
            }
            Stmt::Mutual { items, .. } => out.extend(functions(items)),
            _ => {}
        }
    }
    out
}

/// `program` with its indexed effects expanded (see the module's comment).
/// A program that does not check is left as it is, for the checker to report
/// on; what the expansion cannot do is added to its errors.
///
/// `is_prelude` says that `program` is the prelude itself: it is expanded as
/// a program of its own, checked against itself; it keeps the functions it
/// copies, which a program's calls copy into the program.
pub fn expand_indices(program: &mut Program, per_file: &mut [Vec<Stmt>], is_prelude: bool) {
    every_instance(program, per_file, is_prelude);
    let mut indexed = indexed_effects(program);
    if !is_prelude {
        if indexed.is_empty() && !touches_indexed(program) {
            return;
        }
        indexed.extend(indexed_effects(prelude_for(program)));
    }
    if indexed.is_empty() {
        return;
    }
    let report = if is_prelude {
        check_program_in(program, program)
    } else {
        check_program_in(program, prelude_for(program))
    };
    if !report.errors.is_empty() {
        return;
    }
    let mut x = Expander::new(program, &report, indexed, is_prelude);
    if !is_prelude && x.row_indexed() {
        x.rows = Some(super::check_program_rows_as_types(
            program,
            prelude_for(program),
        ));
    }
    x.relevance();
    let mut errors = Vec::new();
    program.stmts = x.stmts(std::mem::take(&mut program.stmts), &mut errors);
    for file in per_file.iter_mut() {
        *file = x.stmts(std::mem::take(file), &mut Vec::new());
    }
    // The copies, after the function they copy, and the instances of the
    // effects, after the effect (the prelude's: first).
    while let Some((name, from)) = x.queue.pop() {
        if x.made.contains_key(&name) {
            continue;
        }
        if x.made.len() > 4096 {
            errors.push((
                format!("`{}` is copied for too many indices", from.0),
                Span::new(0, 0),
            ));
            break;
        }
        let made = x.instance(&name, &from, &mut errors);
        x.made.insert(name, made);
    }
    let made: Vec<(Name, Stmt)> = x
        .made
        .iter()
        .map(|(n, s)| (x.copies[n].clone(), s.clone()))
        .collect();
    let decls: Vec<(Name, Stmt)> = x.labels.values().cloned().collect();
    place(&mut program.stmts, &made, &decls, true);
    let mut first = true;
    for file in per_file.iter_mut() {
        place(file, &made, &decls, first);
        first = false;
    }
    program.errors.extend(
        errors
            .into_iter()
            .map(|(t, s): (String, Span)| (t.into(), s)),
    );
}

/// Puts each statement after the declaration it was made from, or first when
/// that is not here and `first`.
fn place(stmts: &mut Vec<Stmt>, made: &[(Name, Stmt)], decls: &[(Name, Stmt)], first: bool) {
    let mut sorted: Vec<&(Name, Stmt)> = decls.iter().chain(made).collect();
    sorted.sort_by(|a, b| stmt_name(&a.1).cmp(&stmt_name(&b.1)));
    let mut front = Vec::new();
    for (from, stmt) in sorted {
        let at = stmts.iter().position(|s| match s {
            Stmt::Fn(f) => &f.name == from,
            Stmt::Effect(e) => &e.name == from,
            _ => false,
        });
        match at {
            Some(i) => stmts.insert(i + 1, stmt.clone()),
            None if first => front.push(stmt.clone()),
            None => {}
        }
    }
    front.append(stmts);
    *stmts = front;
}

fn stmt_span(s: &Stmt) -> Option<Span> {
    match s {
        Stmt::Fn(f) => Some(f.span),
        Stmt::Effect(e) => Some(e.span),
        Stmt::Struct(d) | Stmt::Enum(d) => Some(d.span),
        _ => None,
    }
}

fn stmt_name(s: &Stmt) -> Option<&Name> {
    match s {
        Stmt::Fn(f) => Some(&f.name),
        Stmt::Effect(e) => Some(&e.name),
        _ => None,
    }
}

struct Expander<'a> {
    report: &'a TypeReport,
    /// The same check reading rows as types: where a row is an index.
    rows: Option<TypeReport>,
    /// The prelude's, for a program's copies of its functions.
    prelude: Option<&'static TypeReport>,
    is_prelude: bool,
    /// The functions the prelude has, its copies too.
    in_prelude: HashSet<Name>,
    indexed: HashSet<Name>,
    fns: HashMap<Name, FnDecl>,
    effects: HashMap<Name, EffectDecl>,
    /// For each function, its generics that are effect indices.
    relevant: HashMap<Name, Vec<Name>>,
    /// The copies to make: name, and the function and arguments.
    queue: Vec<(Name, (Name, Vec<SurfaceTerm>))>,
    made: HashMap<Name, Stmt>,
    /// Each copy's original.
    copies: HashMap<Name, Name>,
    /// Each effect instance: its original and its declaration.
    labels: HashMap<Name, (Name, Stmt)>,
    /// Each instance's label by the effect and the arguments it names.
    structured: HashMap<Name, (Name, Vec<SurfaceTerm>)>,
    /// The data declarations, whose fields' types say what surrounds a lambda in one.
    datas: HashMap<Name, crate::surface::DataDecl>,
    /// The row a lambda stands in where a written type puts it: the annotation of a `let` it
    /// is bound by, or the result type of the function it is returned from.
    lambda_rows: HashMap<crate::surface::TermId, Around>,
    /// The written types of the parameters of the function being rewritten.
    env: HashMap<Name, SurfaceTerm>,
    /// The type variables of the check that an index decided, in the function
    /// being rewritten: what an unannotated `let` of them is annotated with.
    var_solutions: HashMap<usize, SurfaceTerm>,
    /// The arguments of the `perform`s of the function being rewritten that the
    /// row around them decided.
    performs: HashMap<crate::surface::TermId, Result<Vec<SurfaceTerm>, String>>,
}

/// The instances of indexed effects a row names, with their arguments: what a
/// call's own row is matched against.
type Around = Option<Vec<(Name, Vec<SurfaceTerm>)>>;
type Solved = HashMap<crate::surface::TermId, Result<Vec<SurfaceTerm>, String>>;

impl<'a> Expander<'a> {
    fn new(
        program: &Program,
        report: &'a TypeReport,
        indexed: HashSet<Name>,
        is_prelude: bool,
    ) -> Self {
        let mut effects = HashMap::new();
        let mut fns = HashMap::new();
        let mut in_prelude = HashSet::new();
        if !is_prelude {
            for s in &prelude_for(program).stmts {
                if let Stmt::Effect(e) = s {
                    effects.insert(e.name.clone(), e.clone());
                }
            }
            fns = functions(&prelude_for(program).stmts);
            in_prelude = fns.keys().cloned().collect();
        }
        let mut datas = HashMap::new();
        for s in &program.stmts {
            if let Stmt::Effect(e) = s {
                effects.insert(e.name.clone(), e.clone());
            }
            if let Stmt::Struct(d) = s {
                datas.insert(d.name.clone(), d.clone());
            }
        }
        for (name, f) in functions(&program.stmts) {
            in_prelude.remove(&name);
            fns.insert(name, f);
        }
        Expander {
            report,
            rows: None,
            structured: HashMap::new(),
            datas,
            lambda_rows: HashMap::new(),
            env: HashMap::new(),
            var_solutions: HashMap::new(),
            performs: HashMap::new(),
            prelude: (!is_prelude).then(|| prelude_report_for(program)),
            is_prelude,
            in_prelude,
            indexed,
            fns,
            effects,
            relevant: HashMap::new(),
            queue: Vec::new(),
            made: HashMap::new(),
            copies: HashMap::new(),
            labels: HashMap::new(),
        }
    }

    /// Whether an effect the program writes takes a row as an index.
    fn row_indexed(&self) -> bool {
        self.effects
            .values()
            .any(|e| self.indexed.contains(&e.name) && e.rows.iter().any(|r| *r))
    }

    fn effect_args(&self, id: crate::surface::TermId) -> Option<&Vec<Ty>> {
        self.rows
            .as_ref()
            .and_then(|r| r.effect_args.get(&id))
            .or_else(|| self.report.effect_args.get(&id))
            .or_else(|| self.prelude?.effect_args.get(&id))
    }

    fn instantiation(&self, id: crate::surface::TermId) -> Option<&HashMap<super::ParamId, Ty>> {
        self.rows
            .as_ref()
            .and_then(|r| r.instantiations.get(&id))
            .or_else(|| self.report.instantiations.get(&id))
            .or_else(|| self.prelude?.instantiations.get(&id))
    }

    fn scheme(&self, name: &Name) -> Option<&'a super::Scheme> {
        self.report
            .schemes
            .get(name)
            .or_else(|| self.prelude?.schemes.get(name))
    }

    /// The generics of each function that an index depends on, to a fixpoint
    /// through the calls.
    fn relevance(&mut self) {
        let mut relevant: HashMap<Name, HashSet<Name>> = HashMap::new();
        for (name, f) in &self.fns {
            let generics: HashSet<Name> = f.generics.iter().cloned().collect();
            let mut found = HashSet::new();
            let mut s = Stmt::Fn(f.clone());
            walk::stmt(&mut s, &mut |t| {
                let mut add = |id| {
                    for ty in self.effect_args(id).into_iter().flatten() {
                        params_in(ty, &mut found);
                    }
                };
                match &*t.kind {
                    TermKind::Perform { .. } => add(t.id()),
                    TermKind::Handle { handlers, .. } => {
                        for h in handlers {
                            if let Handler::Operation { body, .. } = h {
                                add(body.id());
                            }
                        }
                    }
                    _ => {}
                }
            });
            rows_mut(&mut s, &mut |row| {
                for entry in row.iter() {
                    if let Some((head, arguments)) = application(entry)
                        && self.indexed.contains(&head)
                    {
                        found.extend(argument_names(&arguments));
                    }
                }
            });
            found.retain(|g| generics.contains(g));
            relevant.insert(name.clone(), found);
        }
        loop {
            let mut changed = false;
            for (name, f) in &self.fns {
                let generics: HashSet<Name> = f.generics.iter().cloned().collect();
                let mut found = HashSet::new();
                let mut s = Stmt::Fn(f.clone());
                walk::stmt(&mut s, &mut |t| {
                    if let TermKind::Var(g) = &*t.kind
                        && let Some(inst) = self.instantiation(t.id())
                        && let Some(scheme) = self.scheme(g)
                    {
                        for (p, _) in &scheme.generics {
                            if relevant.get(g).is_some_and(|r| r.contains(&p.name))
                                && let Some(ty) = inst.get(p.id())
                            {
                                params_in(ty, &mut found);
                            }
                        }
                    }
                });
                let own = relevant.get_mut(name).expect("every function");
                for g in found {
                    if generics.contains(&g) && own.insert(g) {
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for (name, f) in &self.fns {
            let r = &relevant[name];
            let ordered: Vec<Name> = f
                .generics
                .iter()
                .filter(|g| r.contains(*g))
                .cloned()
                .collect();
            if !ordered.is_empty() {
                self.relevant.insert(name.clone(), ordered);
            }
        }
    }

    /// The statements with the expansion done where they stand (with no
    /// generic given), and the functions to be copied left out.
    fn stmts(&mut self, stmts: Vec<Stmt>, errors: &mut Vec<(String, Span)>) -> Vec<Stmt> {
        let mut out = Vec::new();
        for mut s in stmts {
            if let Stmt::Fn(f) = &s
                && self.relevant.contains_key(&f.name)
            {
                if self.is_prelude {
                    out.push(s);
                }
                continue;
            }
            self.rewrite(&mut s, &HashMap::new(), errors);
            out.push(s);
        }
        out
    }

    fn arguments(
        &mut self,
        id: crate::surface::TermId,
        given: &HashMap<Name, SurfaceTerm>,
        span: Span,
    ) -> Result<Vec<SurfaceTerm>, String> {
        let Some(args) = self.effect_args(id).cloned() else {
            return Err("no type was found".into());
        };
        args.iter()
            .map(|t| match t {
                Ty::Param(p, _) => given
                    .get(&p.name)
                    .cloned()
                    .ok_or_else(|| format!("it is the generic `{}`, which is not given", p.name())),
                Ty::Var(_) => Err("its type arguments are not known here; annotate them".into()),
                _ => self
                    .term_of_ty(t, span, given)
                    .ok_or_else(|| format!("`{t}` cannot index an effect")),
            })
            .collect()
    }

    /// A checked type, or a row read as a type, as the term that writes it.
    fn term_of_ty(
        &mut self,
        t: &Ty,
        span: Span,
        given: &HashMap<Name, SurfaceTerm>,
    ) -> Option<SurfaceTerm> {
        match t {
            Ty::Param(p, _) => given.get(&p.name).cloned(),
            Ty::Var(n) => self.var_solutions.get(n).cloned(),
            Ty::Named(n, members) if n.as_str() == ROW_TYPE => {
                let mut names = Vec::new();
                for member in members {
                    match member {
                        Ty::Named(tail, x) if tail.as_str() == ROW_TAIL => {
                            match &*self.term_of_ty(&x[0], span, given)?.kind {
                                TermKind::Row(rest) => names.extend(rest.iter().cloned()),
                                _ => return None,
                            }
                        }
                        Ty::Named(head, args) if args.is_empty() => names.push(head.clone()),
                        Ty::Named(head, args) => {
                            let args = args
                                .iter()
                                .map(|a| self.term_of_ty(a, span, given))
                                .collect::<Option<Vec<_>>>()?;
                            names.push(self.instance_label(head, &args));
                        }
                        _ => return None,
                    }
                }
                names.sort_by_key(|n| n.to_string());
                names.dedup();
                Some(SurfaceTerm::new(TermKind::Row(names), span))
            }
            Ty::Named(n, args) if args.is_empty() => Some(SurfaceTerm::var(n, span)),
            Ty::Named(n, args) => {
                let args = args
                    .iter()
                    .map(|a| self.term_of_ty(a, span, given))
                    .collect::<Option<Vec<_>>>()?;
                Some(SurfaceTerm::app(n, args, span))
            }
            _ => surface_of(t, span),
        }
    }

    /// A written row with the generics in `map` given: a row variable that
    /// stands for a row is spliced in, and an instance of an indexed effect is
    /// named after its arguments. `sorted` makes it a row's one spelling.
    fn canon_row(
        &mut self,
        names: &[Name],
        map: &HashMap<Name, SurfaceTerm>,
        skip: &HashSet<Name>,
        sorted: bool,
    ) -> Vec<Name> {
        let mut out = Vec::new();
        for n in names {
            if let Some(value) = map.get(n)
                && let TermKind::Row(rest) = &*value.kind
            {
                out.extend(rest.iter().cloned());
            } else if let Some((head, mut args)) = application(n)
                && self.indexed.contains(&head)
                && argument_names(&args).iter().all(|n| !skip.contains(n))
            {
                for a in &mut args {
                    replace_vars(a, map);
                    self.canon_term(a, map, skip);
                }
                out.push(self.instance_label(&head, &args));
            } else {
                out.push(n.clone());
            }
        }
        if sorted {
            out.sort_by_key(|n| n.to_string());
            out.dedup();
        }
        out
    }

    /// Every row written inside `t`, in its one spelling.
    fn canon_term(
        &mut self,
        t: &mut SurfaceTerm,
        map: &HashMap<Name, SurfaceTerm>,
        skip: &HashSet<Name>,
    ) {
        walk::term(t, &mut |x| {
            if let TermKind::Row(names) = &*x.kind {
                let names = self.canon_row(&names.clone(), map, skip, true);
                *x = x.with_kind(TermKind::Row(names), x.span);
            }
        });
    }

    /// The name of the effect's instance at `args`, declared once.
    fn instance_label(&mut self, effect: &Name, args: &[SurfaceTerm]) -> Name {
        let mut args = args.to_vec();
        for argument in &mut args {
            walk::term(argument, &mut |term| {
                if let Some(reference) = self.report.type_references.get(&term.id()).or_else(|| {
                    self.prelude
                        .and_then(|report| report.type_references.get(&term.id()))
                }) {
                    if matches!(&*term.kind, TermKind::Var(Name::Selection(_))) {
                        *std::sync::Arc::make_mut(&mut term.kind) =
                            TermKind::Var(reference.clone());
                    }
                }
            });
        }
        let name = specialize(effect, &args);
        self.structured
            .entry(name.clone())
            .or_insert_with(|| (effect.clone(), args.clone()));
        if !self.labels.contains_key(&name)
            && let Some(decl) = self.effects.get(effect)
        {
            let map: HashMap<Name, SurfaceTerm> = decl
                .generics
                .iter()
                .cloned()
                .zip(args.iter().cloned())
                .collect();
            let mut d = decl.clone();
            d.name = name.clone();
            d.generics.clear();
            d.rows.clear();
            for p in d.params.iter_mut().flatten() {
                replace_vars(p, &map);
            }
            if let Some(r) = &mut d.result {
                replace_vars(r, &map);
            }
            let mut s = Stmt::Effect(d);
            freshen(&mut s);
            self.labels.insert(name.clone(), (effect.clone(), s));
        }
        name
    }

    /// The name of the copy of `f` at its index generics `args`.
    fn copy_name(&mut self, f: &Name, args: Vec<SurfaceTerm>) -> Name {
        let name = specialize(f, &args);
        if !self.copies.contains_key(&name) && !self.in_prelude.contains(&name) {
            self.copies.insert(name.clone(), f.clone());
            self.queue.push((name.clone(), (f.clone(), args)));
        }
        name
    }

    /// Renames the performs, arms, rows and calls of `s`, with the generics
    /// in `given` (the copy's).
    fn rewrite(
        &mut self,
        s: &mut Stmt,
        given: &HashMap<Name, SurfaceTerm>,
        errors: &mut Vec<(String, Span)>,
    ) {
        let mut pending: Vec<(crate::surface::TermId, Span, Name)> = Vec::new();
        // Collected first: the walk holds the statement.
        walk::stmt(s, &mut |t| match &*t.kind {
            TermKind::Perform { effect, .. } if self.indexed.contains(effect) => {
                pending.push((t.id(), t.span, effect.clone()))
            }
            TermKind::Handle { handlers, .. } => {
                for h in handlers {
                    if let Handler::Operation { effect, body, .. } = h
                        && self.indexed.contains(effect)
                    {
                        pending.push((body.id(), body.span, effect.clone()));
                    }
                }
            }
            _ => {}
        });
        let mut calls = HashMap::new();
        let mut call_args: HashMap<crate::surface::TermId, Vec<SurfaceTerm>> = HashMap::new();
        walk::stmt(s, &mut |t| {
            if let TermKind::App {
                function,
                arguments,
            } = &*t.kind
            {
                call_args.insert(function.id(), arguments.clone());
            }
            if let TermKind::Var(g) = &*t.kind
                && self.relevant.contains_key(g)
                && let Some(inst) = self.instantiation(t.id())
            {
                calls.insert(t.id(), (g.clone(), inst.clone(), t.span));
            }
        });
        // Outer calls first: the row a call gives its function argument is the
        // row around the calls inside it.
        let mut solved: Solved = HashMap::new();
        self.var_solutions.clear();
        self.performs.clear();
        self.lambda_rows.clear();
        self.env = match &*s {
            Stmt::Fn(f) => f
                .params
                .iter()
                .zip(&f.param_types)
                .filter_map(|(n, t)| Some((n.clone(), t.clone()?)))
                .collect(),
            _ => HashMap::new(),
        };
        if let Stmt::Fn(f) = &*s {
            let around = f.effects.as_ref().map(|row| self.around(row, given));
            if let Some(result) = &f.result {
                self.note_returned(&f.body, result, given);
            }
            self.solve_calls(&f.body.clone(), &around, given, &mut solved);
        }
        self.annotate_lets(s);
        // The performs and arms, after the calls and the rows around them: a
        // `perform` the types leave open is decided by the row it stands in.
        let mut names = HashMap::new();
        for (id, span, effect) in pending {
            let args = match self.performs.remove(&id) {
                Some(result) => result,
                None => self.arguments(id, given, span),
            };
            match args {
                Ok(args) => {
                    names.insert(id, self.instance_label(&effect, &args));
                }
                Err(why) => errors.push((format!("which `{effect}` this is: {why}"), span)),
            }
        }
        let mut call_names = HashMap::new();
        for (id, (g, inst, span)) in calls {
            let args = match solved.remove(&id) {
                Some(result) => result,
                None => {
                    let arguments = call_args.get(&id).cloned().unwrap_or_default();
                    self.solve_call(&g, &inst, span, &arguments, &None, given)
                        .map(|(args, _)| args)
                }
            };
            match args {
                Ok(args) => {
                    call_names.insert(id, self.copy_name(&g, args));
                }
                Err(why) => errors.push((why, span)),
            }
        }
        walk::stmt(s, &mut |t| {
            let id = t.id();
            match std::sync::Arc::make_mut(&mut t.kind) {
                TermKind::Perform { effect, .. } => {
                    if let Some(n) = names.get(&id) {
                        *effect = n.clone();
                    }
                }
                TermKind::Handle { handlers, .. } => {
                    for h in handlers {
                        if let Handler::Operation {
                            effect,
                            instance,
                            body,
                            ..
                        } = h
                            && let Some(n) = names.get(&body.id())
                        {
                            // The instance's own name: it has no generics.
                            *effect = n.clone();
                            *instance = Default::default();
                        }
                    }
                }
                TermKind::Var(g) => {
                    if let Some(n) = call_names.get(&id) {
                        *g = n.clone();
                    }
                }
                _ => {}
            }
        });
        // A data declaration is not copied: a row that writes its generics stays an application
        // until the data's arguments are known (`rows/values.rs`).
        let data_generics: HashSet<Name> = match &*s {
            Stmt::Struct(d) | Stmt::Enum(d) => d.generics.iter().cloned().collect(),
            _ => HashSet::new(),
        };
        rows_mut(s, &mut |row| {
            *row = self.canon_row(&row.clone(), given, &data_generics, false);
        });
        walk::stmt(s, &mut |t| {
            if let TermKind::Row(names) = &*t.kind {
                let names = self.canon_row(&names.clone(), given, &data_generics, true);
                *t = t.with_kind(TermKind::Row(names), t.span);
            }
        });
    }

    /// An unannotated `let` whose type holds a variable an index decided
    /// (`let child := Tree { … }` passed on as `Tree(e)`) is annotated with the
    /// type the index gives it: the rows check reads a row from the use no
    /// later than from the binding.
    fn annotate_lets(&mut self, s: &mut Stmt) {
        if self.var_solutions.is_empty() {
            return;
        }
        let Some(locals) = self.rows.as_ref().map(|r| r.locals.clone()) else {
            return;
        };
        let mut annotations: Vec<(crate::surface::TermId, SurfaceTerm)> = Vec::new();
        let mut walked = s.clone();
        walk::stmt(&mut walked, &mut |t| {
            if let TermKind::Block(stmts) = &*t.kind {
                for st in stmts {
                    if let Stmt::Let {
                        name,
                        ty: None,
                        value,
                        ..
                    } = st
                        && let Some(ty) = locals.get(&(name.clone(), value.id()))
                        && mentions_solved(ty, &self.var_solutions)
                    {
                        if let Some(written) = self.term_of_ty(ty, value.span, &HashMap::new()) {
                            annotations.push((value.id(), written));
                        }
                    }
                }
            }
        });
        if annotations.is_empty() {
            return;
        }
        walk::stmt(s, &mut |t| {
            if let TermKind::Block(stmts) = std::sync::Arc::make_mut(&mut t.kind) {
                for st in stmts {
                    if let Stmt::Let { ty, value, .. } = st
                        && ty.is_none()
                        && let Some((_, written)) =
                            annotations.iter().find(|(id, _)| *id == value.id())
                    {
                        *ty = Some(written.clone());
                    }
                }
            }
        });
    }

    /// A lambda written where a function type is written stands in that type's row.
    fn note_lambda(
        &mut self,
        value: &SurfaceTerm,
        ty: &SurfaceTerm,
        given: &HashMap<Name, SurfaceTerm>,
    ) {
        if matches!(&*value.kind, TermKind::Lam { .. })
            && let TermKind::Pi {
                effects: Some(row), ..
            } = &*ty.kind
        {
            let around = Some(self.around(row, given));
            self.lambda_rows.insert(value.id(), around);
        }
    }

    /// The lambda a function returns stands in the row its result type writes.
    fn note_returned(
        &mut self,
        body: &SurfaceTerm,
        result: &SurfaceTerm,
        given: &HashMap<Name, SurfaceTerm>,
    ) {
        match &*body.kind {
            TermKind::Block(stmts) => {
                if let Some(Stmt::Expr(e) | Stmt::Return(Some(e))) = stmts.last() {
                    self.note_returned(e, result, given);
                }
            }
            _ => self.note_lambda(body, result, given),
        }
    }

    /// The instances of indexed effects `row` names, with `given` applied.
    fn around(
        &mut self,
        row: &[Name],
        given: &HashMap<Name, SurfaceTerm>,
    ) -> Vec<(Name, Vec<SurfaceTerm>)> {
        let mut out = Vec::new();
        for n in row {
            if let Some(value) = given.get(n)
                && let TermKind::Row(rest) = &*value.kind
            {
                out.extend(rest.iter().filter_map(|n| self.structured.get(n).cloned()));
            } else if let Some(found) = self.structured.get(n) {
                out.push(found.clone());
            } else if let Some((head, mut args)) = application(n)
                && self.indexed.contains(&head)
            {
                for a in &mut args {
                    replace_vars(a, given);
                    self.canon_term(a, given, &HashSet::new());
                }
                out.push((head, args));
            }
        }
        out
    }

    /// The row around each lambda field of a record built where a parameter of
    /// type `ty` stands: the field's written row, with the data's generics read
    /// off `ty`.
    fn field_contexts(
        &mut self,
        record: &Name,
        ty: &SurfaceTerm,
        solution: &HashMap<Name, SurfaceTerm>,
    ) -> HashMap<String, Around> {
        let (head, args) = match &*ty.kind {
            TermKind::Var(h) => (h.clone(), Vec::new()),
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(h) => (h.clone(), arguments.clone()),
                _ => return HashMap::new(),
            },
            _ => return HashMap::new(),
        };
        let Some(data) = self.datas.get(&head).cloned() else {
            return HashMap::new();
        };
        // The record names a constructor of the data (`Boundary::Mk`), or the data.
        let Some(constructor) = data.constructors.iter().find(|c| {
            c.name.to_string() == record.to_string()
                || data.constructors.len() == 1 && head.to_string() == record.to_string()
        }) else {
            return HashMap::new();
        };
        let mut map: HashMap<Name, SurfaceTerm> = HashMap::new();
        for (generic, arg) in data.generics.iter().zip(args) {
            let mut arg = arg;
            replace_vars(&mut arg, solution);
            self.canon_term(&mut arg, solution, &HashSet::new());
            map.insert(generic.clone(), arg);
        }
        let mut out = HashMap::new();
        for (field, written) in &constructor.fields {
            let Some(field) = field else { continue };
            match &*written.kind {
                TermKind::Pi {
                    effects: Some(row), ..
                } => {
                    out.insert(field.clone(), Some(self.around(row, &map)));
                }
                // A record's struct (`{ failed: …, body: … }`) takes each field's type as a
                // generic: the function type, with its row, is the argument `ty` gives it.
                TermKind::Var(generic) => {
                    if let Some(arg) = map.get(generic)
                        && let TermKind::Pi {
                            effects: Some(row), ..
                        } = &*arg.kind
                    {
                        let row = row.clone();
                        out.insert(field.clone(), Some(self.around(&row, solution)));
                    }
                }
                _ => {}
            }
        }
        out
    }

    /// Solves the calls inside `t`, those that surround others first. `around`
    /// is the row the code must stay within, when it is written.
    fn solve_calls(
        &mut self,
        t: &SurfaceTerm,
        around: &Around,
        given: &HashMap<Name, SurfaceTerm>,
        out: &mut Solved,
    ) {
        let children = |t: &SurfaceTerm| {
            let mut kids = Vec::new();
            walk::children(&mut t.clone(), &mut |c| kids.push(c.clone()));
            kids
        };
        if matches!(&*t.kind, TermKind::Lam { .. })
            && let Some(inner) = self.lambda_rows.get(&t.id()).cloned()
        {
            for k in children(t) {
                self.solve_calls(&k, &inner, given, out);
            }
            return;
        }
        if let TermKind::Block(stmts) = &*t.kind {
            for st in stmts {
                if let Stmt::Let {
                    ty: Some(ty),
                    value,
                    ..
                } = st
                {
                    self.note_lambda(value, ty, given);
                }
            }
        }
        match &*t.kind {
            TermKind::App {
                function,
                arguments,
            } => {
                // What the callee's parameters say surrounds a lambda passed there, and
                // the callee's generics as the call decided them. A callee that is not
                // a function of the program says nothing, and a lambda passed to it has
                // no row around it.
                let mut callee: Option<(FnDecl, HashMap<Name, SurfaceTerm>)> = None;
                match &*function.kind {
                    TermKind::Var(g)
                        if self.relevant.contains_key(g)
                            && let Some(inst) = self.instantiation(function.id()).cloned() =>
                    {
                        let result =
                            self.solve_call(g, &inst, function.span, arguments, around, given);
                        if let Ok((_, solution)) = &result {
                            callee = Some((self.fns[g].clone(), solution.clone()));
                        }
                        out.insert(function.id(), result.map(|(args, _)| args));
                    }
                    TermKind::Var(g) => {
                        callee = self.fns.get(g).map(|decl| (decl.clone(), HashMap::new()));
                        self.solve_calls(function, around, given, out)
                    }
                    _ => self.solve_calls(function, around, given, out),
                }
                for (i, a) in arguments.iter().enumerate() {
                    let written = callee
                        .as_ref()
                        .and_then(|(decl, _)| decl.param_types.get(i))
                        .and_then(|ty| ty.as_ref());
                    let solution = callee.as_ref().map(|(_, s)| s.clone()).unwrap_or_default();
                    match &*a.kind {
                        TermKind::Lam { .. } => {
                            let inner = match written.map(|ty| &*ty.kind) {
                                Some(TermKind::Pi {
                                    effects: Some(row), ..
                                }) => Some(self.around(row, &solution)),
                                _ => None,
                            };
                            for k in children(a) {
                                self.solve_calls(&k, &inner, given, out);
                            }
                        }
                        // A record's field that is a lambda stands where the field's type
                        // puts it: its row, with the data's generics as the parameter's
                        // type gives them (`error_boundary(Boundary { failed: … })`).
                        TermKind::Record { name, fields, base } => {
                            let contexts = written
                                .map(|ty| self.field_contexts(name, ty, &solution))
                                .unwrap_or_default();
                            for (field, value) in fields {
                                if matches!(&*value.kind, TermKind::Lam { .. }) {
                                    let inner = contexts.get(field).cloned().unwrap_or(None);
                                    for k in children(value) {
                                        self.solve_calls(&k, &inner, given, out);
                                    }
                                } else {
                                    self.solve_calls(value, around, given, out);
                                }
                            }
                            if let Some(base) = base {
                                self.solve_calls(base, around, given, out);
                            }
                        }
                        _ => self.solve_calls(a, around, given, out),
                    }
                }
            }
            TermKind::Perform { effect, .. } if self.indexed.contains(effect) => {
                let result = match self.arguments(t.id(), given, t.span) {
                    Ok(args) => Ok(args),
                    Err(why) => {
                        let mut candidates: Vec<&Vec<SurfaceTerm>> = Vec::new();
                        for (head, args) in around.iter().flatten() {
                            if head == effect
                                && !candidates.iter().any(|c| {
                                    c.len() == args.len()
                                        && c.iter()
                                            .zip(args)
                                            .all(|(x, y)| crate::surface::same_term_structure(x, y))
                                })
                            {
                                candidates.push(args);
                            }
                        }
                        match candidates.len() {
                            1 => Ok(candidates[0].clone()),
                            0 => Err(why),
                            _ => Err(format!(
                                "the row around it has two instances of `{effect}`; write which with a type annotation"
                            )),
                        }
                    }
                };
                self.performs.insert(t.id(), result);
                for k in children(t) {
                    self.solve_calls(&k, around, given, out);
                }
            }
            TermKind::Var(g) if self.relevant.contains_key(g) => {
                if let Some(inst) = self.instantiation(t.id()).cloned() {
                    let result = self.solve_call(g, &inst, t.span, &[], around, given);
                    out.insert(t.id(), result.map(|(args, _)| args));
                }
            }
            _ => {
                for k in children(t) {
                    if matches!(&*k.kind, TermKind::Lam { .. }) {
                        let inner = self.lambda_rows.get(&k.id()).cloned().unwrap_or(None);
                        for kk in children(&k) {
                            self.solve_calls(&kk, &inner, given, out);
                        }
                    } else {
                        self.solve_calls(&k, around, given, out);
                    }
                }
            }
        }
    }

    /// The arguments of the generics of `g` that indices depend on, at one
    /// use: what the types fix, else what the row around the call has of the
    /// effect the call's own row names, else what its arguments perform.
    fn solve_call(
        &mut self,
        g: &Name,
        inst: &HashMap<super::ParamId, Ty>,
        span: Span,
        arguments: &[SurfaceTerm],
        around: &Around,
        given: &HashMap<Name, SurfaceTerm>,
    ) -> Result<(Vec<SurfaceTerm>, HashMap<Name, SurfaceTerm>), String> {
        let scheme = self.scheme(g).expect("a called function");
        let decl = self.fns[g].clone();
        let mut solution: HashMap<Name, SurfaceTerm> = HashMap::new();
        let mut args = Vec::new();
        for wanted in self.relevant[g].clone() {
            let ty = scheme
                .generics
                .iter()
                .find(|(p, _)| p.name == wanted)
                .and_then(|(p, _)| inst.get(p.id()));
            let mut arg = ty.and_then(|t| self.term_of_ty(t, span, given));
            if arg.is_none() {
                arg = self.from_around(&decl, &wanted, around)?;
            }
            if arg.is_none() {
                arg = self.from_argument_types(&decl, &wanted, arguments, given)?;
            }
            if arg.is_none() {
                match self.from_rows(g, &wanted, arguments, given) {
                    Ok(a) => arg = Some(a),
                    Err(Some(why)) => {
                        return Err(format!("`{g}` indexes an effect by `{wanted}`: {why}"));
                    }
                    Err(None) => {}
                }
            }
            let Some(arg) = arg else {
                return Err(format!(
                    "`{g}` indexes an effect by `{wanted}`, which is not known here"
                ));
            };
            if let Some(Ty::Var(n)) = ty {
                self.var_solutions.insert(*n, arg.clone());
            }
            solution.insert(wanted, arg.clone());
            args.push(arg);
        }
        Ok((args, solution))
    }

    /// `wanted`, read from the written type of an argument that is a parameter
    /// of the function around the call: its row names the instance the
    /// callee's parameter row writes with `wanted` (`with_ui(child, body)`).
    fn from_argument_types(
        &mut self,
        decl: &FnDecl,
        wanted: &Name,
        arguments: &[SurfaceTerm],
        given: &HashMap<Name, SurfaceTerm>,
    ) -> Result<Option<SurfaceTerm>, String> {
        let mut found: Vec<SurfaceTerm> = Vec::new();
        for (ty, arg) in decl.param_types.iter().zip(arguments) {
            let (Some(ty), TermKind::Var(x)) = (ty, &*arg.kind) else {
                continue;
            };
            let Some(have) = self.env.get(x).cloned() else {
                continue;
            };
            let TermKind::Pi {
                effects: Some(have_row),
                ..
            } = &*have.kind
            else {
                continue;
            };
            let TermKind::Pi {
                effects: Some(want_row),
                ..
            } = &*ty.kind
            else {
                continue;
            };
            let around = self.around(have_row, given);
            for entry in want_row {
                let Some((head, indices)) = application(entry) else {
                    continue;
                };
                let Some(position) = indices.iter().position(
                    |argument| matches!(&*argument.kind, TermKind::Var(name) if name == wanted),
                ) else {
                    continue;
                };
                for (h, args) in &around {
                    if h == &head
                        && let Some(a) = args.get(position)
                        && !found
                            .iter()
                            .any(|term| crate::surface::same_term_structure(term, a))
                    {
                        found.push(a.clone());
                    }
                }
            }
        }
        match found.len() {
            0 => Ok(None),
            1 => Ok(found.pop()),
            _ => Err(format!(
                "its arguments' rows name `{wanted}` as {}; write which with a type annotation",
                found.iter().map(print).collect::<Vec<_>>().join(" and ")
            )),
        }
    }

    /// `wanted`, read from the instance of the same effect in the row around a
    /// call whose own row names `wanted` as an index (`on`'s `cur_ui(e)`).
    fn from_around(
        &mut self,
        decl: &FnDecl,
        wanted: &Name,
        around: &Around,
    ) -> Result<Option<SurfaceTerm>, String> {
        let Some(around) = around else {
            return Ok(None);
        };
        let mut found: Vec<SurfaceTerm> = Vec::new();
        for entry in decl.effects.iter().flatten() {
            let Some((head, indices)) = application(entry) else {
                continue;
            };
            if !self.indexed.contains(&head) {
                continue;
            }
            let Some(position) = indices.iter().position(
                |argument| matches!(&*argument.kind, TermKind::Var(name) if name == wanted),
            ) else {
                continue;
            };
            for (h, args) in around {
                if h == &head
                    && let Some(a) = args.get(position)
                    && !found
                        .iter()
                        .any(|term| crate::surface::same_term_structure(term, a))
                {
                    found.push(a.clone());
                }
            }
        }
        match found.len() {
            0 => Ok(None),
            1 => Ok(found.pop()),
            _ => Err(format!(
                "the row around this call has two instances of the effect it indexes by `{wanted}`: {}; write which with a type annotation",
                found.iter().map(print).collect::<Vec<_>>().join(" and ")
            )),
        }
    }

    /// `wanted`, a generic of `g` that a parameter's row writes as an index
    /// (`&body: () -> T ! {fail(E)} ∪ e`), read from the instances of that
    /// effect the argument performs: `Err(None)` when nothing says, an
    /// error when they disagree.
    fn from_rows(
        &mut self,
        g: &Name,
        wanted: &Name,
        arguments: &[SurfaceTerm],
        given: &HashMap<Name, SurfaceTerm>,
    ) -> Result<SurfaceTerm, Option<String>> {
        let decl = self.fns.get(g).ok_or(None)?.clone();
        let mut found: Vec<SurfaceTerm> = Vec::new();
        let mut first = None;
        for (ty, arg) in decl.param_types.iter().zip(arguments) {
            let Some(ty) = ty else { continue };
            let mut rows = Vec::new();
            let mut ty = ty.clone();
            walk::term(&mut ty, &mut |t| {
                if let TermKind::Pi {
                    effects: Some(row), ..
                } = &*t.kind
                {
                    rows.extend(row.iter().cloned());
                }
            });
            for entry in rows {
                let Some((head, indices)) = application(&entry) else {
                    continue;
                };
                if !self.indexed.contains(&head) {
                    continue;
                }
                let Some(position) = indices.iter().position(
                    |argument| matches!(&*argument.kind, TermKind::Var(name) if name == wanted),
                ) else {
                    continue;
                };
                let mut seen = HashSet::new();
                for instance in self.performed(arg, &head, given, &mut seen) {
                    if let Some(a) = instance.get(position) {
                        if !found
                            .iter()
                            .any(|term| crate::surface::same_term_structure(term, a))
                        {
                            found.push(a.clone());
                            first.get_or_insert(a.clone());
                        }
                    }
                }
            }
        }
        match found.len() {
            0 => Err(None),
            1 => Ok(first.expect("found")),
            _ => Err(Some(format!(
                "the argument performs it as {}; write which with the result's type",
                found.iter().map(print).collect::<Vec<_>>().join(" and ")
            ))),
        }
    }

    /// The instances of `effect` that `t` performs itself or through the
    /// functions it calls, by their written rows or their bodies.
    fn performed(
        &mut self,
        t: &SurfaceTerm,
        effect: &Name,
        given: &HashMap<Name, SurfaceTerm>,
        seen: &mut HashSet<Name>,
    ) -> Vec<Vec<SurfaceTerm>> {
        let mut out = Vec::new();
        let mut t = t.clone();
        let mut calls = Vec::new();
        walk::term(&mut t, &mut |x| match &*x.kind {
            TermKind::Perform { effect: e, .. } if e == effect => {
                if let Ok(args) = self.arguments(x.id(), given, x.span) {
                    out.push(args);
                }
            }
            TermKind::Var(g) if self.fns.contains_key(g) => calls.push((g.clone(), x.id(), x.span)),
            _ => {}
        });
        for (g, id, span) in calls {
            let decl = self.fns[&g].clone();
            let inst: HashMap<Name, SurfaceTerm> = match (self.instantiation(id), self.scheme(&g)) {
                (Some(inst), Some(scheme)) => scheme
                    .generics
                    .iter()
                    .filter_map(|(p, _)| {
                        let ty = inst.get(p.id())?;
                        let mut a = match ty {
                            Ty::Param(q, _) => given.get(&q.name).cloned()?,
                            t => surface_of(t, span)?,
                        };
                        replace_vars(&mut a, given);
                        Some((p.name.clone(), a))
                    })
                    .collect(),
                _ => HashMap::new(),
            };
            match &decl.effects {
                Some(row) => {
                    for entry in row {
                        let Some((head, mut args)) = application(entry) else {
                            continue;
                        };
                        if &head != effect {
                            continue;
                        }
                        for argument in &mut args {
                            replace_vars(argument, &inst);
                        }
                        out.push(args);
                    }
                }
                None if seen.insert(g.clone()) => {
                    out.extend(self.performed(&decl.body, effect, &inst, seen));
                }
                None => {}
            }
        }
        out
    }

    fn instance(
        &mut self,
        name: &Name,
        (f, args): &(Name, Vec<SurfaceTerm>),
        errors: &mut Vec<(String, Span)>,
    ) -> Stmt {
        let mut decl = self.fns[f].clone();
        let relevant = self.relevant[f].clone();
        let given: HashMap<Name, SurfaceTerm> =
            relevant.iter().cloned().zip(args.iter().cloned()).collect();
        let mut s = Stmt::Fn(decl.clone());
        self.rewrite(&mut s, &given, errors);
        let Stmt::Fn(rewritten) = s else {
            unreachable!()
        };
        decl = rewritten;
        decl.name = name.clone();
        let keep: Vec<bool> = decl
            .generics
            .iter()
            .map(|g| !given.contains_key(g))
            .collect();
        let mut i = 0;
        decl.generics.retain(|_| {
            i += 1;
            keep[i - 1]
        });
        let mut i = 0;
        decl.bounds.retain(|_| {
            i += 1;
            keep.get(i - 1).copied().unwrap_or(true)
        });
        let mut i = 0;
        decl.rows.retain(|_| {
            i += 1;
            keep.get(i - 1).copied().unwrap_or(true)
        });
        // Each specialized declaration owns its remaining telescope. Its
        // row binders must not acquire the owner of another specialization.
        let locals: HashMap<Name, Name> = decl
            .generics
            .iter()
            .chain(&decl.params)
            .filter_map(|name| {
                name.as_local()
                    .map(|local| (name.clone(), Name::Local(local.freshened(name.to_string()))))
            })
            .collect();
        let mut s = Stmt::Fn(decl);
        walk::stmt(&mut s, &mut |t| {
            if let TermKind::Var(n) = &*t.kind
                && let Some(r) = given.get(n)
            {
                *t = t.with_kind((*r.kind).clone(), t.span);
            }
        });
        crate::surface::references::statement(&mut s, &mut |name| {
            if let Some(local) = locals.get(name) {
                *name = local.clone();
            }
        });
        freshen(&mut s);
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bare_host_show_hints_only_every_instance() {
        let generics = HashMap::from([(Name::from("show"), vec![Name::from("A")])]);
        let mut entry = Name::from("show".to_string());
        let why = read_entry(&mut entry, &generics).unwrap_err();
        assert!(why.contains("∀ A. show(A)"), "{why}");
        assert!(!why.contains("show(…)"), "{why}");
        let mut entry = Name::from("∀ A. show(A)".to_string());
        read_entry(&mut entry, &generics).unwrap();
        assert_eq!(entry.as_str(), "show");
    }
}
