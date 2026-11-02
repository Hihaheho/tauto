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

use std::collections::{HashMap, HashSet};

use super::{Ty, TypeReport, check_program_in, prelude, prelude_report};
use crate::surface::PRELUDE_BASE;
use crate::surface::walk;
use crate::surface::{EffectDecl, FnDecl, Handler, Program, Stmt, SurfaceTerm, TermKind};
use tauto_parol::Span;

/// Effects the host answers by their names; they are never indexed.
const HOST: &[&str] = &["show", "exceeded"];

/// The head of a row entry written with type arguments: `res(Pos)` → `res`.
fn indexed_head(entry: &str) -> Option<&str> {
    if entry.starts_with(['|', '?', '∀']) || entry.contains('@') {
        return None;
    }
    entry.split_once('(').map(|(head, _)| head.trim())
}

/// Every row of the statement: the written rows of its functions (local ones
/// too) and of the function types in it.
fn rows_mut(s: &mut Stmt, f: &mut dyn FnMut(&mut Vec<String>)) {
    fn fn_rows(d: &mut FnDecl, f: &mut dyn FnMut(&mut Vec<String>)) {
        if let Some(row) = &mut d.effects {
            f(row);
        }
    }
    fn stmt_rows(s: &mut Stmt, f: &mut dyn FnMut(&mut Vec<String>)) {
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
pub(super) fn indexed_effects(program: &Program) -> HashSet<String> {
    let mut found = HashSet::new();
    for s in &program.stmts {
        let mut s = s.clone();
        rows_mut(&mut s, &mut |row| {
            for entry in row.iter() {
                if let Some(head) = indexed_head(entry)
                    && !HOST.contains(&head)
                {
                    found.insert(head.to_string());
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
                        && !HOST.contains(&effect.as_str())
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
fn typed_generics(programs: &[&Program]) -> HashMap<String, Vec<String>> {
    fn mentions(t: &SurfaceTerm, name: &str) -> bool {
        let mut found = false;
        let mut t = t.clone();
        walk::term(&mut t, &mut |x| {
            if matches!(&*x.kind, TermKind::Var(v) if v == name) {
                found = true;
            }
        });
        found
    }
    fn collect(stmts: &[Stmt], out: &mut HashMap<String, Vec<String>>) {
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
    let mut out = HashMap::from([("show".to_string(), vec!["A".to_string()])]);
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
    let touched = prelude_touched();
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
fn prelude_touched() -> &'static HashSet<String> {
    static TOUCHED: std::sync::OnceLock<HashSet<String>> = std::sync::OnceLock::new();
    TOUCHED.get_or_init(|| {
        let indexed = indexed_effects(prelude());
        let mut touched: HashSet<String> = indexed.clone();
        let mut fns: Vec<(String, Stmt)> = Vec::new();
        fn collect(stmts: &[Stmt], out: &mut Vec<(String, Stmt)>) {
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
        collect(&prelude().stmts, &mut fns);
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
                        indexed_head(e).is_some_and(|h| indexed.contains(h))
                            || indexed.contains(e.as_str())
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
pub(super) fn every_instance(program: &mut Program, per_file: &mut [Vec<Stmt>]) {
    let generics = if program
        .stmts
        .first()
        .and_then(stmt_span)
        .is_some_and(|sp| sp.start >= PRELUDE_BASE)
    {
        typed_generics(&[program])
    } else {
        typed_generics(&[prelude(), program])
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
    program.errors.extend(errors);
}

fn read_entry(entry: &mut String, generics: &HashMap<String, Vec<String>>) -> Result<(), String> {
    if let Some(rest) = entry.strip_prefix('∀') {
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
        let typed = generics.get(head).map(Vec::as_slice).unwrap_or_default();
        let distinct = names.iter().collect::<HashSet<_>>().len() == names.len();
        if typed.is_empty() || !distinct || names != args || args.len() != typed.len() {
            let want = typed.join(", ");
            return Err(format!(
                "`{entry}`: every instance of `{head}` binds each type argument in order: `∀ {want}. {head}({want})`"
            ));
        }
        *entry = head.to_string();
        return Ok(());
    }
    if entry.starts_with(['|', '?']) || entry.contains(['(', '@']) {
        return Ok(());
    }
    match generics.get(entry.as_str()) {
        Some(typed) if !typed.is_empty() => {
            let want = typed.join(", ");
            // A host operation is never read by instance, so the only row
            // that names it is the one for every instance.
            if HOST.contains(&entry.as_str()) {
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
pub(super) fn index_generics(program: &Program) -> HashMap<String, HashSet<String>> {
    let indexed = indexed_effects(program);
    let mut out = HashMap::new();
    for (name, f) in functions(&program.stmts) {
        let mut found = HashSet::new();
        let mut s = Stmt::Fn(f.clone());
        rows_mut(&mut s, &mut |row| {
            for entry in row.iter() {
                if let Some(head) = indexed_head(entry)
                    && indexed.contains(head)
                {
                    found.extend(
                        idents(&entry[head.len()..])
                            .filter(|i| f.generics.iter().any(|g| g == i))
                            .map(str::to_string),
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
        Ty::Int(_) | Ty::Bool | Ty::Text | Ty::Decimal | Ty::Float | Ty::Float32 => {
            Some(SurfaceTerm::var(&t.to_string(), span))
        }
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

/// A type argument as text, the same for a written one and an inferred one.
fn print(t: &SurfaceTerm) -> String {
    match &*t.kind {
        TermKind::Var(n) => n.clone(),
        TermKind::App {
            function,
            arguments,
        } => {
            let args: Vec<String> = arguments.iter().map(print).collect();
            format!("{}({})", print(function), args.join(","))
        }
        _ => "?".into(),
    }
}

fn label(effect: &str, args: &[SurfaceTerm]) -> String {
    let args: Vec<String> = args.iter().map(print).collect();
    format!("{effect}@{}", args.join(","))
}

fn replace_vars(t: &mut SurfaceTerm, map: &HashMap<String, SurfaceTerm>) {
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

fn params_in(t: &Ty, out: &mut HashSet<String>) {
    match t {
        Ty::Param(p, _) => {
            out.insert(p.name().to_string());
        }
        Ty::Fn(ps, r, _) => {
            ps.iter().for_each(|p| params_in(p, out));
            params_in(r, out);
        }
        Ty::Union(ts) | Ty::Product(ts) | Ty::Named(_, ts) => {
            ts.iter().for_each(|t| params_in(t, out))
        }
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Poly(_, t) => params_in(t, out),
        Ty::App(h, x) => {
            params_in(h, out);
            params_in(x, out);
        }
        _ => {}
    }
}

fn idents(text: &str) -> impl Iterator<Item = &str> {
    text.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == ':'))
        .filter(|s| !s.is_empty())
}

fn functions(stmts: &[Stmt]) -> HashMap<String, FnDecl> {
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
pub fn expand_indices(program: &mut Program, per_file: &mut [Vec<Stmt>]) {
    every_instance(program, per_file);
    // The prelude is expanded as a program of its own, checked against
    // itself; it keeps the functions it copies, which a program's calls copy
    // into the program.
    let is_prelude = program
        .stmts
        .first()
        .and_then(stmt_span)
        .is_some_and(|sp| sp.start >= PRELUDE_BASE);
    let mut indexed = indexed_effects(program);
    if !is_prelude {
        if indexed.is_empty() && !touches_indexed(program) {
            return;
        }
        indexed.extend(indexed_effects(prelude()));
    }
    if indexed.is_empty() {
        return;
    }
    let report = if is_prelude {
        check_program_in(program, program)
    } else {
        check_program_in(program, prelude())
    };
    if !report.errors.is_empty() {
        return;
    }
    let mut x = Expander::new(program, &report, indexed, is_prelude);
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
    let made: Vec<(String, Stmt)> = x
        .made
        .iter()
        .map(|(n, s)| (x.copies[n].clone(), s.clone()))
        .collect();
    let decls: Vec<(String, Stmt)> = x.labels.values().cloned().collect();
    place(&mut program.stmts, &made, &decls, true);
    let mut first = true;
    for file in per_file.iter_mut() {
        place(file, &made, &decls, first);
        first = false;
    }
    program.errors.extend(errors);
}

/// Puts each statement after the declaration it was made from, or first when
/// that is not here and `first`.
fn place(stmts: &mut Vec<Stmt>, made: &[(String, Stmt)], decls: &[(String, Stmt)], first: bool) {
    let mut sorted: Vec<&(String, Stmt)> = decls.iter().chain(made).collect();
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

fn stmt_name(s: &Stmt) -> &str {
    match s {
        Stmt::Fn(f) => &f.name,
        Stmt::Effect(e) => &e.name,
        _ => "",
    }
}

struct Expander<'a> {
    report: &'a TypeReport,
    /// The prelude's, for a program's copies of its functions.
    prelude: Option<&'static TypeReport>,
    is_prelude: bool,
    /// The functions the prelude has, its copies too.
    in_prelude: HashSet<String>,
    indexed: HashSet<String>,
    fns: HashMap<String, FnDecl>,
    effects: HashMap<String, EffectDecl>,
    relevant: HashMap<String, Vec<String>>,
    queue: Vec<(String, (String, Vec<SurfaceTerm>))>,
    made: HashMap<String, Stmt>,
    copies: HashMap<String, String>,
    labels: HashMap<String, (String, Stmt)>,
}

impl<'a> Expander<'a> {
    fn new(
        program: &Program,
        report: &'a TypeReport,
        indexed: HashSet<String>,
        is_prelude: bool,
    ) -> Self {
        let mut effects = HashMap::new();
        let mut fns = HashMap::new();
        let mut in_prelude = HashSet::new();
        if !is_prelude {
            for s in &prelude().stmts {
                if let Stmt::Effect(e) = s {
                    effects.insert(e.name.clone(), e.clone());
                }
            }
            fns = functions(&prelude().stmts);
            in_prelude = fns.keys().cloned().collect();
        }
        for s in &program.stmts {
            if let Stmt::Effect(e) = s {
                effects.insert(e.name.clone(), e.clone());
            }
        }
        for (name, f) in functions(&program.stmts) {
            in_prelude.remove(&name);
            fns.insert(name, f);
        }
        Expander {
            report,
            prelude: (!is_prelude).then(prelude_report),
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

    fn effect_args(&self, id: crate::surface::TermId) -> Option<&'a Vec<Ty>> {
        self.report
            .effect_args
            .get(&id)
            .or_else(|| self.prelude?.effect_args.get(&id))
    }

    fn instantiation(&self, id: crate::surface::TermId) -> Option<&'a HashMap<super::ParamId, Ty>> {
        self.report
            .instantiations
            .get(&id)
            .or_else(|| self.prelude?.instantiations.get(&id))
    }

    fn scheme(&self, name: &str) -> Option<&'a super::Scheme> {
        self.report
            .schemes
            .get(name)
            .or_else(|| self.prelude?.schemes.get(name))
    }

    /// The generics of each function that an index depends on, to a fixpoint
    /// through the calls.
    fn relevance(&mut self) {
        let mut relevant: HashMap<String, HashSet<String>> = HashMap::new();
        for (name, f) in &self.fns {
            let generics: HashSet<&str> = f.generics.iter().map(|g| g.as_str()).collect();
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
                    if let Some(head) = indexed_head(entry)
                        && self.indexed.contains(head)
                    {
                        found.extend(idents(&entry[head.len()..]).map(str::to_string));
                    }
                }
            });
            found.retain(|g| generics.contains(g.as_str()));
            relevant.insert(name.clone(), found);
        }
        loop {
            let mut changed = false;
            for (name, f) in &self.fns {
                let generics: HashSet<&str> = f.generics.iter().map(|g| g.as_str()).collect();
                let mut found = HashSet::new();
                let mut s = Stmt::Fn(f.clone());
                walk::stmt(&mut s, &mut |t| {
                    if let TermKind::Var(g) = &*t.kind
                        && let Some(inst) = self.instantiation(t.id())
                        && let Some(scheme) = self.scheme(g)
                    {
                        for (p, _) in &scheme.generics {
                            if relevant.get(g).is_some_and(|r| r.contains(p.name()))
                                && let Some(ty) = inst.get(p.id())
                            {
                                params_in(ty, &mut found);
                            }
                        }
                    }
                });
                let own = relevant.get_mut(name).expect("every function");
                for g in found {
                    if generics.contains(g.as_str()) && own.insert(g) {
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
            let ordered: Vec<String> = f
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
        &self,
        id: crate::surface::TermId,
        given: &HashMap<String, SurfaceTerm>,
        span: Span,
    ) -> Result<Vec<SurfaceTerm>, String> {
        let Some(args) = self.effect_args(id) else {
            return Err("no type was found".into());
        };
        args.iter()
            .map(|t| match t {
                Ty::Param(p, _) => given
                    .get(p.name())
                    .cloned()
                    .ok_or_else(|| format!("it is the generic `{}`, which is not given", p.name())),
                Ty::Var(_) => Err("its type arguments are not known here; annotate them".into()),
                _ => {
                    let mut t = surface_of(t, span)
                        .ok_or_else(|| format!("`{t}` cannot index an effect"))?;
                    replace_vars(&mut t, given);
                    Ok(t)
                }
            })
            .collect()
    }

    /// The name of the effect's instance at `args`, declared once.
    fn instance_label(&mut self, effect: &str, args: &[SurfaceTerm]) -> String {
        let name = label(effect, args);
        if !self.labels.contains_key(&name)
            && let Some(decl) = self.effects.get(effect)
        {
            let map: HashMap<String, SurfaceTerm> = decl
                .generics
                .iter()
                .cloned()
                .zip(args.iter().cloned())
                .collect();
            let mut d = decl.clone();
            d.name = name.clone();
            d.generics.clear();
            for p in d.params.iter_mut().flatten() {
                replace_vars(p, &map);
            }
            if let Some(r) = &mut d.result {
                replace_vars(r, &map);
            }
            let mut s = Stmt::Effect(d);
            freshen(&mut s);
            self.labels.insert(name.clone(), (effect.to_string(), s));
        }
        name
    }

    fn copy_name(&mut self, f: &str, args: Vec<SurfaceTerm>) -> String {
        let name = label(f, &args);
        if !self.copies.contains_key(&name) && !self.in_prelude.contains(&name) {
            self.copies.insert(name.clone(), f.to_string());
            self.queue.push((name.clone(), (f.to_string(), args)));
        }
        name
    }

    /// Renames the performs, arms, rows and calls of `s`, with the generics
    /// in `given` (the copy's).
    fn rewrite(
        &mut self,
        s: &mut Stmt,
        given: &HashMap<String, SurfaceTerm>,
        errors: &mut Vec<(String, Span)>,
    ) {
        let mut pending: Vec<(crate::surface::TermId, Span, String)> = Vec::new();
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
        let mut names = HashMap::new();
        for (id, span, effect) in pending {
            match self.arguments(id, given, span) {
                Ok(args) => {
                    names.insert(id, self.instance_label(&effect, &args));
                }
                Err(why) => errors.push((format!("which `{effect}` this is: {why}"), span)),
            }
        }
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
        let mut call_names = HashMap::new();
        for (id, (g, inst, span)) in calls {
            let arguments = call_args.get(&id).cloned().unwrap_or_default();
            let scheme = self.scheme(&g).expect("a called function");
            let mut args = Vec::new();
            for wanted in self.relevant[&g].clone() {
                let ty = scheme
                    .generics
                    .iter()
                    .find(|(p, _)| p.name() == wanted)
                    .and_then(|(p, _)| inst.get(p.id()));
                let arg = match ty {
                    Some(Ty::Param(p, _)) => given.get(p.name()).cloned(),
                    Some(t) => surface_of(t, span).map(|mut t| {
                        replace_vars(&mut t, given);
                        t
                    }),
                    None => None,
                };
                // Not fixed by the types: the row of the argument whose
                // function type writes the index says it (`catch`'s body).
                let arg = match arg {
                    Some(a) => Ok(a),
                    None => self.from_rows(&g, &wanted, &arguments, given),
                };
                match arg {
                    Ok(a) => args.push(a),
                    Err(Some(why)) => {
                        errors.push((
                            format!("`{g}` indexes an effect by `{wanted}`: {why}"),
                            span,
                        ));
                        break;
                    }
                    Err(None) => {
                        errors.push((
                            format!(
                                "`{g}` indexes an effect by `{wanted}`, which is not known here"
                            ),
                            span,
                        ));
                        break;
                    }
                }
            }
            if args.len() == self.relevant[&g].len() {
                call_names.insert(id, self.copy_name(&g, args));
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
        let mut wanted = Vec::new();
        rows_mut(s, &mut |row| {
            for entry in row.iter_mut() {
                let Some(head) = indexed_head(entry).map(str::to_string) else {
                    continue;
                };
                if !self.indexed.contains(&head) {
                    continue;
                }
                let inner = entry[head.len()..].trim();
                let inner = inner
                    .strip_prefix('(')
                    .and_then(|i| i.strip_suffix(')'))
                    .unwrap_or("");
                let args: Option<Vec<SurfaceTerm>> = split_top(inner)
                    .into_iter()
                    .map(|a| {
                        parse_argument(a, Span::new(0, 0)).map(|mut t| {
                            replace_vars(&mut t, given);
                            t
                        })
                    })
                    .collect();
                if let Some(args) = args {
                    *entry = label(&head, &args);
                    wanted.push((head, args));
                }
            }
        });
        for (head, args) in wanted {
            self.instance_label(&head, &args);
        }
    }

    /// `wanted`, a generic of `g` that a parameter's row writes as an index
    /// (`&body: () -> T ! {fail(E)} ∪ e`), read from the instances of that
    /// effect the argument performs: `Err(None)` when nothing says, an
    /// error when they disagree.
    fn from_rows(
        &self,
        g: &str,
        wanted: &str,
        arguments: &[SurfaceTerm],
        given: &HashMap<String, SurfaceTerm>,
    ) -> Result<SurfaceTerm, Option<String>> {
        let decl = self.fns.get(g).ok_or(None)?;
        let mut found: Vec<String> = Vec::new();
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
                let Some(head) = indexed_head(&entry) else {
                    continue;
                };
                if !self.indexed.contains(head) {
                    continue;
                }
                let inner = entry[head.len()..].trim();
                let inner = inner
                    .strip_prefix('(')
                    .and_then(|i| i.strip_suffix(')'))
                    .unwrap_or("");
                let Some(position) = split_top(inner).iter().position(|a| a.trim() == wanted)
                else {
                    continue;
                };
                let mut seen = HashSet::new();
                for instance in self.performed(arg, head, given, &mut seen) {
                    if let Some(a) = instance.get(position) {
                        let text = print(a);
                        if !found.contains(&text) {
                            found.push(text);
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
                found.join(" and ")
            ))),
        }
    }

    /// The instances of `effect` that `t` performs itself or through the
    /// functions it calls, by their written rows or their bodies.
    fn performed(
        &self,
        t: &SurfaceTerm,
        effect: &str,
        given: &HashMap<String, SurfaceTerm>,
        seen: &mut HashSet<String>,
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
            let decl = &self.fns[&g];
            let inst: HashMap<String, SurfaceTerm> = match (self.instantiation(id), self.scheme(&g))
            {
                (Some(inst), Some(scheme)) => scheme
                    .generics
                    .iter()
                    .filter_map(|(p, _)| {
                        let ty = inst.get(p.id())?;
                        let mut a = match ty {
                            Ty::Param(q, _) => given.get(q.name()).cloned()?,
                            t => surface_of(t, span)?,
                        };
                        replace_vars(&mut a, given);
                        Some((p.name().to_string(), a))
                    })
                    .collect(),
                _ => HashMap::new(),
            };
            match &decl.effects {
                Some(row) => {
                    for entry in row {
                        if indexed_head(entry) != Some(effect) {
                            continue;
                        }
                        let inner = entry[effect.len()..].trim();
                        let inner = inner
                            .strip_prefix('(')
                            .and_then(|i| i.strip_suffix(')'))
                            .unwrap_or("");
                        let args: Option<Vec<SurfaceTerm>> = split_top(inner)
                            .into_iter()
                            .map(|a| {
                                parse_argument(a, span).map(|mut t| {
                                    replace_vars(&mut t, &inst);
                                    t
                                })
                            })
                            .collect();
                        if let Some(args) = args {
                            out.push(args);
                        }
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
        name: &str,
        (f, args): &(String, Vec<SurfaceTerm>),
        errors: &mut Vec<(String, Span)>,
    ) -> Stmt {
        let mut decl = self.fns[f].clone();
        let relevant = self.relevant[f].clone();
        let given: HashMap<String, SurfaceTerm> =
            relevant.iter().cloned().zip(args.iter().cloned()).collect();
        let mut s = Stmt::Fn(decl.clone());
        self.rewrite(&mut s, &given, errors);
        let Stmt::Fn(rewritten) = s else {
            unreachable!()
        };
        decl = rewritten;
        decl.name = name.to_string();
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
        let mut s = Stmt::Fn(decl);
        walk::stmt(&mut s, &mut |t| {
            if let TermKind::Var(n) = &*t.kind
                && let Some(r) = given.get(n)
            {
                *t = t.with_kind((*r.kind).clone(), t.span);
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
        let generics = HashMap::from([("show".to_string(), vec!["A".to_string()])]);
        let mut entry = "show".to_string();
        let why = read_entry(&mut entry, &generics).unwrap_err();
        assert!(why.contains("∀ A. show(A)"), "{why}");
        assert!(!why.contains("show(…)"), "{why}");
        let mut entry = "∀ A. show(A)".to_string();
        read_entry(&mut entry, &generics).unwrap();
        assert_eq!(entry, "show");
    }
}
