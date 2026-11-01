//! `module M { … }` and the names `M::f`: modules
//! are flattened where the program is read, so what follows sees plain names
//! with `::` in them (`File::open`).
//!
//! Functions (and the functions of `extern` blocks), theorems and types
//! (`struct`, `enum`, `inductive`) take the module's name: a type `T` of
//! `module M` is `M::T`, and its constructor `C` is `M::T::C` (a struct's one
//! constructor is the type's name, `M::T`). Inside the module they are written
//! `T`, `C` and `T::C`; outside, `M::T` and `M::T::C`. Effects and classes in a
//! module keep their names.

use std::cell::RefCell;
use std::collections::HashSet;
use std::sync::Arc;

use tauto_message::msg;
use tauto_parol::Span;

use super::program::{FnDecl, Handler, Pattern, Stmt};
use super::qualify::SEPARATOR;
use super::{SurfaceTerm, TermKind};

/// Flattens the modules of `stmts`, and writes out the sets of effects
/// (`effect_sets`).
pub fn resolve(stmts: Vec<Stmt>) -> (Vec<Stmt>, Vec<(String, Span)>) {
    resolve_with(stmts, &super::effect_sets::Sets::new(), &[])
}

/// [`resolve`] where the functions of the prelude's modules (`Code.term`,
/// `Eq.trans`) are known: statements read apart from the program, such as
/// the files before a macro, name them as the program does.
pub fn resolve_in_prelude(stmts: Vec<Stmt>) -> (Vec<Stmt>, Vec<(String, Span)>) {
    resolve_in_prelude_against(stmts, std::iter::empty())
}

/// [`resolve_in_prelude`] of statements that also use the functions `known`
/// declared elsewhere.
pub fn resolve_in_prelude_against<'a>(
    stmts: Vec<Stmt>,
    known: impl IntoIterator<Item = &'a str>,
) -> (Vec<Stmt>, Vec<(String, Span)>) {
    let mut r = Resolver::default();
    r.know(prelude_fns().iter().map(|n| n.as_str()));
    r.know(known);
    let (mut stmts, mut errors) = flatten_with(stmts, r);
    errors.extend(super::effect_sets::expand(
        &mut stmts,
        &super::effect_sets::Sets::new(),
    ));
    (stmts, errors)
}

/// The full names of the functions of the prelude's modules.
fn prelude_fns() -> &'static [String] {
    static NAMES: std::sync::OnceLock<Vec<String>> = std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        let mut names = Vec::new();
        for text in [
            crate::nibstd::PRELUDE,
            crate::nibstd::KERNEL,
            include_str!("../../../tauto-kernel/src/prelude_nat.taut"),
            include_str!("../../../tauto-kernel/src/prelude_deq.taut"),
        ] {
            if let Ok(p) = super::program::parse_program_unresolved_at(text, 0) {
                names.extend(declared(&p.stmts));
                names.extend(
                    declared_flat(&p.stmts)
                        .into_iter()
                        .filter(|n| n.contains(SEPARATOR)),
                );
            }
        }
        names
    })
}

/// [`resolve`] of one file, whose rows may name the sets `others` (those of
/// the other files of the program) too.
pub fn resolve_with(
    stmts: Vec<Stmt>,
    others: &super::effect_sets::Sets,
    known: &[String],
) -> (Vec<Stmt>, Vec<(String, Span)>) {
    let (mut stmts, mut errors) = if known.is_empty() {
        flatten(stmts)
    } else {
        let mut r = Resolver::default();
        r.know(known.iter().map(|k| k.as_str()));
        flatten_with(stmts, r)
    };
    errors.extend(super::effect_sets::expand(&mut stmts, others));
    (stmts, errors)
}

/// [`resolve`] of text that uses the functions `known` (full names such as `Bool::and`) of
/// modules declared elsewhere.
pub fn resolve_against<'a>(
    stmts: Vec<Stmt>,
    known: impl IntoIterator<Item = &'a str>,
) -> (Vec<Stmt>, Vec<(String, Span)>) {
    let mut r = Resolver::default();
    r.know(known);
    let (mut stmts, mut errors) = flatten_with(stmts, r);
    errors.extend(super::effect_sets::expand(
        &mut stmts,
        &super::effect_sets::Sets::new(),
    ));
    (stmts, errors)
}

/// One term written outside any module (`tauto eval`'s expression) with the
/// names `M::f` read as in a file that sees the functions `known`.
pub fn resolve_term_against<'a>(
    term: &SurfaceTerm,
    known: impl IntoIterator<Item = &'a str>,
) -> SurfaceTerm {
    let mut r = Resolver::default();
    r.know(known);
    let mut term = term.clone();
    r.term(&mut term, &[]);
    term
}

/// Flattens the modules of each file before its names are qualified
/// (`qualify`): a function of a module is a declaration like any other, named
/// `M::f`, and `M::f` written in a file is that name, so that two files
/// declaring `M::f` (or a file and the prelude) are told apart as two files
/// declaring `f` are. `known` are the full names (`M::f`) the prelude
/// declares; a pattern that writes one of `ctors` alone matches it.
pub fn flatten_files<'a>(
    files: &mut [Vec<Stmt>],
    known: impl IntoIterator<Item = &'a str>,
    ctors: &HashSet<String>,
) -> Vec<(String, Span)> {
    let mut all: Vec<String> = known.into_iter().map(str::to_string).collect();
    for f in files.iter() {
        all.extend(declared(f));
        all.extend(declared_flat(f));
    }
    let mut errors = Vec::new();
    for f in files.iter_mut() {
        let mut r = Resolver::default();
        r.know(all.iter().map(|k| k.as_str()));
        r.program_ctors = ctors.clone();
        let (stmts, mut e) = flatten_with(std::mem::take(f), r);
        *f = stmts;
        errors.append(&mut e);
    }
    errors
}

fn flatten(stmts: Vec<Stmt>) -> (Vec<Stmt>, Vec<(String, Span)>) {
    if !has_module(&stmts) {
        return (stmts, Vec::new());
    }
    flatten_with(stmts, Resolver::default())
}

fn flatten_with(stmts: Vec<Stmt>, mut r: Resolver) -> (Vec<Stmt>, Vec<(String, Span)>) {
    r.classes = stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Class(c) => Some(c.name.clone()),
            _ => None,
        })
        .collect();
    r.collect(&stmts, &mut Vec::new());
    let mut out = Vec::new();
    r.flatten(stmts, &mut Vec::new(), &mut out);
    (out, r.errors.into_inner())
}

fn has_module(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Module { .. } | Stmt::Syntax { .. } => true,
        // A name a `syntax!` made, under the module of its name.
        Stmt::Fn(f) => f.name.contains(SEPARATOR),
        _ => false,
    })
}

#[derive(Default)]
struct Resolver {
    /// Every module, by its full path (`A::B`).
    modules: HashSet<String>,
    /// Every function in a module, by its full name (`A::B::f`).
    fns: HashSet<String>,
    /// Every type in a module, by its full name (`A::T`).
    types: HashSet<String>,
    /// The constructors of the types in a module, by the module and the short
    /// name (`A::C`), each with its full name (`A::T::C`); a short name two types
    /// of one module share is `None`, written `T::C`.
    ctors: std::collections::HashMap<String, Option<String>>,
    /// Every class: its members are the flat names `Class::member`, so a
    /// module of the same name would put its functions among them.
    classes: HashSet<String>,
    errors: RefCell<Vec<(String, Span)>>,
    /// The constructors of the program: a pattern that writes one alone
    /// matches it and binds nothing (the names are not qualified yet).
    program_ctors: HashSet<String>,
    /// Names bound in the current lexical scope, newest last.
    locals: RefCell<Vec<String>>,
}

/// The full names of the functions and theorems the modules of `stmts` declare: what another file
/// of the program may name.
pub fn declared(stmts: &[Stmt]) -> Vec<String> {
    let mut r = Resolver::default();
    r.collect(stmts, &mut Vec::new());
    r.fns.into_iter().collect()
}

/// The names of functions and theorems of `stmts` that are already full (`M::f`).
pub fn declared_flat(stmts: &[Stmt]) -> Vec<String> {
    let mut names = Vec::new();
    for s in stmts {
        match s {
            Stmt::Fn(f) => names.push(f.name.clone()),
            Stmt::Theorem(t) | Stmt::Def(t) => names.push(t.name.clone()),
            Stmt::Extern { fns, .. } => names.extend(fns.iter().map(|f| f.name.clone())),
            _ => {}
        }
    }
    names.retain(|n| n.contains(SEPARATOR));
    names
}

fn join(path: &[String], name: &str) -> String {
    if path.is_empty() {
        name.to_string()
    } else {
        format!("{}{SEPARATOR}{name}", path.join(SEPARATOR))
    }
}

impl Resolver {
    /// Takes the full names `known` (`M::f`) as declared elsewhere.
    fn know<'a>(&mut self, known: impl IntoIterator<Item = &'a str>) {
        for name in known {
            let mut at = 0;
            while let Some(i) = name[at..].find(SEPARATOR) {
                self.modules.insert(name[..at + i].to_string());
                at += i + SEPARATOR.len();
            }
            if at > 0 {
                self.fns.insert(name.to_string());
            }
        }
    }

    fn collect(&mut self, stmts: &[Stmt], path: &mut Vec<String>) {
        for s in stmts {
            match s {
                Stmt::Module { name, items, span } => {
                    let full = join(path, name);
                    if self.classes.contains(&full) {
                        self.errors.borrow_mut().push((
                            msg!("surface-module-collides-with-class", name = &full).to_string(),
                            *span,
                        ));
                    }
                    // A module may be opened again: its blocks merge.
                    self.modules.insert(full);
                    path.push(name.clone());
                    self.collect(items, path);
                    path.pop();
                }
                // The names a `syntax!` makes live under the module of its name.
                Stmt::Syntax { name, .. } => {
                    self.know([format!("{}{SEPARATOR}parse", join(path, name)).as_str()]);
                }
                Stmt::Fn(f) if path.is_empty() && f.name.contains(SEPARATOR) => {
                    self.know([f.name.as_str()]);
                }
                Stmt::Fn(f) if !path.is_empty() => {
                    self.fns.insert(join(path, &f.name));
                }
                Stmt::Theorem(t) | Stmt::Def(t) if !path.is_empty() => {
                    self.fns.insert(join(path, &t.name));
                }
                Stmt::Mutual { items, .. } if !path.is_empty() => self.collect(items, path),
                Stmt::Attributed { stmt, .. } if !path.is_empty() => {
                    self.collect(std::slice::from_ref(&**stmt), path)
                }
                Stmt::Extern { fns, .. } if !path.is_empty() => {
                    for f in fns {
                        self.fns.insert(join(path, &f.name));
                    }
                }
                Stmt::Struct(d) | Stmt::Enum(d) if !path.is_empty() => {
                    let ctors: Vec<&str> = d
                        .constructors
                        .iter()
                        .filter(|c| c.name != d.name)
                        .map(|c| c.name.as_str())
                        .collect();
                    self.type_in(path, &d.name, &ctors);
                }
                Stmt::Inductive(d) if !path.is_empty() => {
                    let ctors: Vec<&str> = d.constructors.iter().map(|c| c.name.as_str()).collect();
                    self.type_in(path, &d.name, &ctors);
                }
                _ => {}
            }
        }
    }

    /// Takes the type `name` of the module `path`, with its constructors `ctors`.
    fn type_in(&mut self, path: &[String], name: &str, ctors: &[&str]) {
        let full = join(path, name);
        self.fns.insert(full.clone());
        self.types.insert(full.clone());
        for c in ctors {
            let ctor = format!("{full}{SEPARATOR}{c}");
            self.fns.insert(ctor.clone());
            self.ctors
                .entry(join(path, c))
                .and_modify(|v| *v = None)
                .or_insert(Some(ctor));
        }
    }

    fn flatten(&self, stmts: Vec<Stmt>, path: &mut Vec<String>, out: &mut Vec<Stmt>) {
        for s in stmts {
            match s {
                Stmt::Module { name, items, .. } => {
                    path.push(name);
                    self.scoped(|| self.flatten(items, path, out));
                    path.pop();
                }
                mut s => {
                    self.scoped(|| self.stmt(&mut s, path));
                    if !path.is_empty() {
                        Self::rename(&mut s, path);
                    }
                    out.push(s);
                }
            }
        }
    }

    fn fn_decl(&self, f: &mut FnDecl, path: &[String]) {
        self.scoped(|| {
            self.bind(&f.generics, path, f.span);
            self.bind(&f.params, path, f.span);
            // The types written in the signature may be named under a module
            // (`m.Answer` of a `syntax!`).
            for ty in f.param_types.iter_mut().flatten() {
                self.term(ty, path);
            }
            if let Some(r) = &mut f.result {
                self.term(r, path);
            }
            self.term(&mut f.body, path);
        })
    }

    fn rename(s: &mut Stmt, path: &[String]) {
        match s {
            Stmt::Fn(f) => f.name = join(path, &f.name),
            Stmt::Theorem(t) | Stmt::Def(t) => t.name = join(path, &t.name),
            Stmt::Extern { fns, .. } => {
                for f in fns {
                    f.name = join(path, &f.name);
                }
            }
            Stmt::Mutual { items, .. } => {
                for i in items {
                    Self::rename(i, path);
                }
            }
            Stmt::Attributed { stmt, .. } => Self::rename(stmt, path),
            Stmt::Struct(d) | Stmt::Enum(d) => {
                let full = join(path, &d.name);
                for c in &mut d.constructors {
                    c.name = if c.name == d.name {
                        full.clone()
                    } else {
                        format!("{full}{SEPARATOR}{}", c.name)
                    };
                }
                d.name = full;
            }
            Stmt::Inductive(d) => {
                let full = join(path, &d.name);
                for c in &mut d.constructors {
                    c.name = format!("{full}{SEPARATOR}{}", c.name);
                }
                d.name = full;
            }
            _ => {}
        }
    }

    /// The full name of `name` written in the module `path`: the innermost
    /// module that has it, then the outer ones, then the top level.
    fn name(&self, name: &str, path: &[String]) -> String {
        if self.locals.borrow().iter().any(|bound| bound == name) {
            return name.to_string();
        }
        for n in (1..=path.len()).rev() {
            let full = join(&path[..n], name);
            if self.fns.contains(&full) {
                return full;
            }
            if let Some(Some(ctor)) = self.ctors.get(&full) {
                return ctor.clone();
            }
        }
        name.to_string()
    }

    /// The full name of a name written with dots (`M::T::C`, `T::C` inside
    /// `M`): its first part a module or a type of a module.
    fn dotted_name(&self, parts: &[&str], path: &[String]) -> Option<String> {
        if self.locals.borrow().iter().any(|bound| bound == parts[0]) {
            return None;
        }
        let first = match self.module(parts[0], path) {
            Some(m) => m,
            None => {
                let t = self.name(parts[0], path);
                self.types.contains(&t).then_some(t)?
            }
        };
        let mut full = first;
        for p in &parts[1..] {
            full = format!("{full}{SEPARATOR}{p}");
        }
        Some(full)
    }

    /// A constructor's or a struct's name as written in a pattern or a
    /// record, read in the module `path`.
    fn ctor_name(&self, n: &mut String, path: &[String]) {
        let parts: Vec<&str> = n.split(SEPARATOR).collect();
        let full = if parts.len() > 1 {
            self.dotted_name(&parts, path)
        } else {
            Some(self.name(n, path))
        };
        if let Some(full) = full {
            *n = full;
        }
    }

    fn pattern(&self, p: &mut Pattern, path: &[String]) {
        match p {
            Pattern::Ctor { name, args } => {
                // `@a p`: a label, which names no declaration.
                if !name.starts_with('@') {
                    self.ctor_name(name, path);
                }
                for a in args {
                    self.pattern(a, path);
                }
            }
            Pattern::Record { name, fields } => {
                self.ctor_name(name, path);
                for (_, f) in fields {
                    self.pattern(f, path);
                }
            }
            Pattern::Tuple(items) => {
                for a in items {
                    self.pattern(a, path);
                }
            }
            // A constructor without fields, written bare (`C` of `M::T::C`).
            Pattern::Bind(n) => {
                let full = self.name(n, path);
                if full != *n && self.ctors.values().any(|c| c.as_deref() == Some(&full)) {
                    *p = Pattern::Ctor {
                        name: full,
                        args: Vec::new(),
                    };
                }
            }
            _ => {}
        }
    }

    /// The full path of the module `m` written in `path`.
    fn module(&self, m: &str, path: &[String]) -> Option<String> {
        for n in (0..=path.len()).rev() {
            let full = join(&path[..n], m);
            if self.modules.contains(&full) {
                return Some(full);
            }
        }
        None
    }

    /// `A::B` written as a chain of fields over a name.
    fn dotted(t: &SurfaceTerm) -> Option<Vec<&str>> {
        match &*t.kind {
            TermKind::Var(n) => Some(vec![n.as_str()]),
            TermKind::Field { base, name } => {
                let mut v = Self::dotted(base)?;
                v.push(name.as_str());
                Some(v)
            }
            _ => None,
        }
    }

    fn check_local(&self, name: &str, path: &[String], span: Span) {
        if self.module(name, path).is_some() {
            self.errors.borrow_mut().push((
                msg!("surface-name-of-a-module", name = name).to_string(),
                span,
            ));
        }
    }

    fn scoped(&self, f: impl FnOnce()) {
        let depth = self.locals.borrow().len();
        f();
        self.locals.borrow_mut().truncate(depth);
    }

    fn bind(&self, names: &[String], path: &[String], span: Span) {
        for name in names {
            if self.program_ctors.contains(name) {
                continue;
            }
            self.check_local(name, path, span);
            self.locals.borrow_mut().push(name.clone());
        }
    }

    fn pattern_names(pattern: &Pattern, names: &mut Vec<String>) {
        match pattern {
            Pattern::Bind(name) => names.push(name.clone()),
            Pattern::Ctor { args, .. } => {
                for arg in args {
                    Self::pattern_names(arg, names);
                }
            }
            Pattern::Record { fields, .. } => {
                for (_, field) in fields {
                    Self::pattern_names(field, names);
                }
            }
            Pattern::Tuple(items) => {
                for item in items {
                    Self::pattern_names(item, names);
                }
            }
            _ => {}
        }
    }

    fn stmt(&self, s: &mut Stmt, path: &[String]) {
        match s {
            Stmt::Let {
                name, ty, value, ..
            }
            | Stmt::Var {
                name, ty, value, ..
            } => {
                self.check_local(name, path, value.span);
                if let Some(ty) = ty {
                    self.term(ty, path);
                }
                self.term(value, path);
                self.locals.borrow_mut().push(name.clone());
            }
            Stmt::Assign { value, .. } => self.term(value, path),
            Stmt::Fn(f) => self.fn_decl(f, path),
            Stmt::Class(c) => {
                for m in &mut c.methods {
                    self.fn_decl(m, path);
                }
                for l in &mut c.laws {
                    let mut t = Stmt::Theorem(l.theorem.clone());
                    self.stmt(&mut t, path);
                    if let Stmt::Theorem(t) = t {
                        l.theorem = t;
                    }
                }
            }
            Stmt::Instance(i) => {
                for m in &mut i.methods {
                    self.fn_decl(m, path);
                }
                for l in &mut i.laws {
                    let mut t = Stmt::Theorem(l.theorem.clone());
                    self.stmt(&mut t, path);
                    if let Stmt::Theorem(t) = t {
                        l.theorem = t;
                    }
                }
            }
            Stmt::Theorem(t) | Stmt::Def(t) => self.scoped(|| {
                for (n, ty) in &mut t.params {
                    self.term(ty, path);
                    self.bind(std::slice::from_ref(n), path, t.span);
                }
                self.term(&mut t.ty, path);
                if let Some(b) = &mut t.body {
                    self.term(b, path);
                }
                if let Some(d) = &mut t.decreasing_by {
                    self.term(d, path);
                }
            }),
            Stmt::Inductive(d) => self.scoped(|| {
                for (n, ty) in &mut d.params {
                    self.term(ty, path);
                    self.bind(std::slice::from_ref(n), path, d.span);
                }
                self.term(&mut d.sort, path);
                for c in &mut d.constructors {
                    self.scoped(|| {
                        for (n, ty) in &mut c.params {
                            self.term(ty, path);
                            self.bind(std::slice::from_ref(n), path, d.span);
                        }
                        self.term(&mut c.result, path);
                    });
                }
            }),
            Stmt::Struct(d) | Stmt::Enum(d) => self.scoped(|| {
                self.bind(&d.generics, path, d.span);
                for c in &mut d.constructors {
                    for (_, ty) in &mut c.fields {
                        self.term(ty, path);
                    }
                }
            }),
            Stmt::Attributed { stmt, .. } => self.stmt(stmt, path),
            Stmt::While { condition, body } => {
                self.term(condition, path);
                self.term(body, path)
            }
            Stmt::Return(Some(e)) | Stmt::Expr(e) => self.term(e, path),
            Stmt::Mutual { items, .. } => {
                for i in items {
                    self.stmt(i, path);
                }
            }
            _ => {}
        }
    }

    fn term(&self, t: &mut SurfaceTerm, path: &[String]) {
        // A qualified name: `M::f`, `M::N::f`, one name.
        if let TermKind::Var(n) = &*t.kind
            && n.contains(SEPARATOR)
        {
            let parts: Vec<&str> = n.split(SEPARATOR).collect();
            if let Some(full) = self.dotted_name(&parts, path) {
                t.kind = Arc::new(TermKind::Var(full));
            }
            return;
        }
        // `.` takes a field only: `M::f` over a module is written `M::f`.
        if let TermKind::Field { .. } = &*t.kind
            && let Some(parts) = Self::dotted(t)
            && let Some(full) = self.dotted_name(&parts, path)
        {
            self.errors.borrow_mut().push((
                msg!("surface-dot-names-a-declaration", name = parts.join(SEPARATOR)).to_string(),
                t.span,
            ));
            t.kind = Arc::new(TermKind::Var(full));
            return;
        }
        match Arc::make_mut(&mut t.kind) {
            TermKind::Var(n) => *n = self.name(n, path),
            TermKind::App {
                function,
                arguments,
            } => {
                self.term(function, path);
                for a in arguments {
                    self.term(a, path);
                }
            }
            TermKind::Lam {
                params,
                body,
                types,
            } => self.scoped(|| {
                for ty in types.iter_mut().flatten() {
                    self.term(ty, path);
                }
                self.bind(params, path, t.span);
                self.term(body, path);
            }),
            TermKind::Pi { params, result, .. } => self.scoped(|| {
                for (n, ty) in params.iter_mut() {
                    self.term(ty, path);
                    if let Some(n) = n {
                        self.bind(std::slice::from_ref(n), path, t.span);
                    }
                }
                self.term(result, path);
            }),
            TermKind::Exists {
                binder,
                domain,
                body,
            } => self.scoped(|| {
                self.term(domain, path);
                self.bind(std::slice::from_ref(binder), path, t.span);
                self.term(body, path);
            }),
            TermKind::Union(ts) | TermKind::Product(ts) | TermKind::Tuple(ts) => {
                for x in ts {
                    self.term(x, path);
                }
            }
            TermKind::Ascribe { term, ty } => {
                self.term(term, path);
                self.term(ty, path);
            }
            TermKind::FnKind { ty, .. } => self.term(ty, path),
            TermKind::Step(step) => {
                self.term(&mut step.arg, path);
                if let Some(b) = &mut step.before {
                    self.term(b, path);
                }
                for arm in &mut step.arms {
                    self.scoped(|| {
                        for (n, ty) in &mut arm.binders {
                            self.term(ty, path);
                            self.bind(std::slice::from_ref(n), path, arm.span);
                        }
                        self.term(&mut arm.goal, path);
                        self.term(&mut arm.body, path);
                    });
                }
            }
            TermKind::BorrowLam { lam, .. } => self.term(lam, path),
            TermKind::Borrow { term, .. } | TermKind::Tagged { term, .. } => self.term(term, path),
            TermKind::Record { name, fields, base } => {
                self.ctor_name(name, path);
                for (_, v) in fields {
                    self.term(v, path);
                }
                if let Some(b) = base {
                    self.term(b, path);
                }
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.term(condition, path);
                self.term(then, path);
                if let Some(o) = otherwise {
                    self.term(o, path);
                }
            }
            TermKind::Field { base, .. } => self.term(base, path),
            TermKind::Perform { args, .. } => {
                for a in args {
                    self.term(a, path);
                }
            }
            TermKind::Budget { steps, body, .. } => {
                self.term(steps, path);
                self.term(body, path);
            }
            TermKind::Block(stmts) => self.scoped(|| {
                for s in stmts {
                    self.stmt(s, path);
                }
            }),
            TermKind::Handle { body, handlers } => {
                self.term(body, path);
                for h in handlers {
                    match h {
                        Handler::Return { pattern, body } => self.scoped(|| {
                            self.pattern(pattern, path);
                            let mut names = Vec::new();
                            Self::pattern_names(pattern, &mut names);
                            self.bind(&names, path, body.span);
                            self.term(body, path);
                        }),
                        Handler::Operation {
                            patterns,
                            cont,
                            body,
                            guard,
                            ..
                        } => self.scoped(|| {
                            let mut names = Vec::new();
                            for pattern in patterns {
                                Self::pattern_names(pattern, &mut names);
                            }
                            names.extend(cont.iter().cloned());
                            self.bind(&names, path, body.span);
                            if let Some(g) = guard {
                                self.term(g, path);
                            }
                            self.term(body, path);
                        }),
                    }
                }
            }
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } => {
                self.term(scrutinee, path);
                if let Some(result) = result {
                    self.term(result, path);
                }
                for a in arms {
                    self.scoped(|| {
                        self.pattern(&mut a.pattern, path);
                        let mut names = Vec::new();
                        Self::pattern_names(&a.pattern, &mut names);
                        names.extend(binder.iter().cloned());
                        self.bind(&names, path, a.body.span);
                        if let Some(g) = &mut a.guard {
                            self.term(g, path);
                        }
                        if let Some(goal) = &mut a.goal {
                            self.term(goal, path);
                        }
                        self.term(&mut a.body, path);
                    });
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::{program::parse_program_as_written, walk};

    fn names(source: &str) -> Vec<String> {
        let program = parse_program_as_written(&source).unwrap();
        assert!(program.errors.is_empty(), "{:?}", program.errors);
        let Stmt::Fn(function) = &program.stmts[1] else {
            panic!("expected M::g")
        };
        let mut body = function.body.clone();
        let mut names = Vec::new();
        walk::term(&mut body, &mut |term| {
            if let TermKind::Var(name) = &*term.kind {
                names.push(name.clone());
            }
        });
        names
    }

    #[test]
    fn local_initializers_and_following_uses_have_different_scopes() {
        assert_eq!(
            names(r#"module M { fn f(): i64 { 1 }
fn g(): i64 { let f := f()
f } }"#),
            ["M::f", "f"]
        );
        assert_eq!(
            names(r#"module M { fn f(): i64 { 1 }
fn g(): i64 { var f := f()
f } }"#),
            ["M::f", "f"]
        );
    }

    #[test]
    fn lambda_and_block_bindings_do_not_escape() {
        assert_eq!(
            names(r#"module M { fn f(): i64 { 1 }
fn g(): i64 { let callback := (f) => f()
f() } }"#),
            ["f", "M::f"]
        );
        assert_eq!(
            names(r#"module M { fn f(): i64 { 1 }
fn g(): i64 { { let f := 2
f }
f() } }"#),
            ["f", "M::f"]
        );
    }

    #[test]
    fn match_patterns_bind_guards_and_bodies_only_in_their_arm() {
        assert_eq!(
            names(r#"module M { fn f(): i64 { 1 }
fn g(): i64 { match Some(2) { Some(f) if f == 2 => f
None => f() } } }"#),
            ["Some", "==", "f", "f", "M::f"]
        );
    }

    #[test]
    fn handler_patterns_and_continuations_are_local() {
        assert_eq!(
            names(r#"module M { fn f(): i64 { 1 }
fn g(): i64 { handle { 2 } with { return f => f } } }"#),
            ["f"]
        );
        assert_eq!(
            names(r#"module M { fn f(): i64 { 1 }
fn g(): i64 { handle { perform ask() } with { ask(), f => f(42) } } }"#),
            ["f"]
        );
    }

    #[test]
    fn arguments_do_not_hide_names_in_the_next_function() {
        let program = parse_program_as_written(r#"module M { fn f(): i64 { 1 }
fn g(f: i64): i64 { f }
fn h(): i64 { f() } }"#)
        .unwrap();
        assert!(program.errors.is_empty());
        let Stmt::Fn(g) = &program.stmts[1] else {
            panic!("expected g")
        };
        assert_eq!(*g.body.kind, TermKind::Var("f".into()));
        let Stmt::Fn(h) = &program.stmts[2] else {
            panic!("expected h")
        };
        let mut body = h.body.clone();
        let mut references = Vec::new();
        walk::term(&mut body, &mut |t| {
            if let TermKind::Var(n) = &*t.kind {
                references.push(n.clone());
            }
        });
        assert_eq!(references, ["M::f"]);
    }
}
