//! Names with the scopes they carry.
//!
//! An expansion's output is read back into the surface syntax, where a name is
//! a string. A name a macro made carries the expansions that made it after a
//! separator: `tmp\u{1}3`. [`crate::macros::resolve`] gives each such
//! binder a name of its own and ties each such name to the binder that
//! matches, then no name carries one.

/// Between a name and the scopes it carries.
pub const SEP: char = '\u{1}';

/// `name` with `scopes` (sorted, each once); the name alone when there are none.
pub fn mark(name: &str, scopes: &[u64]) -> String {
    if scopes.is_empty() {
        return name.to_string();
    }
    let mut sorted = scopes.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    let list: Vec<String> = sorted.iter().map(u64::to_string).collect();
    format!("{name}{SEP}{}", list.join(","))
}

/// The name and the scopes of a marked name (`""` for none).
pub fn split(name: &str) -> (&str, &str) {
    split_on(name, SEP.encode_utf8(&mut [0; 4]))
}

/// [`split`] with another separator (`totes/macros` reads marks that are
/// written out in source).
fn split_on<'a>(name: &'a str, sep: &str) -> (&'a str, &'a str) {
    name.split_once(sep).unwrap_or((name, ""))
}

pub fn scopes_of(name: &str) -> Vec<u64> {
    split(name)
        .1
        .split(',')
        .filter_map(|s| s.parse().ok())
        .collect()
}

/// `scopes` with `s` removed when it is there, added when it is not.
pub fn flip(scopes: &[u64], s: u64) -> Vec<u64> {
    let mut out: Vec<u64> = scopes.iter().copied().filter(|x| *x != s).collect();
    if out.len() == scopes.len() {
        out.push(s);
    }
    out.sort_unstable();
    out
}

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::surface::{
    DataDecl, EffectDecl, FnDecl, Handler, InductiveDecl, MatchArm, Pattern, Stmt, SurfaceTerm,
    TermKind, TheoremDecl,
};

/// Gives each name its binder: a name a
/// macro made is tied to the binder of the same name that the same expansion
/// made, and no other; each such binder gets a name of its own (`tmp#3`).
/// What no binder of the expansion matches is a global, and keeps its name:
/// a local of the caller that has that name is renamed so it does not take it.
/// `ctors` are the names a bare name in a pattern may be instead of a binder.
pub fn resolve(stmts: Vec<Stmt>, ctors: &HashSet<String>) -> Vec<Stmt> {
    resolve_with(stmts, ctors, SEP.encode_utf8(&mut [0; 4]))
}

/// Where a global a macro wrote comes from, by the scopes it carries and its
/// name: the file of the macro whose expansion wrote it, and the declaration
/// that file means by the name when that is not the name itself.
pub type Seeing<'s> = &'s dyn Fn(&[u64], &str) -> Option<(usize, Option<String>)>;

/// [`resolve`], with each global a macro wrote read as its file reads it:
/// a name means what it means where the macro is written, not what the
/// files around the call make of it.
pub fn resolve_seeing(stmts: Vec<Stmt>, ctors: &HashSet<String>, seeing: Seeing) -> Vec<Stmt> {
    resolve_full(stmts, ctors, SEP.encode_utf8(&mut [0; 4]), Some(seeing))
}

/// [`resolve`] for names whose scopes follow `sep`.
pub fn resolve_with(stmts: Vec<Stmt>, ctors: &HashSet<String>, sep: &str) -> Vec<Stmt> {
    resolve_full(stmts, ctors, sep, None)
}

fn resolve_full(
    stmts: Vec<Stmt>,
    ctors: &HashSet<String>,
    sep: &str,
    seeing: Option<Seeing>,
) -> Vec<Stmt> {
    let mut probe = stmts.clone();
    let mut first = Resolver::new(ctors, sep, HashSet::new());
    first.seeing = seeing;
    first.top(&mut probe);
    if first.captured.is_empty() {
        return probe;
    }
    let mut again = Resolver::new(ctors, sep, first.captured);
    again.seeing = seeing;
    let mut out = stmts;
    again.top(&mut out);
    out
}

struct Binder {
    plain: String,
    marks: String,
    unique: String,
    id: usize,
}

struct Resolver<'c> {
    ctors: &'c HashSet<String>,
    seeing: Option<Seeing<'c>>,
    /// The file of the macro that wrote the global just resolved.
    origin: Option<usize>,
    sep: &'c str,
    env: Vec<Binder>,
    /// Declarations made by an expansion, by name and marks.
    globals: HashMap<(String, String), String>,
    /// Binders (by their number in the walk) that a name of an expansion would
    /// have been taken by.
    captured: HashSet<usize>,
    rename: HashSet<usize>,
    counter: usize,
    unique: usize,
}

impl<'c> Resolver<'c> {
    fn new(ctors: &'c HashSet<String>, sep: &'c str, rename: HashSet<usize>) -> Self {
        Resolver {
            ctors,
            seeing: None,
            origin: None,
            sep,
            env: Vec::new(),
            globals: HashMap::new(),
            captured: HashSet::new(),
            rename,
            counter: 0,
            unique: 0,
        }
    }

    fn bind(&mut self, name: &str) -> String {
        let (plain, marks) = split_on(name, self.sep);
        let id = self.counter;
        self.counter += 1;
        let unique = if !marks.is_empty() {
            self.unique += 1;
            format!("{plain}#{}", self.unique)
        } else if self.rename.contains(&id) {
            self.unique += 1;
            format!("{plain}#r{}", self.unique)
        } else {
            plain.to_string()
        };
        self.env.push(Binder {
            plain: plain.to_string(),
            marks: marks.to_string(),
            unique: unique.clone(),
            id,
        });
        unique
    }

    fn reference(&mut self, name: &str) -> String {
        let (plain, marks) = split_on(name, self.sep);
        if let Some((head, rest)) = plain.split_once("::") {
            // A function of a module (`Text::of_nat`) means, as a whole,
            // what the macro's file means by it: the prelude's builtin
            // where the file reads it so, whatever the caller imports.
            if !marks.is_empty() && !self.env.iter().any(|b| b.plain == head) {
                if let Some((file, to)) = self.seeing.and_then(|f| {
                    let scopes: Vec<u64> =
                        marks.split(',').filter_map(|s| s.parse().ok()).collect();
                    f(&scopes, plain)
                }) {
                    self.origin = Some(file);
                    if let Some(to) = to {
                        return to;
                    }
                }
            }
            let head = self.reference_one(head, marks);
            return format!("{head}::{rest}");
        }
        self.reference_one(plain, marks)
    }

    fn reference_one(&mut self, plain: &str, marks: &str) -> String {
        if let Some(b) = self
            .env
            .iter()
            .rev()
            .find(|b| b.plain == plain && b.marks == marks)
        {
            return b.unique.clone();
        }
        if !marks.is_empty() {
            if let Some(u) = self.globals.get(&(plain.to_string(), marks.to_string())) {
                return u.clone();
            }
            // A global, read as the macro's file reads it: the file goes with
            // the name (`SurfaceTerm::origin`), and a name the file means by
            // another name is written so, a full name no local of the caller has.
            if let Some((file, to)) = self.seeing.and_then(|f| {
                let scopes: Vec<u64> = marks.split(',').filter_map(|s| s.parse().ok()).collect();
                f(&scopes, plain)
            }) {
                self.origin = Some(file);
                if let Some(to) = to.filter(|to| to != plain) {
                    return to;
                }
            }
            // A global; a local of the caller with this name must not take it.
            for b in &self.env {
                if b.plain == plain && b.marks.is_empty() {
                    self.captured.insert(b.id);
                }
            }
        }
        plain.to_string()
    }

    fn mark(&self) -> usize {
        self.env.len()
    }

    fn pop(&mut self, mark: usize) {
        self.env.truncate(mark);
    }

    /// Declarations an expansion made at the top, and in `mutual`/`module`.
    fn collect_globals(&mut self, stmts: &mut [Stmt]) {
        for s in stmts {
            let declare = |this: &mut Self, name: &mut String| {
                let (plain, marks) = split_on(name, this.sep);
                if !marks.is_empty() {
                    this.unique += 1;
                    let unique = format!("{plain}#{}", this.unique);
                    this.globals
                        .insert((plain.to_string(), marks.to_string()), unique.clone());
                    *name = unique;
                }
            };
            match s {
                Stmt::Fn(f) => declare(self, &mut f.name),
                Stmt::Theorem(d) | Stmt::Def(d) => declare(self, &mut d.name),
                Stmt::Struct(d) | Stmt::Enum(d) => {
                    declare(self, &mut d.name);
                    for c in &mut d.constructors {
                        declare(self, &mut c.name);
                    }
                }
                Stmt::Effect(e) => declare(self, &mut e.name),
                Stmt::Inductive(d) => declare(self, &mut d.name),
                Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                    self.collect_globals(items)
                }
                _ => {}
            }
        }
    }

    fn top(&mut self, stmts: &mut [Stmt]) {
        self.collect_globals(stmts);
        for s in stmts {
            self.stmt(s);
        }
    }

    fn stmts(&mut self, stmts: &mut [Stmt]) {
        let mark = self.mark();
        for s in stmts {
            self.stmt(s);
        }
        self.pop(mark);
    }

    fn opt(&mut self, t: &mut Option<SurfaceTerm>) {
        if let Some(t) = t {
            self.term(t);
        }
    }

    fn stmt(&mut self, s: &mut Stmt) {
        match s {
            Stmt::Attributed { arg, stmt, .. } => {
                self.term(arg);
                self.stmt(stmt);
            }
            Stmt::Called { call, .. } => self.term(call),
            Stmt::Let {
                name, ty, value, ..
            } => {
                self.opt(ty);
                self.term(value);
                *name = self.bind(name);
            }
            Stmt::Var {
                name, ty, value, ..
            } => {
                self.opt(ty);
                self.term(value);
                *name = self.bind(name);
            }
            Stmt::Assign { name, value, .. } => {
                self.term(value);
                *name = self.reference(name);
            }
            Stmt::Fn(f) => self.fn_decl(f),
            Stmt::Theorem(d) | Stmt::Def(d) => self.theorem(d),
            Stmt::While { condition, body } => {
                self.term(condition);
                self.term(body);
            }
            Stmt::Return(e) => self.opt(e),
            Stmt::Expr(e) => self.term(e),
            Stmt::Struct(d) | Stmt::Enum(d) => self.data(d),
            Stmt::Effect(e) => self.effect(e),
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for i in items {
                    self.stmt(i);
                }
            }
            Stmt::Inductive(d) => self.inductive(d),
            Stmt::Extern { .. }
            | Stmt::Class(_)
            | Stmt::Instance(_)
            | Stmt::Import { .. }
            | Stmt::Syntax { .. }
            | Stmt::Macro { .. }
            | Stmt::Other(..) => {}
        }
    }

    fn fn_decl(&mut self, f: &mut FnDecl) {
        f.name = self.reference(&f.name);
        let mark = self.mark();
        for i in 0..f.params.len() {
            if let Some(t) = f.param_types.get_mut(i) {
                self.opt(t);
            }
            f.params[i] = self.bind(&f.params[i].clone());
        }
        self.opt(&mut f.result);
        self.term(&mut f.body);
        self.pop(mark);
    }

    fn theorem(&mut self, d: &mut TheoremDecl) {
        d.name = self.reference(&d.name);
        let mark = self.mark();
        for (n, t) in &mut d.params {
            self.term(t);
            *n = self.bind(n);
        }
        self.term(&mut d.ty);
        self.opt(&mut d.body);
        self.pop(mark);
    }

    fn data(&mut self, d: &mut DataDecl) {
        d.name = self.reference(&d.name);
        for c in &mut d.constructors {
            c.name = self.reference(&c.name);
            for (_, t) in &mut c.fields {
                self.term(t);
            }
        }
    }

    fn effect(&mut self, e: &mut EffectDecl) {
        e.name = self.reference(&e.name);
        for p in e.params.iter_mut() {
            self.opt(p);
        }
        self.opt(&mut e.result);
    }

    fn inductive(&mut self, d: &mut InductiveDecl) {
        d.name = self.reference(&d.name);
        let mark = self.mark();
        for (n, t) in &mut d.params {
            self.term(t);
            *n = self.bind(n);
        }
        self.term(&mut d.sort);
        for c in &mut d.constructors {
            c.name = self.reference(&c.name);
            let inner = self.mark();
            for (n, t) in &mut c.params {
                self.term(t);
                *n = self.bind(n);
            }
            self.term(&mut c.result);
            self.pop(inner);
        }
        self.pop(mark);
    }

    fn pattern(&mut self, p: &mut Pattern) {
        match p {
            Pattern::Bind(n) => {
                let (plain, _) = split_on(n, self.sep);
                let is_ctor = self.ctors.contains(plain);
                if is_ctor {
                    *n = self.reference(n);
                } else {
                    *n = self.bind(n);
                }
            }
            Pattern::Ctor { name, args } => {
                // `@a p`: a label, which names no declaration.
                if !name.starts_with('@') {
                    *name = self.reference(name);
                }
                for a in args {
                    self.pattern(a);
                }
            }
            Pattern::Record { name, fields } => {
                *name = self.reference(name);
                for (_, f) in fields {
                    self.pattern(f);
                }
            }
            Pattern::Tuple(items) => {
                for a in items {
                    self.pattern(a);
                }
            }
            Pattern::Wild
            | Pattern::Int(_)
            | Pattern::Bool(_)
            | Pattern::Text(_)
            | Pattern::Other(_) => {}
        }
    }

    fn arm(&mut self, a: &mut MatchArm) {
        let mark = self.mark();
        self.pattern(&mut a.pattern);
        self.opt(&mut a.guard);
        self.opt(&mut a.goal);
        self.term(&mut a.body);
        self.pop(mark);
    }

    fn handler(&mut self, h: &mut Handler) {
        let mark = self.mark();
        match h {
            Handler::Return { pattern, body } => {
                self.pattern(pattern);
                self.term(body);
            }
            Handler::Operation {
                effect,
                patterns,
                cont,
                guard,
                body,
                ..
            } => {
                // The instance is left as a row's entries are.
                *effect = self.reference(effect);
                for p in patterns {
                    self.pattern(p);
                }
                if let Some(k) = cont {
                    *k = self.bind(k);
                }
                self.opt(guard);
                self.term(body);
            }
        }
        self.pop(mark);
    }

    /// A term, with the file of the macro that wrote the global it names
    /// (a variable, a record's type, an effect performed) kept on it.
    fn term(&mut self, t: &mut SurfaceTerm) {
        self.origin = None;
        let origin = self.names(t);
        if origin.is_some() {
            t.set_origin(origin);
        }
    }

    /// The names of `t` resolved; the file of the macro that wrote the one
    /// `t` itself names, if a macro wrote it.
    fn names(&mut self, t: &mut SurfaceTerm) -> Option<usize> {
        let mut origin = None;
        match Arc::make_mut(&mut t.kind) {
            TermKind::Var(n) => {
                *n = self.reference(n);
                origin = self.origin.take();
            }
            TermKind::Nat(_)
            | TermKind::Float(_)
            | TermKind::Text(_)
            | TermKind::Bool(_)
            | TermKind::Hole(_)
            | TermKind::Other(_)
            | TermKind::SyntaxLit(_)
            | TermKind::Row(_)
            | TermKind::Quote { .. } => {}
            TermKind::MacroCall { arg, .. } | TermKind::Splice(arg) => self.term(arg),
            TermKind::App {
                function,
                arguments,
            } => {
                self.term(function);
                for a in arguments {
                    self.term(a);
                }
            }
            TermKind::Pi { params, result, .. } => {
                let mark = self.mark();
                for (n, ty) in params {
                    self.term(ty);
                    if let Some(n) = n {
                        *n = self.bind(n);
                    }
                }
                self.term(result);
                self.pop(mark);
            }
            TermKind::Exists {
                binder,
                domain,
                body,
            } => {
                self.term(domain);
                let mark = self.mark();
                *binder = self.bind(binder);
                self.term(body);
                self.pop(mark);
            }
            TermKind::Lam {
                params,
                body,
                types,
            } => {
                for ty in types.iter_mut().flatten() {
                    self.term(ty);
                }
                let mark = self.mark();
                for p in params.iter_mut() {
                    *p = self.bind(p);
                }
                self.term(body);
                self.pop(mark);
            }
            TermKind::BorrowLam { lam, .. } => self.term(lam),
            TermKind::Union(items) | TermKind::Product(items) | TermKind::Tuple(items) => {
                for i in items {
                    self.term(i);
                }
            }
            TermKind::Tagged { term, .. }
            | TermKind::Borrow { term, .. }
            | TermKind::FnKind { ty: term, .. } => self.term(term),
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.term(condition);
                self.term(then);
                if let Some(o) = otherwise {
                    self.term(o);
                }
            }
            TermKind::Field { base, .. } => self.term(base),
            TermKind::Ascribe { term, ty } => {
                self.term(term);
                self.term(ty);
            }
            TermKind::Block(stmts) => self.stmts(stmts),
            TermKind::Perform { effect, args } => {
                self.origin = None;
                *effect = self.reference(effect);
                origin = self.origin.take();
                for a in args {
                    self.term(a);
                }
            }
            TermKind::Handle { body, handlers } => {
                self.term(body);
                for h in handlers {
                    self.handler(h);
                }
            }
            TermKind::Budget { steps, body, .. } => {
                self.term(steps);
                self.term(body);
            }
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } => {
                self.term(scrutinee);
                // The equation is bound in the arms, not in the result type.
                if let Some(r) = result {
                    self.term(r);
                }
                let mark = self.mark();
                if let Some(h) = binder {
                    *h = self.bind(h);
                }
                for a in arms {
                    self.arm(a);
                }
                self.pop(mark);
            }
            TermKind::Record { name, fields, base } => {
                self.origin = None;
                *name = self.reference(name);
                origin = self.origin.take();
                for (_, v) in fields {
                    self.term(v);
                }
                if let Some(b) = base {
                    self.term(b);
                }
            }
            // The variables an arm adds are bound in its goal and its proof.
            TermKind::Step(s) => {
                self.term(&mut s.arg);
                if let Some(b) = &mut s.before {
                    self.term(b);
                }
                for a in &mut s.arms {
                    let mark = self.mark();
                    for (n, ty) in &mut a.binders {
                        self.term(ty);
                        *n = self.bind(n);
                    }
                    self.term(&mut a.goal);
                    self.term(&mut a.body);
                    self.pop(mark);
                }
            }
        }
        origin
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn marks_round_trip() {
        assert_eq!(mark("x", &[]), "x");
        assert_eq!(mark("x", &[3, 1, 3]), "x\u{1}1,3");
        assert_eq!(split("x\u{1}1,3"), ("x", "1,3"));
        assert_eq!(scopes_of("x\u{1}1,3"), vec![1, 3]);
        assert_eq!(scopes_of("x"), Vec::<u64>::new());
    }

    #[test]
    fn flipping_adds_and_removes() {
        assert_eq!(flip(&[], 5), vec![5]);
        assert_eq!(flip(&[5], 5), Vec::<u64>::new());
        assert_eq!(flip(&[2, 5], 5), vec![2]);
    }
}
