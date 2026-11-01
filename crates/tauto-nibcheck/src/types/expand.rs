//! The expansion of classes: a constraint becomes an
//! argument for each method of the class, a method call a call of the
//! argument or of the instance's function, and an instance a function for
//! each of its methods. What follows sees no class, and checks the result
//! as it checks any program.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::sync::OnceLock;

use tauto_parol::Span;

use super::classes::{instance_fn, replace};
use super::{Ev, Kind, STRUCTURAL, TypeError, TypeReport, check_program_in, prelude_source};
use crate::surface::walk;
use crate::surface::{
    ClassDecl, Constraint, FnDecl, InstanceDecl, Program, Stmt, SurfaceTerm, TermId, TermKind,
};

/// The classes and the constrained functions of the prelude.
fn prelude_names() -> &'static (HashSet<String>, HashSet<String>) {
    static NAMES: OnceLock<(HashSet<String>, HashSet<String>)> = OnceLock::new();
    NAMES.get_or_init(|| {
        let (mut classes, mut fns) = (HashSet::new(), HashSet::new());
        for s in &prelude_source().stmts {
            match s {
                Stmt::Class(c) => {
                    classes.insert(c.name.clone());
                }
                Stmt::Fn(f) if constrained(&f.where_) => {
                    fns.insert(f.name.clone());
                }
                Stmt::Extern { fns: es, .. } => {
                    for f in es.iter().filter(|f| constrained(&f.where_)) {
                        fns.insert(f.name.clone());
                    }
                }
                _ => {}
            }
        }
        (classes, fns)
    })
}

/// Some constraint is of a class (not a structural predicate).
fn constrained(where_: &[Constraint]) -> bool {
    where_
        .iter()
        .any(|c| !STRUCTURAL.contains(&c.class.as_str()))
}

/// Whether the program declares a class, an instance or a constraint
/// (`Some(true)`), or only looks to use the std's (`Some(false)`).
fn needs_expansion(program: &Program) -> Option<bool> {
    let (classes, fns) = prelude_names();
    let mut found = false;
    let own: HashSet<&str> = program
        .stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Fn(f) => Some(f.name.as_str()),
            _ => None,
        })
        .collect();
    for s in &program.stmts {
        match s {
            Stmt::Class(_) | Stmt::Instance(_) => return Some(true),
            Stmt::Fn(f) if constrained(&f.where_) => return Some(true),
            Stmt::Struct(d) | Stmt::Enum(d) if classes.contains(&d.name) => return Some(true),
            _ => {}
        }
        let mut s = s.clone();
        walk::stmt(&mut s, &mut |t| match &*t.kind {
            TermKind::Var(n) if fns.contains(n) && !own.contains(n.as_str()) => found = true,
            TermKind::Field { base, .. } if matches!(&*base.kind, TermKind::Var(c) if classes.contains(c)) => {
                found = true
            }
            _ => {}
        });
        if found {
            return Some(false);
        }
    }
    None
}

/// The first of `Program::errors` when the program did not expand: the rest
/// are what the class-aware check found.
pub(super) const UNEXPANDED: &str = "\0unexpanded";

/// What kept `program`'s classes from expanding: the errors the class-aware
/// check finds in a program that still uses a class, or none for one whose
/// classes expanded (or that uses none).
pub fn expansion_errors(program: &Program) -> Vec<TypeError> {
    if needs_expansion(program).is_none() {
        return Vec::new();
    }
    check_program_in(program, prelude_source()).errors
}

/// What kept `program`'s indexed effects from expanding: a row of the
/// program that still writes type arguments (`fail(Text)`) was left as it is
/// because the program does not check (`indices.rs`), and these are the
/// errors that check finds. None for a program whose rows expanded.
pub fn index_expansion_errors(program: &Program) -> Vec<TypeError> {
    if super::indices::indexed_effects(program).is_empty() {
        return Vec::new();
    }
    check_program_in(program, super::prelude()).errors
}

/// `program` with its classes, instances and constraints expanded. A program
/// that does not check is returned as it is, for the checker to report on.
/// The terms the expansion makes get spans from `synthetic` on, which no
/// written term has.
pub fn expand_classes(mut program: Program, synthetic: u32) -> Program {
    expand(&mut program, &mut Vec::new(), synthetic, true);
    super::indices::expand_indices(&mut program, &mut []);
    program
}

/// [`expand_classes`] for a program read from several files: the program,
/// and the statements of each file, are expanded alike, so that a term the
/// expansion makes has one span in both.
pub fn expand_loaded(program: &mut Program, per_file: &mut [Vec<Stmt>], synthetic: u32) {
    expand(program, per_file, synthetic, false);
    super::indices::expand_indices(program, per_file);
}

/// With `report`, a program that does not check carries what was found, for
/// `check_program`; without, it is left as it is.
fn expand(program: &mut Program, per_file: &mut [Vec<Stmt>], synthetic: u32, report_errors: bool) {
    let Some(declared) = needs_expansion(program) else {
        return;
    };
    let report = check_program_in(program, prelude_source());
    if !report.errors.is_empty() {
        // A name the program binds itself (a parameter called `join`) looks
        // like a use of the std's; that it checks as it is settles it.
        if !report_errors
            || !declared
                && check_program_in(program, super::prelude())
                    .errors
                    .is_empty()
        {
            return;
        }
        let found = report.errors.iter().map(|e| (e.message.clone(), e.span));
        program.errors = std::iter::once((UNEXPANDED.to_string(), Span::new(0, 0)))
            .chain(found)
            .collect();
        return;
    }
    let mut e = Expander {
        report: &report,
        next: synthetic,
        origin: None,
        count: 0,
        spans: HashMap::new(),
    };
    program.stmts = e.stmts(std::mem::take(&mut program.stmts));
    for file in per_file {
        *file = e.stmts(std::mem::take(file));
    }
}

struct Expander<'a> {
    report: &'a TypeReport,
    next: u32,
    /// The occurrence the terms being made stand for, and their order.
    /// The program and per-file clones receive the same generated identities.
    origin: Option<(TermId, bool)>,
    count: usize,
    spans: HashMap<((TermId, bool), usize), SurfaceTerm>,
}

/// The name an instance's head gives its functions.
fn head_name(head: &SurfaceTerm) -> String {
    match &*head.kind {
        TermKind::Var(n) => n.clone(),
        TermKind::App { function, .. } => head_name(function),
        _ => String::new(),
    }
}

impl Expander<'_> {
    /// What is made from here on stands for this occurrence.
    fn from(&mut self, origin: TermId) {
        self.origin = Some((origin, false));
        self.count = 0;
    }

    fn stmts(&mut self, stmts: Vec<Stmt>) -> Vec<Stmt> {
        let mut out = Vec::new();
        for s in stmts {
            self.top(s, &mut out);
        }
        out
    }

    fn term(&mut self, kind: TermKind) -> SurfaceTerm {
        let key = (
            self.origin.expect("a generated term has an origin"),
            self.count,
        );
        self.count += 1;
        if let Some(previous) = self.spans.get(&key) {
            return previous.with_kind(kind, previous.span);
        }
        let span = Span::new(self.next, self.next + 1);
        self.next += 1;
        let term = SurfaceTerm::new(kind, span);
        self.spans.insert(key, term.clone());
        term
    }

    fn var(&mut self, name: impl Into<String>) -> SurfaceTerm {
        self.term(TermKind::Var(name.into()))
    }

    fn class(&self, name: &str) -> Option<&ClassDecl> {
        self.report.classes.get(name)
    }

    fn top(&mut self, s: Stmt, out: &mut Vec<Stmt>) {
        match s {
            Stmt::Class(_) => {}
            Stmt::Instance(i) => {
                for m in &i.methods {
                    let f = self.instance_method(&i, m);
                    out.push(Stmt::Fn(f));
                }
            }
            Stmt::Fn(mut f) => {
                self.fn_decl(&mut f);
                out.push(Stmt::Fn(f));
            }
            mut other => {
                walk::roots(&mut other, &mut |t| self.go(t));
                out.push(other);
            }
        }
    }

    /// The function an instance gives a method: `C::m@H`, over the instance's
    /// generics, asking for what the instance's `where` asks.
    fn instance_method(&mut self, i: &InstanceDecl, m: &FnDecl) -> FnDecl {
        let mut f = m.clone();
        f.name = instance_fn(&i.class, &m.name, &head_name(&i.head));
        f.span = m.span;
        f.bounds.resize(f.generics.len(), None);
        let mut bounds = i.bounds.clone();
        bounds.resize(i.generics.len(), None);
        bounds.append(&mut f.bounds);
        f.bounds = bounds;
        f.generics.splice(0..0, i.generics.iter().cloned());
        f.where_ = i.where_.clone();
        self.fn_decl(&mut f);
        f
    }

    /// A function that asks for a class takes the class's methods, after its
    /// own parameters; its body is expanded.
    fn fn_decl(&mut self, f: &mut FnDecl) {
        let mut added = Vec::new();
        for c in &f.where_ {
            let (TermKind::Var(g), Some(class)) = (&*c.ty.kind, self.class(&c.class).cloned())
            else {
                continue;
            };
            for m in &class.methods {
                added.push((
                    format!("{}::{}@{g}", class.name, m.name),
                    class.clone(),
                    m.clone(),
                    c.ty.clone(),
                ));
            }
        }
        self.origin = Some((f.body.id(), true));
        self.count = 0;
        for (name, class, m, with) in added {
            let ty = self.method_type(&class, &m, &with);
            f.params.push(name);
            f.param_types.push(Some(ty));
            f.borrows.push(None);
        }
        f.where_.retain(|c| STRUCTURAL.contains(&c.class.as_str()));
        self.go(&mut f.body);
    }

    /// A method's type with `with` for the class's parameter.
    fn method_type(&mut self, class: &ClassDecl, m: &FnDecl, with: &SurfaceTerm) -> SurfaceTerm {
        let mut params = Vec::new();
        // The method's own type generics make the dictionary polymorphic:
        // `(A: Shared, B: Type, …)` leads.
        for (n, g) in m.generics.iter().enumerate() {
            let kind = match m.bounds.get(n).cloned().flatten() {
                None => "affine".to_string(),
                Some(b) => match Kind::parse(&b) {
                    Some(_) => b,
                    None => continue,
                },
            };
            let kind = self.term(TermKind::Var(kind));
            params.push((Some(g.clone()), kind));
        }
        for (n, t) in m.param_types.iter().enumerate() {
            let t = match t {
                Some(t) => replace(t, &class.param, with),
                None => self.unit(),
            };
            let t = match m.borrows.get(n).copied().flatten() {
                Some(mutable) => self.term(TermKind::Borrow {
                    mutable,
                    term: Box::new(t),
                }),
                None => t,
            };
            params.push((None, t));
        }
        let result = match &m.result {
            Some(r) => replace(r, &class.param, with),
            None => self.unit(),
        };
        self.term(TermKind::Pi {
            params,
            result: Box::new(result),
            effects: m.effects.clone(),
        })
    }

    fn unit(&mut self) -> SurfaceTerm {
        let function = Box::new(self.var("Tuple"));
        self.term(TermKind::App {
            function,
            arguments: Vec::new(),
        })
    }

    fn evidence(&self, t: &SurfaceTerm) -> Option<Vec<Ev>> {
        self.report.evidence.get(&t.id()).cloned()
    }

    /// `C::m`, the method of a class. A static reference reads as one name
    /// (`Var("Ord::compare")`); a function `C::m` of a module `C` is not one.
    fn method_use<'t>(&self, t: &'t SurfaceTerm) -> Option<(&'t str, &'t str)> {
        match &*t.kind {
            TermKind::Field { base, name } => match &*base.kind {
                TermKind::Var(c) => Some((c, name)),
                _ => None,
            },
            TermKind::Var(n) => n.rsplit_once("::").filter(|(c, m)| {
                self.class(c)
                    .is_some_and(|class| class.methods.iter().any(|f| f.name == *m))
            }),
            _ => None,
        }
    }

    fn go(&mut self, t: &mut SurfaceTerm) {
        if let Some((taken, count)) = self.report.pair_members.get(&t.id()).cloned()
            && let TermKind::Ascribe { term: base, .. } = &*t.kind
        {
            let mut base = (**base).clone();
            self.go(&mut base);
            self.from(t.id());
            *t = self.pair_members(&base, &taken, count);
            return;
        }
        let own = self.evidence(t);
        let callee = match &*t.kind {
            TermKind::App { function, .. } => self.evidence(function),
            _ => None,
        };
        match Arc::make_mut(&mut t.kind) {
            TermKind::App {
                function,
                arguments,
            } if callee.is_some() => {
                for a in arguments.iter_mut() {
                    self.go(a);
                }
                self.from(function.id());
                let (target, extra) = self.call_target(function, &callee.unwrap_or_default());
                **function = target;
                arguments.extend(extra);
            }
            TermKind::Block(stmts) => {
                for s in stmts {
                    match s {
                        Stmt::Fn(f) => self.fn_decl(f),
                        s => walk::roots(s, &mut |t| self.go(t)),
                    }
                }
            }
            _ if own.is_some() => {
                let evs = own.unwrap_or_default();
                self.from(t.id());
                *t = self.value_form(t, &evs);
            }
            _ => walk::children(t, &mut |c| self.go(c)),
        }
    }

    /// The members `taken` of the pair `base` of `count` members, by `.fst`
    /// and `.snd`, put together in a `Pair` when they are more than one.
    fn pair_members(&mut self, base: &SurfaceTerm, taken: &[usize], count: usize) -> SurfaceTerm {
        let mut picked: Vec<SurfaceTerm> = taken
            .iter()
            .map(|&i| {
                let mut m = base.clone();
                for _ in 0..i {
                    m = self.term(TermKind::Field {
                        base: Box::new(m),
                        name: "snd".into(),
                    });
                }
                if i + 1 < count {
                    m = self.term(TermKind::Field {
                        base: Box::new(m),
                        name: "fst".into(),
                    });
                }
                m
            })
            .collect();
        let last = picked.pop().expect("one or more");
        picked.into_iter().rev().fold(last, |snd, fst| {
            let function = self.var("Pair");
            self.term(TermKind::App {
                function: Box::new(function),
                arguments: vec![fst, snd],
            })
        })
    }

    /// The function a call goes to, and the arguments it is given besides.
    fn call_target(
        &mut self,
        function: &SurfaceTerm,
        evs: &[Ev],
    ) -> (SurfaceTerm, Vec<SurfaceTerm>) {
        if let Some((class, method)) = self.method_use(function) {
            return match evs.first() {
                Some(Ev::Assume(_, g)) => (self.var(format!("{class}::{method}@{g}")), Vec::new()),
                Some(Ev::Inst(_, head, _, subs)) => {
                    let callee = self.var(instance_fn(class, method, head));
                    (callee, self.dictionaries(subs))
                }
                _ => (function.clone(), Vec::new()),
            };
        }
        (function.clone(), self.dictionaries(evs))
    }

    /// The arguments that stand for the evidence: one for each method of each
    /// class.
    fn dictionaries(&mut self, evs: &[Ev]) -> Vec<SurfaceTerm> {
        let mut out = Vec::new();
        for ev in evs {
            let class = match ev {
                Ev::Assume(c, _) | Ev::Inst(c, ..) => c,
                _ => continue,
            };
            let Some(class) = self.class(class).cloned() else {
                continue;
            };
            for m in &class.methods {
                out.push(self.method_value(&class, m, ev));
            }
        }
        out
    }

    /// The method as a value, as the evidence gives it.
    fn method_value(&mut self, class: &ClassDecl, m: &FnDecl, ev: &Ev) -> SurfaceTerm {
        match ev {
            Ev::Assume(_, g) => self.var(format!("{}::{}@{g}", class.name, m.name)),
            Ev::Inst(_, head, _, subs) => {
                let name = instance_fn(&class.name, &m.name, head);
                let extra = self.dictionaries(subs);
                if extra.is_empty() {
                    return self.var(name);
                }
                let names: Vec<String> = (0..m.params.len())
                    .map(|n| format!("{}@{n}", m.name))
                    .collect();
                let mut arguments: Vec<SurfaceTerm> =
                    names.iter().map(|n| self.var(n.clone())).collect();
                arguments.extend(extra);
                let callee = self.var(name);
                let call = self.term(TermKind::App {
                    function: Box::new(callee),
                    arguments,
                });
                self.closure(names, m.borrows.clone(), call)
            }
            _ => self.unit(),
        }
    }

    fn closure(
        &mut self,
        params: Vec<String>,
        borrows: Vec<Option<bool>>,
        body: SurfaceTerm,
    ) -> SurfaceTerm {
        let lam = self.term(TermKind::Lam {
            params,
            body: Box::new(body),
            types: Vec::new(),
        });
        if borrows.iter().any(Option::is_some) {
            self.term(TermKind::BorrowLam {
                borrows,
                lam: Box::new(lam),
            })
        } else {
            lam
        }
    }

    /// A use that is not a call: a method, or a function that asks for a
    /// class, as a value.
    fn value_form(&mut self, t: &SurfaceTerm, evs: &[Ev]) -> SurfaceTerm {
        if let Some((class, method)) = self.method_use(t) {
            let found = self.class(class).cloned();
            let method = found
                .as_ref()
                .and_then(|c| c.methods.iter().find(|m| m.name == method));
            if let (Some(c), Some(m), Some(ev)) = (found.as_ref(), method, evs.first()) {
                let m = m.clone();
                return self.method_value(c, &m, ev);
            }
            return t.clone();
        }
        let TermKind::Var(name) = &*t.kind else {
            return t.clone();
        };
        let Some(scheme) = self.report.scheme(name) else {
            return t.clone();
        };
        let crate::types::Ty::Fn(params, ..) = &scheme.ty else {
            return t.clone();
        };
        let borrows: Vec<Option<bool>> = params
            .iter()
            .map(|p| match p {
                crate::types::Ty::Borrow(_, m) => Some(*m),
                _ => None,
            })
            .collect();
        let names: Vec<String> = (0..params.len()).map(|n| format!("{name}@{n}")).collect();
        let mut arguments: Vec<SurfaceTerm> = names.iter().map(|n| self.var(n.clone())).collect();
        arguments.extend(self.dictionaries(evs));
        let callee = self.term((*t.kind).clone());
        let call = self.term(TermKind::App {
            function: Box::new(callee),
            arguments,
        });
        self.closure(names, borrows, call)
    }
}
