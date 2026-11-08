//! A function over a type constructor variable (`F: (Shared) -> Shared`), or
//! one that takes the method of a class with generics of its own (the
//! expansion makes its dictionary a polymorphic function), has no Rust or
//! NIR shape as it is. Each call names what the function runs with: the
//! checked instantiation gives the type constructor, and the arguments the
//! expansion added give the dictionaries, which are the instances' functions.
//! So each such function becomes one copy for each constructor and
//! dictionaries it is called with: the variable written as that constructor,
//! the class's argument a dictionary's type is in terms of written as the
//! type the call gives, the dictionary parameter as the instance's function,
//! and the call as a call of the copy without the dictionaries. The other
//! generics stay the copy's. Calls inside a copy are copied
//! in turn. The program that results is checked again as any program, and
//! lowered only when it checks.

use std::collections::{HashMap, HashSet, VecDeque};

use tauto::identity::DeclRef;
use tauto::surface::{FnDecl, Name, Program, Stmt, SurfaceTerm, TermKind, walk};
use tauto::types::{Kind, ParamId, Ty, TypeReport, Width};

/// More copies than this is a recursion that grows its types: not lowered.
const LIMIT: usize = 512;

struct Target {
    decl: FnDecl,
    /// The type generics the copy is made for (the type constructor
    /// variables among them): their index and their identity in the checked
    /// scheme.
    ctors: Vec<(usize, ParamId)>,
    /// The parameters whose type is a polymorphic function.
    dictionaries: Vec<usize>,
}

#[derive(Default, Clone)]
struct Env {
    /// What a generic is in this copy, by identity.
    types: HashMap<ParamId, Ty>,
    /// The same, as written: by the generic's name.
    written: HashMap<Name, SurfaceTerm>,
    /// The dictionaries, by the parameter's name.
    values: HashMap<Name, SurfaceTerm>,
}

struct Specializer<'a> {
    report: &'a TypeReport,
    targets: HashMap<Name, Target>,
    copies: HashMap<String, Name>,
    work: VecDeque<(Name, Name, Env)>,
    made: HashMap<Name, Vec<Stmt>>,
    failed: bool,
}

/// `program` with its functions over type constructors and polymorphic
/// dictionaries copied for each use, or `None` when it has none or a use is
/// not one this can copy (the function as a value, a constructor that is
/// still a variable).
pub(super) fn program(program: &Program, report: &TypeReport) -> Option<Program> {
    let mut targets = HashMap::new();
    collect(&program.stmts, report, &mut targets);
    if targets.is_empty() {
        return None;
    }
    let mut sp = Specializer {
        report,
        targets,
        copies: HashMap::new(),
        work: VecDeque::new(),
        made: HashMap::new(),
        failed: false,
    };
    let stmts = sp.stmts(&program.stmts);
    while let Some((name, source, env)) = sp.work.pop_front() {
        if sp.failed || sp.copies.len() > LIMIT {
            return None;
        }
        let copy = sp.copy(&name, &source, &env);
        sp.made.entry(source).or_default().push(Stmt::Fn(copy));
    }
    if sp.failed {
        return None;
    }
    let mut out = program.clone();
    out.stmts = sp.place(stmts);
    Some(out)
}

/// The targets among `stmts`, and in the modules among them (an instance's
/// functions are in the class's module).
fn collect(stmts: &[Stmt], report: &TypeReport, out: &mut HashMap<Name, Target>) {
    for s in stmts {
        match s {
            Stmt::Fn(f) => {
                if let Some(t) = target(f, report) {
                    out.insert(f.name.clone(), t);
                }
            }
            Stmt::Module { items, .. } => collect(items, report, out),
            _ => {}
        }
    }
}

/// A statement as it runs, or the place of a target its copies go to.
enum Placed {
    Stmt(Stmt),
    Module(Stmt, Vec<Placed>),
    Target(Name),
}

fn target(f: &FnDecl, report: &TypeReport) -> Option<Target> {
    let scheme = report.schemes.get(&f.name)?;
    let Ty::Fn(params, ..) = &scheme.ty else {
        return None;
    };
    let dictionaries: Vec<usize> = params
        .iter()
        .enumerate()
        .filter(|(_, p)| matches!(p.unborrowed(), Ty::Poly(..)))
        .map(|(i, _)| i)
        .collect();
    let constructor = |i: usize| {
        f.generic_types
            .get(i)
            .is_some_and(|t| matches!(&*t.kind, TermKind::Pi { .. }))
    };
    if dictionaries.is_empty() && !(0..f.generics.len()).any(constructor) {
        return None;
    }
    // A dictionary's type is in terms of the class's argument, so the copy
    // is made for that generic too, not only for the constructors: the
    // instance's function the copy calls takes the type the call gives.
    // The other generics stay the copy's.
    let mut ctors = Vec::new();
    for (i, g) in f.generics.iter().enumerate() {
        if f.rows.get(i).copied().unwrap_or(false) {
            continue;
        }
        match scheme.generics.iter().find(|(p, _)| p.reference() == g) {
            Some((p, _))
                if constructor(i) || dictionaries.iter().any(|&d| mentions(&params[d], p.id())) =>
            {
                ctors.push((i, p.id().clone()))
            }
            None if constructor(i) => return None,
            _ => {}
        }
    }
    Some(Target {
        decl: f.clone(),
        ctors,
        dictionaries,
    })
}

impl Specializer<'_> {
    fn stmts(&mut self, stmts: &[Stmt]) -> Vec<Placed> {
        stmts
            .iter()
            .map(|s| match s {
                Stmt::Fn(f) if self.targets.contains_key(&f.name) => Placed::Target(f.name.clone()),
                Stmt::Module { items, .. } => Placed::Module(s.clone(), self.stmts(items)),
                s => {
                    let mut s = s.clone();
                    walk::roots(&mut s, &mut |t| self.rewrite(t, &Env::default()));
                    Placed::Stmt(s)
                }
            })
            .collect()
    }

    /// The statements with each target's copies where it was.
    fn place(&mut self, placed: Vec<Placed>) -> Vec<Stmt> {
        let mut out = Vec::new();
        for p in placed {
            match p {
                Placed::Stmt(s) => out.push(s),
                Placed::Target(name) => out.extend(self.made.remove(&name).into_iter().flatten()),
                Placed::Module(mut s, inner) => {
                    let placed = self.place(inner);
                    if let Stmt::Module { items, .. } = &mut s {
                        *items = placed;
                    }
                    out.push(s);
                }
            }
        }
        out
    }

    /// `t` as it runs in `env`: the dictionaries and type constructor
    /// variables of the copy replaced, and the calls of a target made calls
    /// of its copy.
    fn rewrite(&mut self, t: &mut SurfaceTerm, env: &Env) {
        walk::term(t, &mut |t| {
            if self.failed {
                return;
            }
            let replaced = match &*t.kind {
                TermKind::Var(n) if env.values.contains_key(n) => Some(env.values[n].clone()),
                TermKind::Var(n) if env.written.contains_key(n) => Some(env.written[n].clone()),
                // The function as a value: no copy says what it runs with.
                TermKind::Var(n) if self.targets.contains_key(n) => {
                    self.failed = true;
                    None
                }
                TermKind::App {
                    function,
                    arguments,
                } => match &*function.kind {
                    TermKind::Var(f) if self.targets.contains_key(f) => {
                        self.call(f, function, arguments, env, t.span)
                    }
                    TermKind::Var(n) if env.values.contains_key(n) => {
                        applied(&env.values[n], arguments)
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some(r) = replaced {
                *t = r;
            }
        });
    }

    fn call(
        &mut self,
        f: &Name,
        function: &SurfaceTerm,
        arguments: &[SurfaceTerm],
        env: &Env,
        span: tauto_parol::Span,
    ) -> Option<SurfaceTerm> {
        let target = &self.targets[f];
        if arguments.len() != target.decl.params.len() {
            self.failed = true;
            return None;
        }
        let Some(inst) = self.report.instantiations.get(&function.id()) else {
            self.failed = true;
            return None;
        };
        let mut types = Vec::new();
        for (_, p) in &target.ctors {
            match inst.get(p).map(|t| substitute(t, &env.types)) {
                Some(t) if closed(&t) => types.push(t),
                _ => {
                    self.failed = true;
                    return None;
                }
            }
        }
        let dictionaries = target.dictionaries.clone();
        let mut values = Vec::new();
        let mut key = format!("{f:?}");
        for t in &types {
            key.push_str(&format!("|{t:?}"));
        }
        for &i in &dictionaries {
            let mut v = arguments[i].clone();
            self.rewrite(&mut v, env);
            let Some(shape) = shape(&v) else {
                self.failed = true;
                return None;
            };
            key.push('|');
            key.push_str(&shape);
            values.push(v);
        }
        if self.failed {
            return None;
        }
        let name = match self.copies.get(&key) {
            Some(n) => n.clone(),
            None => {
                let target = &self.targets[f];
                let n: Name = Name::Global(DeclRef::fresh(format!("{f}@{}", self.copies.len())));
                let mut copy_env = Env::default();
                for ((i, p), t) in target.ctors.iter().zip(&types) {
                    let Some(w) = written(t, span) else {
                        self.failed = true;
                        return None;
                    };
                    copy_env.types.insert(p.clone(), t.clone());
                    copy_env.written.insert(target.decl.generics[*i].clone(), w);
                }
                for (&i, v) in dictionaries.iter().zip(values) {
                    copy_env.values.insert(target.decl.params[i].clone(), v);
                }
                self.copies.insert(key, n.clone());
                self.work.push_back((n.clone(), f.clone(), copy_env));
                n
            }
        };
        let kept: Vec<SurfaceTerm> = arguments
            .iter()
            .enumerate()
            .filter(|(i, _)| !dictionaries.contains(i))
            .map(|(_, a)| a.clone())
            .collect();
        Some(SurfaceTerm::new(
            TermKind::App {
                function: Box::new(SurfaceTerm::new(TermKind::Var(name), function.span)),
                arguments: kept,
            },
            span,
        ))
    }

    fn copy(&mut self, name: &Name, source: &Name, env: &Env) -> FnDecl {
        let target = &self.targets[source];
        let mut d = target.decl.clone();
        let generics: HashSet<usize> = target.ctors.iter().map(|(i, _)| *i).collect();
        let params: HashSet<usize> = target.dictionaries.iter().copied().collect();
        d.name = name.clone();
        retain_indices(&mut d.generics, &generics);
        retain_indices(&mut d.generic_types, &generics);
        retain_indices(&mut d.rows, &generics);
        retain_indices(&mut d.bounds, &generics);
        retain_indices(&mut d.bound_spans, &generics);
        retain_indices(&mut d.params, &params);
        retain_indices(&mut d.borrows, &params);
        retain_indices(&mut d.param_types, &params);
        let mut terms: Vec<&mut SurfaceTerm> = Vec::new();
        terms.extend(d.generic_types.iter_mut());
        terms.extend(d.param_types.iter_mut().flatten());
        terms.extend(d.result.iter_mut());
        terms.extend(d.where_.iter_mut().map(|c| &mut c.ty));
        terms.push(&mut d.body);
        for t in terms {
            self.rewrite(t, env);
            refresh(t);
        }
        d
    }
}

/// The call of a dictionary that is a closure the expansion wrote (an
/// instance's function given the dictionaries it asks for itself) as the
/// call of that function: each parameter of the closure is used once, in
/// order, so the arguments take their places.
fn applied(value: &SurfaceTerm, arguments: &[SurfaceTerm]) -> Option<SurfaceTerm> {
    let lam = match &*value.kind {
        TermKind::BorrowLam { lam, .. } => lam,
        TermKind::Lam { .. } => value,
        _ => return None,
    };
    let TermKind::Lam { params, body, .. } = &*lam.kind else {
        return None;
    };
    if params.len() != arguments.len() {
        return None;
    }
    let by: HashMap<&Name, &SurfaceTerm> = params.iter().zip(arguments).collect();
    let mut body = (**body).clone();
    walk::term(&mut body, &mut |t| {
        if let TermKind::Var(n) = &*t.kind
            && let Some(a) = by.get(n)
        {
            *t = (*a).clone();
        }
    });
    Some(body)
}

fn retain_indices<T>(v: &mut Vec<T>, drop: &HashSet<usize>) {
    let mut i = 0;
    v.retain(|_| {
        let keep = !drop.contains(&i);
        i += 1;
        keep
    });
}

/// Every term of `t` a distinct occurrence: a copy is checked apart from the
/// declaration it was copied from, and from the other copies.
fn refresh(t: &mut SurfaceTerm) {
    walk::term(t, &mut |t| {
        *t = SurfaceTerm::new((*t.kind).clone(), t.span);
    });
}

/// A dictionary as the copy's key: the names and the closures the expansion
/// writes. `None` for anything else.
fn shape(t: &SurfaceTerm) -> Option<String> {
    Some(match &*t.kind {
        TermKind::Var(n) => format!("{n:?}"),
        TermKind::App {
            function,
            arguments,
        } => {
            let mut s = format!("({}", shape(function)?);
            for a in arguments {
                s.push(' ');
                s.push_str(&shape(a)?);
            }
            s.push(')');
            s
        }
        TermKind::Lam {
            params,
            body,
            types,
        } if types.is_empty() => {
            format!("(λ {params:?} {})", shape(body)?)
        }
        TermKind::BorrowLam { borrows, lam } => format!("(& {borrows:?} {})", shape(lam)?),
        _ => return None,
    })
}

fn mentions(t: &Ty, p: &ParamId) -> bool {
    match t {
        Ty::Param(q, _) => q.id() == p,
        Ty::Fn(ps, r, _) => ps.iter().any(|t| mentions(t, p)) || mentions(r, p),
        Ty::Union(ts) | Ty::Named(_, ts) => ts.iter().any(|t| mentions(t, p)),
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Poly(_, t) => mentions(t, p),
        Ty::App(h, x) => mentions(h, p) || mentions(x, p),
        _ => false,
    }
}

fn closed(t: &Ty) -> bool {
    match t {
        Ty::Param(..) | Ty::Var(_) | Ty::App(..) | Ty::Poly(..) => false,
        Ty::Fn(ps, r, _) => ps.iter().all(closed) && closed(r),
        Ty::Union(ts) | Ty::Named(_, ts) => ts.iter().all(closed),
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) => closed(t),
        _ => true,
    }
}

/// `t` with the generics of `env` replaced, and an
/// application of a known constructor read as the type it makes.
fn substitute(t: &Ty, env: &HashMap<ParamId, Ty>) -> Ty {
    match t {
        Ty::Param(p, _) => env.get(p.id()).cloned().unwrap_or_else(|| t.clone()),
        Ty::App(h, x) => match (substitute(h, env), substitute(x, env)) {
            (Ty::Named(n, mut args), x) => {
                args.push(x);
                Ty::Named(n, args)
            }
            (h, x) => Ty::App(Box::new(h), Box::new(x)),
        },
        Ty::Fn(ps, r, k) => Ty::Fn(
            ps.iter().map(|p| substitute(p, env)).collect(),
            Box::new(substitute(r, env)),
            *k,
        ),
        Ty::Union(ts) => Ty::Union(ts.iter().map(|t| substitute(t, env)).collect()),
        Ty::Named(n, ts) => Ty::Named(n.clone(), ts.iter().map(|t| substitute(t, env)).collect()),
        Ty::Tagged(tags, t) => Ty::Tagged(tags.clone(), Box::new(substitute(t, env))),
        Ty::Info(t) => Ty::Info(Box::new(substitute(t, env))),
        Ty::Borrow(t, m) => Ty::Borrow(Box::new(substitute(t, env)), *m),
        _ => t.clone(),
    }
}

/// A closed type as the program would write it, for the copy's annotations.
fn written(t: &Ty, span: tauto_parol::Span) -> Option<SurfaceTerm> {
    let var = |n: Name| SurfaceTerm::new(TermKind::Var(n), span);
    let library = |s: &str| var(tauto::bindings::library_name(s));
    let app = |function: SurfaceTerm, arguments: Vec<SurfaceTerm>| {
        SurfaceTerm::new(
            TermKind::App {
                function: Box::new(function),
                arguments,
            },
            span,
        )
    };
    Some(match t {
        Ty::Int(w) => library(match w {
            Width::W32 => "i32",
            Width::W64 => "i64",
            Width::U8 => "u8",
            Width::U32 => "u32",
            Width::U64 => "u64",
            Width::Nat => "nat",
        }),
        Ty::Bool => library("Bool"),
        Ty::Text => library("Text"),
        Ty::Never => library("Never"),
        Ty::Decimal => library("Decimal"),
        Ty::Float => library("Float"),
        Ty::Float32 => library("Float32"),
        Ty::Unit => app(library("Tuple"), Vec::new()),
        Ty::Info(t) => app(library("Info"), vec![written(t, span)?]),
        Ty::Named(n, args) if args.is_empty() => var(n.clone()),
        Ty::Named(n, args) => app(
            var(n.clone()),
            args.iter()
                .map(|a| written(a, span))
                .collect::<Option<_>>()?,
        ),
        Ty::Borrow(t, mutable) => SurfaceTerm::new(
            TermKind::Borrow {
                mutable: *mutable,
                term: Box::new(written(t, span)?),
            },
            span,
        ),
        Ty::Fn(ps, r, Kind::Shared) => SurfaceTerm::new(
            TermKind::Pi {
                params: ps
                    .iter()
                    .map(|p| Some((None, written(p, span)?)))
                    .collect::<Option<_>>()?,
                result: Box::new(written(r, span)?),
                effects: None,
            },
            span,
        ),
        _ => return None,
    })
}
