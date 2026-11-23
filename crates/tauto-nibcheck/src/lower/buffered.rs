//! A function value that makes a text is, as Rust runs it, given the buffer
//! to put the text on (`docs/design/rust-backend.md`).
//!
//! A struct field whose type is `(A, …) -> Text` becomes `(Buf, A, …) -> Buf`:
//! the function puts its text after what the buffer holds and gives the
//! buffer back. Each value written for the field is wrapped to that form: a
//! closure whose body fills a fresh buffer (`{ var wbuf := Buf::new() …
//! Text::of(wbuf) }`, what extraction writes for a text writer) fills the
//! given one instead, and any other pushes its text onto the given buffer.
//! Each call of the field makes its text on an empty buffer, so a program
//! that reads the text still reads the same text; where the text is only
//! pushed onto another buffer (`let w := f(…); Buf::push(&mut b, &w)`), the
//! call fills that buffer in place, and no text of its own is made.
//!
//! A function whose every result is a call of such a field (an accessor,
//! `match c { S { f: p, … } => p(a) }`) gets a copy that takes the buffer
//! too, so a push of its result fills the buffer in place as well.
//!
//! The rewrite is only taken for fields whose every use it understands: a
//! field read by a record pattern and called, and written by a record
//! literal. The program it gives is checked again, and the one written is
//! kept when that fails.

use std::collections::{HashMap, HashSet};

use tauto_parol::Span;
use tauto_surface::identity::{DeclRef, LocalRef};
use tauto_surface::surface::{
    FnDecl, MatchArm, Name, Pattern, Program, Stmt, SurfaceTerm, TermKind, walk,
};

/// A struct field `(A, …) -> Text`, by the struct and the field.
type Field = (Name, String);

fn library(s: &str, span: Span) -> SurfaceTerm {
    SurfaceTerm::var(&tauto_surface::bindings::library_name(s), span)
}

fn app(f: SurfaceTerm, args: Vec<SurfaceTerm>, span: Span) -> SurfaceTerm {
    SurfaceTerm::new(
        TermKind::App {
            function: Box::new(f),
            arguments: args,
        },
        span,
    )
}

fn local(n: &Name, span: Span) -> SurfaceTerm {
    SurfaceTerm::var(n, span)
}

fn borrow(mutable: bool, t: SurfaceTerm, span: Span) -> SurfaceTerm {
    SurfaceTerm::new(
        TermKind::Borrow {
            orig: false,
            rc: false,
            mutable,
            term: Box::new(t),
        },
        span,
    )
}

fn fresh(display: &str) -> Name {
    Name::Local(LocalRef::fresh(display))
}

fn is_var(t: &SurfaceTerm, name: &str) -> bool {
    matches!(&*t.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(n, name))
}

/// Whether `t` is the type `Text`.
fn is_text(t: &SurfaceTerm) -> bool {
    is_var(t, "Text")
}

/// The number of parameters of a field type `(A, …) -> Text` that takes no
/// borrow and performs nothing.
fn text_function(t: &SurfaceTerm) -> Option<usize> {
    let TermKind::Pi {
        params,
        result,
        effects,
        ..
    } = &*t.kind
    else {
        return None;
    };
    (is_text(result)
        && effects.as_ref().is_none_or(|e| e.is_empty())
        && params
            .iter()
            .all(|(_, p)| !matches!(&*p.kind, TermKind::Borrow { .. })))
    .then_some(params.len())
}

fn structs<'s>(stmts: &'s [Stmt], out: &mut Vec<&'s tauto_surface::surface::DataDecl>) {
    for s in stmts {
        match s {
            Stmt::Struct(d) => out.push(d),
            Stmt::Module { items, .. } | Stmt::Mutual { items, .. } => structs(items, out),
            _ => {}
        }
    }
}

struct Scan<'a> {
    fields: &'a HashMap<Field, usize>,
    /// The names a record pattern binds to a field, and the field.
    bound: HashMap<Name, Field>,
    /// Fields read or written in a way this does not rewrite.
    bad: HashSet<Field>,
}

impl Scan<'_> {
    fn field_of(&self, s: &Name, f: &str) -> Option<Field> {
        let k = (s.clone(), f.to_string());
        self.fields.contains_key(&k).then_some(k)
    }

    fn pattern(&mut self, p: &Pattern) {
        match p {
            Pattern::Record { name, fields } => {
                for (f, q) in fields {
                    if let Some(k) = self.field_of(name, f) {
                        match q {
                            Pattern::Bind { name: n, .. } => {
                                self.bound.insert(n.clone(), k);
                            }
                            Pattern::Wild => {}
                            _ => {
                                self.bad.insert(k);
                            }
                        }
                    } else {
                        self.pattern(q);
                    }
                }
            }
            Pattern::Ctor { args, .. } => args.iter().for_each(|q| self.pattern(q)),
            _ => {}
        }
    }

    fn term(&mut self, t: &SurfaceTerm) {
        let mut t = t.clone();
        walk::term(&mut t, &mut |u| match &*u.kind {
            TermKind::Match { arms, .. } => {
                for a in arms {
                    self.pattern(&a.pattern);
                }
            }
            TermKind::Record { name, base, .. } if base.is_some() => {
                for ((s, f), _) in self.fields.iter() {
                    if s == name {
                        self.bad.insert((s.clone(), f.clone()));
                    }
                }
            }
            TermKind::Field { name, .. } => {
                for ((s, f), _) in self.fields.iter() {
                    if f == name {
                        self.bad.insert((s.clone(), f.clone()));
                    }
                }
            }
            _ => {}
        });
    }

    /// Every use of a bound name is a call with all its arguments: the
    /// name occurs as often as it is called.
    fn uses(&mut self, t: &SurfaceTerm) {
        let mut t = t.clone();
        let mut calls: HashMap<Name, usize> = HashMap::new();
        let mut occurs: HashMap<Name, usize> = HashMap::new();
        walk::term(&mut t, &mut |u| {
            if let TermKind::App {
                function,
                arguments,
            } = &*u.kind
                && let TermKind::Var(n) = &*function.kind
                && let Some(k) = self.bound.get(n)
            {
                if arguments.len() == self.fields[k] {
                    *calls.entry(n.clone()).or_default() += 1;
                } else {
                    self.bad.insert(k.clone());
                }
            }
            if let TermKind::Var(n) = &*u.kind
                && self.bound.contains_key(n)
            {
                *occurs.entry(n.clone()).or_default() += 1;
            }
        });
        for (n, c) in occurs {
            if calls.get(&n).copied().unwrap_or(0) != c {
                self.bad.insert(self.bound[&n].clone());
            }
        }
    }
}

/// The terms of every statement, the declarations' bodies among them.
fn each_term(stmts: &[Stmt], f: &mut dyn FnMut(&SurfaceTerm)) {
    for s in stmts {
        match s {
            Stmt::Module { items, .. } | Stmt::Mutual { items, .. } => each_term(items, f),
            s => {
                let mut s = s.clone();
                walk::roots(&mut s, &mut |t| f(t));
            }
        }
    }
}

struct Rewrite {
    fields: HashMap<Field, usize>,
    bound: HashMap<Name, Field>,
    /// The accessors and the copy of each that takes the buffer.
    accessors: HashMap<Name, Name>,
    /// The buffers of the values already rewritten: the walk visits what it
    /// put in place, and these are not rewritten again.
    given: std::cell::RefCell<HashSet<Name>>,
}

impl Rewrite {
    fn done(&self, v: &SurfaceTerm) -> bool {
        matches!(&*v.kind, TermKind::Lam { params, .. }
            if params.first().is_some_and(|p| self.given.borrow().contains(p)))
    }

    /// The arity of the field bound to `f`.
    fn arity(&self, f: &Name) -> Option<usize> {
        self.bound.get(f).map(|k| self.fields[k])
    }

    /// The field's value `v`, as a function that puts its text on a buffer.
    fn value(&self, v: &SurfaceTerm, n: usize) -> SurfaceTerm {
        let span = v.span;
        let b = fresh("wgiven");
        self.given.borrow_mut().insert(b.clone());
        let buf = library("Buf", span);
        let (params, types, body) = match &*v.kind {
            TermKind::Lam {
                params,
                body,
                types,
                ..
            } if params.len() == n => (params.clone(), types.clone(), (**body).clone()),
            _ => {
                let xs: Vec<Name> = (0..n).map(|i| fresh(&format!("warg{i}"))).collect();
                let call = app(v.clone(), xs.iter().map(|x| local(x, span)).collect(), span);
                (xs, vec![None; n], call)
            }
        };
        let body = self.filled(&body, &b, span);
        let mut all_params = vec![b];
        all_params.extend(params);
        let mut all_types = vec![Some(buf)];
        all_types.extend(types);
        SurfaceTerm::new(
            TermKind::Lam {
                params: all_params,
                unused_params: Vec::new(),
                body: Box::new(body),
                types: all_types,
            },
            span,
        )
    }

    /// `body`, which makes a text, as a block that puts that text on `b`
    /// and gives `b` back.
    fn filled(&self, body: &SurfaceTerm, b: &Name, span: Span) -> SurfaceTerm {
        // `{ var wbuf := Buf::new(); …; Text::of(wbuf) }`: fill `b` instead.
        if let TermKind::Block(stmts) = &*body.kind
            && let [Stmt::Var { name, value, .. }, middle @ .., Stmt::Expr(last)] = stmts.as_slice()
            && let TermKind::App {
                function,
                arguments,
            } = &*value.kind
            && is_var(function, "Buf::new")
            && arguments.is_empty()
            && let TermKind::App {
                function,
                arguments,
            } = &*last.kind
            && is_var(function, "Text::of")
            && matches!(arguments.as_slice(), [a] if matches!(&*a.kind, TermKind::Var(x) if x == name))
        {
            let mut out = vec![Stmt::Var {
                stack: None,
                name: name.clone(),
                unused: None,
                ty: None,
                value: local(b, span),
                borrow: false,
            }];
            out.extend(middle.iter().cloned());
            out.push(Stmt::Expr(local(name, span)));
            return SurfaceTerm::new(TermKind::Block(out), span);
        }
        let w = fresh("wfill");
        let t = fresh("wtext");
        SurfaceTerm::new(
            TermKind::Block(vec![
                Stmt::Var {
                    stack: None,
                    name: w.clone(),
                    unused: None,
                    ty: None,
                    value: local(b, span),
                    borrow: false,
                },
                Stmt::Let {
                    stack: None,
                    name: t.clone(),
                    unused: None,
                    ty: None,
                    value: body.clone(),
                    borrow: false,
                    borrow_mut: false,
                },
                Stmt::Expr(app(
                    library("Buf::push", span),
                    vec![
                        borrow(true, local(&w, span), span),
                        borrow(false, local(&t, span), span),
                    ],
                    span,
                )),
                Stmt::Expr(local(&w, span)),
            ]),
            span,
        )
    }

    /// `Text::of(f(Buf::new(), …))`: the text a call of the field makes.
    fn text_of(&self, call: &SurfaceTerm) -> SurfaceTerm {
        let span = call.span;
        let TermKind::App {
            function,
            arguments,
        } = &*call.kind
        else {
            return call.clone();
        };
        let mut args = vec![app(library("Buf::new", span), Vec::new(), span)];
        args.extend(arguments.iter().cloned());
        app(
            library("Text::of", span),
            vec![app((**function).clone(), args, span)],
            span,
        )
    }

    /// The call `e` given buffer `b` first, when it is a call of a field or
    /// of an accessor.
    fn given(&self, e: &SurfaceTerm, b: SurfaceTerm) -> Option<SurfaceTerm> {
        let TermKind::App {
            function,
            arguments,
        } = &*e.kind
        else {
            return None;
        };
        let TermKind::Var(f) = &*function.kind else {
            return None;
        };
        let callee = if let Some(n) = self.arity(f) {
            if arguments.len() != n {
                return None;
            }
            (**function).clone()
        } else {
            local(self.accessors.get(f)?, function.span)
        };
        let mut args = vec![b];
        args.extend(arguments.iter().cloned());
        Some(app(callee, args, e.span))
    }

    /// `let w := g(…); Buf::push(&mut b, &w)`, for `g` a field or an
    /// accessor: `g` fills `b` in place.
    fn statements(&self, stmts: &mut Vec<Stmt>) {
        let mut i = 0;
        while i + 1 < stmts.len() {
            let Stmt::Let { name, value, .. } = &stmts[i] else {
                i += 1;
                continue;
            };
            let Stmt::Expr(push) = &stmts[i + 1] else {
                i += 1;
                continue;
            };
            let TermKind::App {
                function,
                arguments,
            } = &*push.kind
            else {
                i += 1;
                continue;
            };
            let target = match arguments.as_slice() {
                [b, t] if is_var(function, "Buf::push") => match (&*b.kind, &*t.kind) {
                    (
                        TermKind::Borrow {
                            mutable: true,
                            term: b,
                            ..
                        },
                        TermKind::Borrow {
                            mutable: false,
                            term: t,
                            ..
                        },
                    ) if matches!(&*t.kind, TermKind::Var(x) if x == name) => Some((**b).clone()),
                    _ => None,
                },
                _ => None,
            };
            let Some(target) = target else {
                i += 1;
                continue;
            };
            let span = push.span;
            let taken = fresh("wtaken");
            let empty = fresh("wempty");
            let Some(call) = self.given(value, local(&taken, span)) else {
                i += 1;
                continue;
            };
            let filled = fresh("wfilled");
            let replace = |with: SurfaceTerm| {
                app(
                    library("replace", span),
                    vec![borrow(true, target.clone(), span), with],
                    span,
                )
            };
            let new = vec![
                Stmt::Let {
                    stack: None,
                    name: empty.clone(),
                    unused: None,
                    ty: None,
                    value: SurfaceTerm::new(TermKind::Text(String::new()), span),
                    borrow: false,
                    borrow_mut: false,
                },
                Stmt::Let {
                    stack: None,
                    name: taken.clone(),
                    unused: None,
                    ty: None,
                    value: replace(app(
                        library("Buf::of", span),
                        vec![borrow(false, local(&empty, span), span)],
                        span,
                    )),
                    borrow: false,
                    borrow_mut: false,
                },
                Stmt::Let {
                    stack: None,
                    name: filled.clone(),
                    unused: None,
                    ty: None,
                    value: call,
                    borrow: false,
                    borrow_mut: false,
                },
                Stmt::Expr(replace(local(&filled, span))),
            ];
            stmts.splice(i..i + 2, new);
            i += 4;
        }
    }

    fn term(&self, t: &mut SurfaceTerm) {
        walk::term(t, &mut |u| {
            let replaced = match &*u.kind {
                TermKind::Record { name, fields, base } => {
                    let mut changed = false;
                    let fields = fields
                        .iter()
                        .map(|(f, v)| match self.fields.get(&(name.clone(), f.clone())) {
                            Some(&n) if !self.done(v) => {
                                changed = true;
                                (f.clone(), self.value(v, n))
                            }
                            _ => (f.clone(), v.clone()),
                        })
                        .collect();
                    changed.then(|| {
                        u.with_kind(
                            TermKind::Record {
                                name: name.clone(),
                                fields,
                                base: base.clone(),
                            },
                            u.span,
                        )
                    })
                }
                TermKind::Block(stmts) => {
                    let mut stmts = stmts.clone();
                    let before = stmts.len();
                    self.statements(&mut stmts);
                    (stmts.len() != before).then(|| u.with_kind(TermKind::Block(stmts), u.span))
                }
                TermKind::App { function, .. } => match &*function.kind {
                    TermKind::Var(f)
                        if self.arity(f).is_some_and(|n| {
                            matches!(&*u.kind, TermKind::App { arguments, .. } if arguments.len() == n)
                        }) =>
                    {
                        Some(self.text_of(u))
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some(r) = replaced {
                *u = r;
            }
        });
    }

    /// The copy of accessor `f` that takes the buffer: each result
    /// `p(…)` becomes `p(b, …)`.
    fn accessor_copy(&self, f: &FnDecl, name: &Name) -> Option<FnDecl> {
        let span = f.span;
        let b = fresh("wgiven");
        let mut d = f.clone();
        d.name = name.clone();
        d.params.insert(0, b.clone());
        d.borrows.insert(0, None);
        d.param_types.insert(0, Some(library("Buf", span)));
        d.result = Some(library("Buf", span));
        d.body = self.tails(&f.body, &b)?;
        walk::term(&mut d.body, &mut |t| t.freshen());
        Some(d)
    }

    fn tails(&self, t: &SurfaceTerm, b: &Name) -> Option<SurfaceTerm> {
        match &*t.kind {
            TermKind::Ascribe { term, .. } => self.tails(term, b),
            TermKind::Match {
                scrutinee,
                binder,
                arms,
                ..
            } => {
                let arms = arms
                    .iter()
                    .map(|a| {
                        Some(MatchArm {
                            body: self.tails(&a.body, b)?,
                            ..a.clone()
                        })
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(t.with_kind(
                    TermKind::Match {
                        scrutinee: scrutinee.clone(),
                        result: None,
                        binder: binder.clone(),
                        binder_unused: None,
                        arms,
                    },
                    t.span,
                ))
            }
            TermKind::App {
                function,
                arguments,
            } => {
                let TermKind::Var(p) = &*function.kind else {
                    return None;
                };
                self.bound.contains_key(p).then(|| {
                    let mut args = vec![local(b, t.span)];
                    args.extend(arguments.iter().cloned());
                    app((**function).clone(), args, t.span)
                })
            }
            _ => None,
        }
    }
}

/// Whether every result of `t` is a call of a bound field.
fn only_field_calls(t: &SurfaceTerm, bound: &HashMap<Name, Field>) -> bool {
    match &*t.kind {
        TermKind::Ascribe { term, .. } => only_field_calls(term, bound),
        TermKind::Match { arms, .. } => {
            !arms.is_empty() && arms.iter().all(|a| only_field_calls(&a.body, bound))
        }
        TermKind::App { function, .. } => {
            matches!(&*function.kind, TermKind::Var(p) if bound.contains_key(p))
        }
        _ => false,
    }
}

fn rewrite_stmts(stmts: &mut Vec<Stmt>, rw: &Rewrite, copies: &HashMap<Name, FnDecl>) {
    let mut out = Vec::new();
    for mut s in std::mem::take(stmts) {
        match &mut s {
            Stmt::Module { items, .. } | Stmt::Mutual { items, .. } => {
                rewrite_stmts(items, rw, copies);
            }
            Stmt::Struct(d) => {
                for c in &mut d.constructors {
                    for (f, ty) in &mut c.fields {
                        if let Some(f) = f
                            && rw.fields.contains_key(&(d.name.clone(), f.clone()))
                            && let TermKind::Pi { params, .. } = &*ty.kind
                        {
                            let span = ty.span;
                            let mut ps = vec![(None, library("Buf", span))];
                            ps.extend(params.iter().cloned());
                            *ty = ty.with_kind(
                                TermKind::Pi {
                                    params: ps,
                                    unused: Vec::new(),
                                    result: Box::new(library("Buf", span)),
                                    effects: None,
                                },
                                span,
                            );
                        }
                    }
                }
            }
            s => walk::roots(s, &mut |t| rw.term(t)),
        }
        let copy = match &s {
            Stmt::Fn(f) => copies.get(&f.name).cloned(),
            _ => None,
        };
        out.push(s);
        if let Some(c) = copy {
            out.push(Stmt::Fn(c));
        }
    }
    *stmts = out;
}

fn fns<'s>(stmts: &'s [Stmt], out: &mut Vec<&'s FnDecl>) {
    for s in stmts {
        match s {
            Stmt::Fn(f) => out.push(f),
            Stmt::Module { items, .. } | Stmt::Mutual { items, .. } => fns(items, out),
            _ => {}
        }
    }
}

/// `program` with its text-making struct fields given the buffer, or `None`
/// when it has none this rewrites.
pub(super) fn program(program: &Program) -> Option<Program> {
    let mut decls = Vec::new();
    structs(&program.stmts, &mut decls);
    let mut fields = HashMap::new();
    for d in decls {
        for c in &d.constructors {
            for (f, ty) in &c.fields {
                if let (Some(f), Some(n)) = (f, text_function(ty)) {
                    fields.insert((d.name.clone(), f.clone()), n);
                }
            }
        }
    }
    if fields.is_empty() {
        return None;
    }
    let mut scan = Scan {
        fields: &fields,
        bound: HashMap::new(),
        bad: HashSet::new(),
    };
    each_term(&program.stmts, &mut |t| scan.term(t));
    each_term(&program.stmts, &mut |t| scan.uses(t));
    let bad = scan.bad.clone();
    let bound: HashMap<Name, Field> = scan
        .bound
        .into_iter()
        .filter(|(_, k)| !bad.contains(k))
        .collect();
    fields.retain(|k, _| !bad.contains(k));
    if fields.is_empty() {
        return None;
    }
    let mut all = Vec::new();
    fns(&program.stmts, &mut all);
    let accessors: HashMap<Name, Name> = all
        .iter()
        .filter(|f| f.result.as_ref().is_some_and(is_text) && only_field_calls(&f.body, &bound))
        .map(|f| {
            (
                f.name.clone(),
                Name::Global(DeclRef::fresh(format!("{}__b", f.name))),
            )
        })
        .collect();
    let rw = Rewrite {
        fields,
        bound,
        accessors,
        given: Default::default(),
    };
    let mut copies = HashMap::new();
    for f in &all {
        if let Some(name) = rw.accessors.get(&f.name) {
            let mut copy = rw.accessor_copy(f, name)?;
            walk::term(&mut copy.body, &mut |t| t.freshen());
            copies.insert(f.name.clone(), copy);
        }
    }
    let mut out = program.clone();
    rewrite_stmts(&mut out.stmts, &rw, &copies);
    Some(out)
}
