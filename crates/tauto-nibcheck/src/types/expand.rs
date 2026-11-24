//! The expansion of classes: a constraint becomes an
//! argument for each method of the class, a method call a call of the
//! argument or of the instance's function, and an instance a function for
//! each of its methods. What follows sees no class, and checks the result
//! as it checks any program.

use crate::surface::Name;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use tauto_parol::Span;

use super::classes::{instance_fn, member_fn, replace};
use super::{Ev, Kind, STRUCTURAL, TypeError, TypeReport, check_program_in, prelude_source_for};
use crate::surface::walk;
use crate::surface::{
    ClassDecl, Constraint, FnDecl, InstanceDecl, Program, Stmt, SurfaceTerm, TermId, TermKind,
};

/// The classes and the constrained functions of the prelude.
fn prelude_names(program: &Program) -> (HashSet<Name>, HashSet<Name>, HashSet<Name>) {
    let (mut classes, mut fns, mut methods) = (HashSet::new(), HashSet::new(), HashSet::new());
    for s in &prelude_source_for(program).stmts {
        match s {
            Stmt::Class(c) => {
                classes.insert(c.name.clone());
                methods.extend(c.methods.iter().map(|m| member_fn(c, &m.name)));
            }
            Stmt::Fn(f) if constrained(&f.where_) => {
                fns.insert(f.name.clone());
            }
            Stmt::Extern { fns: es, .. } => {
                fns.extend(
                    es.iter()
                        .filter(|f| constrained(&f.where_))
                        .map(|f| f.name.clone()),
                );
            }
            _ => {}
        }
    }
    (classes, fns, methods)
}

fn constrained(where_: &[Constraint]) -> bool {
    where_
        .iter()
        .any(|c| !STRUCTURAL.contains(&c.class.as_str()))
}

/// Whether the program declares a class, an instance or a constraint
/// (`Some(true)`), or only looks to use the std's (`Some(false)`).
fn needs_expansion(program: &Program) -> Option<bool> {
    let (classes, fns, methods) = prelude_names(program);
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
            Stmt::Extern { fns, .. } if fns.iter().any(|f| constrained(&f.where_)) => {
                return Some(true);
            }
            Stmt::Struct(d) | Stmt::Enum(d) if classes.contains(&d.name) => return Some(true),
            _ => {}
        }
        let mut s = s.clone();
        walk::stmt(&mut s, &mut |t| match &*t.kind {
            TermKind::Var(n) if fns.contains(n) && !own.contains(n.as_str()) => found = true,
            // `C::m`, a method of a class of the prelude, is one name.
            TermKind::Var(n) if methods.contains(n) => found = true,
            TermKind::Field { base, .. } if matches!(&*base.kind, TermKind::Var(c) if classes.contains(&Name::from(c))) => {
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

/// Whether the program declares or uses a class, so that what it means is
/// read against the prelude as written.
pub(super) fn uses_classes(program: &Program) -> bool {
    needs_expansion(program).is_some() && !expanded(program)
}

/// Whether the program is already expanded: a call of a constrained function
/// of the prelude is given more values than it is written with, the
/// dictionaries the expansion added. Such a program is read against the
/// expanded prelude only.
fn expanded(program: &Program) -> bool {
    let mut arity: HashMap<Name, usize> = HashMap::new();
    for s in &prelude_source_for(program).stmts {
        if let Stmt::Fn(f) = s {
            if constrained(&f.where_) {
                arity.insert(f.name.clone(), f.params.len());
            }
        }
    }
    let mut found = false;
    for s in &program.stmts {
        let mut s = s.clone();
        walk::stmt(&mut s, &mut |t| {
            if let TermKind::App {
                function,
                arguments,
            } = &*t.kind
            {
                if let TermKind::Var(n) = &*function.kind {
                    if arity.get(n).is_some_and(|&k| arguments.len() > k) {
                        found = true;
                    }
                }
            }
        });
        if found {
            return true;
        }
    }
    false
}

/// The first of `Program::errors` when the program did not expand: the rest
/// are what the class-aware check found.
pub(super) const UNEXPANDED: &str = "\0unexpanded";

/// What kept `program`'s classes from expanding: the errors the class-aware
/// check finds in a program that still uses a class, or none for one whose
/// classes expanded (or that uses none).
pub fn expansion_errors(program: &Program) -> Vec<TypeError> {
    // The instances the compiler made for the program's types (`debug.rs`)
    // ask nothing of a program that uses no class: its rows say their own.
    let mut written = program.clone();
    written.stmts.retain(|s| match s {
        Stmt::Instance(i) => !super::debug::is_made(i.span),
        Stmt::Fn(f) => !super::debug::is_made(f.span),
        _ => true,
    });
    if needs_expansion(&written).is_none() || expanded(program) {
        return Vec::new();
    }
    check_program_in(program, prelude_source_for(program)).errors
}

/// What kept `program`'s indexed effects from expanding: a row of the
/// program that still writes type arguments (`fail(Text)`) was left as it is
/// because the program does not check (`indices.rs`), and these are the
/// errors that check finds. None for a program whose rows expanded.
pub fn index_expansion_errors(program: &Program) -> Vec<TypeError> {
    if super::indices::indexed_effects(program).is_empty() {
        return Vec::new();
    }
    check_program_in(program, super::prelude_for(program)).errors
}

/// `program` with its classes, instances and constraints expanded. A program
/// that does not check is returned as it is, for the checker to report on.
/// The terms the expansion makes get spans from `synthetic` on, which no
/// written term has.
pub fn expand_classes(mut program: Program, synthetic: u32) -> Program {
    super::coerce::expand_coercions(&mut program, &mut []);
    super::lend::expand_lends(&mut program, &mut []);
    expand(&mut program, &mut Vec::new(), &[], synthetic, true);
    super::indices::expand_indices(&mut program, &mut [], &[], false);
    program
}

/// [`expand_classes`] for the prelude itself, whose indexed effects are
/// expanded against itself rather than against the prelude.
pub(super) fn expand_prelude(mut program: Program, synthetic: u32) -> Program {
    expand(&mut program, &mut Vec::new(), &[], synthetic, true);
    super::indices::expand_indices(&mut program, &mut [], &[], true);
    program
}

/// [`expand_prelude`] for a library read as a program with the library's own
/// names (the prelude a runtime reads): its indexed effects are its own, so
/// they are not also taken from the prelude it would be checked against,
/// where the same declaration hides the uses that need a copy.
pub fn expand_library(program: Program, synthetic: u32) -> Program {
    expand_prelude(program, synthetic)
}

/// [`expand_classes`] for a program read from several files: the program,
/// and the statements of each file, are expanded alike, so that a term the
/// expansion makes has one span in both.
///
/// The origin of each term the class expansion made is returned in the order
/// of their spans: the span `synthetic + i` stands for the written occurrence
/// `i`-th returned, so an error found in generated code is shown where the
/// occurrence that needed it is written.
///
/// `imported` are the statements the top levels of the imported files would
/// run (a dependency's `perform test(...)`): they are in `per_file` but not
/// in `program`, and the class-aware check reads them with it, so that a call
/// in one of them gets the dictionaries it needs like a call in the entry.
pub fn expand_loaded(
    program: &mut Program,
    per_file: &mut [Vec<Stmt>],
    imported: &[Stmt],
    synthetic: u32,
) -> Vec<Span> {
    super::coerce::expand_coercions(program, per_file);
    super::lend::expand_lends(program, per_file);
    let made = expand(program, per_file, imported, synthetic, false);
    super::indices::expand_indices(program, per_file, &expanded_top(per_file, imported), false);
    made
}

/// [`expand_loaded`] for a program that has to run as expanded, such as the
/// program extraction makes: one that does not check is left as it is but
/// carries what the class-aware check found, so that [`check_program`] reports
/// why it did not expand rather than what its unexpanded classes look like
/// afterwards (a method that no function defines).
///
/// [`check_program`]: super::check_program
pub fn expand_loaded_reporting(
    program: &mut Program,
    per_file: &mut [Vec<Stmt>],
    imported: &[Stmt],
    synthetic: u32,
) -> Vec<Span> {
    super::coerce::expand_coercions(program, per_file);
    super::lend::expand_lends(program, per_file);
    let made = expand(program, per_file, imported, synthetic, true);
    super::indices::expand_indices(program, per_file, &expanded_top(per_file, imported), false);
    made
}

/// With `report`, a program that does not check carries what was found, for
/// `check_program`; without, it is left as it is.
fn expand(
    program: &mut Program,
    per_file: &mut [Vec<Stmt>],
    imported: &[Stmt],
    synthetic: u32,
    report_errors: bool,
) -> Vec<Span> {
    if !std::ptr::eq(prelude_source_for(program), &*program) {
        let prelude = prelude_source_for(program);
        super::debug::add_instances(program, per_file, Some(prelude));
    }
    let Some(declared) = needs_expansion(program) else {
        return Vec::new();
    };
    inherit_local_where(program);
    // The imported top levels are read with the program, so that their calls
    // get dictionaries; a program that checks without them keeps doing so
    // when they are what does not check (that is not reported here).
    let with_imports = with_imported(program, imported);
    let mut checked = with_imports.as_ref().unwrap_or(program);
    let mut report = check_program_in(checked, prelude_source_for(checked));
    if !report.errors.is_empty() && with_imports.is_some() {
        checked = program;
        report = check_program_in(checked, prelude_source_for(checked));
    }
    if !report.errors.is_empty() {
        // A name the program binds itself (a parameter called `join`) looks
        // like a use of the std's; that it checks as it is settles it.
        if !report_errors
            || !declared
                && check_program_in(checked, super::prelude_for(checked))
                    .errors
                    .is_empty()
        {
            return Vec::new();
        }
        let found = report.errors.iter().map(|e| (e.message.clone(), e.span));
        program.errors = std::iter::once((UNEXPANDED.into(), Span::new(0, 0)))
            .chain(found)
            .collect();
        return Vec::new();
    }
    let mut externs = HashSet::new();
    extern_names(&program.stmts, &mut externs);
    for file in per_file.iter() {
        extern_names(file, &mut externs);
    }
    let mut e = Expander {
        report: &report,
        externs,
        next: synthetic,
        origin: None,
        count: 0,
        spans: HashMap::new(),
        dictionaries: HashMap::new(),
        made: Vec::new(),
    };
    program.stmts = e.stmts(std::mem::take(&mut program.stmts));
    for file in per_file {
        *file = e.stmts(std::mem::take(file));
    }
    e.made
}

/// `imported` as the class expansion left it in `per_file`: the top levels of
/// every file but the entry (the last), in the order `imported` has them.
fn expanded_top(per_file: &[Vec<Stmt>], imported: &[Stmt]) -> Vec<Stmt> {
    if imported.is_empty() {
        return Vec::new();
    }
    per_file
        .split_last()
        .map(|(_, before)| before)
        .unwrap_or_default()
        .iter()
        .flatten()
        .filter(|s| runs_at_top_level(s))
        .cloned()
        .collect()
}

/// Whether a statement runs when the file's top level does.
fn runs_at_top_level(s: &Stmt) -> bool {
    match s {
        Stmt::Let { .. }
        | Stmt::Var { .. }
        | Stmt::Assign { .. }
        | Stmt::While { .. }
        | Stmt::Expr(_) => true,
        Stmt::Attributed { stmt, .. } => runs_at_top_level(stmt),
        _ => false,
    }
}

/// `program` with the statements the imported files' top levels would run
/// placed before its own, after its declarations; `None` when there are none.
pub(super) fn with_imported(program: &Program, imported: &[Stmt]) -> Option<Program> {
    if imported.is_empty() {
        return None;
    }
    let at = program
        .stmts
        .iter()
        .position(runs_at_top_level)
        .unwrap_or(program.stmts.len());
    let mut stmts = program.stmts[..at].to_vec();
    stmts.extend(imported.iter().cloned());
    stmts.extend(program.stmts[at..].iter().cloned());
    Some(Program {
        stmts,
        errors: program.errors.clone(),
    })
}

/// The functions an `extern` block declares, in `stmts` and the blocks in it.
fn extern_names(stmts: &[Stmt], out: &mut HashSet<Name>) {
    for s in stmts {
        match s {
            // A fallback body that asks for a class is code like any `fn`'s:
            // it takes the class's methods, so its callers pass them.
            Stmt::Extern { fns, .. } => out.extend(
                fns.iter()
                    .filter(|f| {
                        !(tauto_surface::surface::extern_fn_has_body(f) && constrained(&f.where_))
                    })
                    .map(|f| f.name.clone()),
            ),
            Stmt::Mutual { items, .. } => extern_names(items, out),
            _ => {}
        }
    }
}

struct Expander<'a> {
    report: &'a TypeReport,
    /// The functions the host gives. A class in an `extern` function's
    /// `where` is a bound its callers meet, checked before the expansion;
    /// the host's function takes no dictionary, so a call passes none.
    externs: HashSet<Name>,
    dictionaries: HashMap<(Name, Name), Name>,
    next: u32,
    /// The occurrence the terms being made stand for, and their order.
    /// The program and per-file clones receive the same generated identities.
    origin: Option<(TermId, bool)>,
    count: usize,
    spans: HashMap<((TermId, bool), usize), SurfaceTerm>,
    /// The written span each made term stands for, by the order made.
    made: Vec<Span>,
}

fn head_name(head: &SurfaceTerm, resolved: bool) -> Name {
    match &*head.kind {
        // An instance for the product `A × B` is the one for `Pair`.
        TermKind::App { .. } if head.as_pair_type().is_some() && resolved => {
            tauto_surface::bindings::library_name("Pair")
        }
        TermKind::App { .. } if head.as_pair_type().is_some() => Name::from("Pair"),
        TermKind::Var(n) => n.clone(),
        TermKind::App { function, .. } => head_name(function, resolved),
        TermKind::Pi { params, .. } => super::classes::fn_head(params.len()),
        _ => Name::default(),
    }
}

/// Instance method key: one constructor, or every class argument's constructor joined (`i64@Bool`).
/// Matches [`super::classes`] instance table keys so expansion and resolution name the same function.
fn instance_heads_name(i: &InstanceDecl, resolved: bool) -> Name {
    let args: Vec<&SurfaceTerm> = std::iter::once(&i.head).chain(&i.arguments).collect();
    let ctors: Vec<Name> = args.iter().map(|a| head_name(a, resolved)).collect();
    if ctors.len() <= 1 {
        ctors.into_iter().next().unwrap_or_default()
    } else {
        Name::from(
            ctors
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join("@"),
        )
    }
}

/// Dictionary parameter key for an assumed constraint: one generic, or every
/// constrained generic joined (`A@B` for `where Convert(A, B)`).
fn assume_dictionary_key(parameters: &[Name]) -> Name {
    if parameters.len() <= 1 {
        parameters.first().cloned().unwrap_or_default()
    } else {
        Name::from(
            parameters
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join("@"),
        )
    }
}

/// Class method types with every class parameter replaced by the constraint's arguments.
fn instantiate_class_args(t: &SurfaceTerm, class: &ClassDecl, args: &[SurfaceTerm]) -> SurfaceTerm {
    let mut t = t.clone();
    for ((name, _), arg) in class.parameters.iter().zip(args) {
        t = replace(&t, name, arg);
    }
    t
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
        self.made.push(key.0.0.span());
        let term = SurfaceTerm::new(kind, span);
        self.spans.insert(key, term.clone());
        term
    }

    fn var(&mut self, name: impl Into<Name>) -> SurfaceTerm {
        self.term(TermKind::Var(name.into()))
    }

    fn class(&self, name: &Name) -> Option<&ClassDecl> {
        self.report.classes.get(name)
    }

    /// Whether a class has no method to run (`PolicyState`): it has no
    /// dictionary, so it stays as written, with its instances and the
    /// constraints that name it, and every check after the expansion still
    /// sees a missing instance. A function that asks for it takes nothing
    /// more, an `extern` one included.
    fn kept(&self, class: &Name) -> bool {
        self.class(class)
            .is_some_and(|c| !c.methods.iter().any(super::type_functions::executable))
    }

    fn kept_or_structural(&self, c: &Constraint) -> bool {
        STRUCTURAL.contains(&c.class.as_str()) || self.kept(&c.class)
    }

    fn top(&mut self, s: Stmt, out: &mut Vec<Stmt>) {
        match s {
            Stmt::Class(c) if self.kept(&c.name) => out.push(Stmt::Class(c)),
            Stmt::Instance(i) if self.kept(&i.class) => {
                let mut i = Stmt::Instance(i);
                walk::roots(&mut i, &mut |t| self.go(t));
                out.push(i);
            }
            Stmt::Class(_) => {}
            Stmt::Instance(i) => {
                // A method that is not executable is a type, never run.
                for m in i
                    .methods
                    .iter()
                    .filter(|m| super::type_functions::executable(m))
                {
                    let f = self.instance_method(&i, m);
                    out.push(Stmt::Fn(f));
                }
            }
            Stmt::Fn(mut f) => {
                self.fn_decl(&mut f);
                out.push(Stmt::Fn(f));
            }
            Stmt::Extern {
                mut fns,
                instances,
                types,
                structs,
                enums,
                span,
            } => {
                // The body of a fallback is expanded as an ordinary function's
                // is, with the dictionaries its `where` asks for; it is kept
                // out of the walk of the rest of the block below.
                let mut bodies = Vec::new();
                for f in &mut fns {
                    if tauto_surface::surface::extern_fn_has_body(f) {
                        self.fn_decl(f);
                        let placeholder =
                            SurfaceTerm::new(TermKind::Other("ExternFn".into()), f.span);
                        bodies.push(Some(std::mem::replace(&mut f.body, placeholder)));
                        continue;
                    }
                    bodies.push(None);
                    let kept: Vec<bool> = f
                        .where_
                        .iter()
                        .map(|c| self.kept_or_structural(c))
                        .collect();
                    let mut kept = kept.into_iter();
                    f.where_.retain(|_| kept.next().unwrap_or(false));
                }
                let mut other = Stmt::Extern {
                    fns,
                    instances,
                    types,
                    structs,
                    enums,
                    span,
                };
                walk::roots(&mut other, &mut |t| self.go(t));
                if let Stmt::Extern { fns, .. } = &mut other {
                    for (f, body) in fns.iter_mut().zip(bodies) {
                        if let Some(body) = body {
                            f.body = body;
                        }
                    }
                }
                out.push(other);
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
        let class = self.class(&i.class).expect("checked class");
        // The product `A × B` is named as the rest of the program is: by reference once the
        // program's names are resolved. Multi-arg classes key every head (`C(i64, Bool)` → `i64@Bool`).
        let resolved = member_fn(class, &m.name).as_global().is_some();
        f.name = instance_fn(class, &m.name, &instance_heads_name(i, resolved));
        f.span = m.span;
        f.bounds.resize(f.generics.len(), None);
        let mut bounds = i.bounds.clone();
        bounds.resize(i.generics.len(), None);
        bounds.append(&mut f.bounds);
        f.bounds = bounds;
        f.generics.splice(0..0, i.generics.iter().cloned());
        f.unused_generics
            .splice(0..0, i.unused_generics.iter().cloned());
        // The instance's evidence comes first, the method's own after, as a
        // call through the class passes them.
        f.where_ = i.where_.iter().chain(&m.where_).cloned().collect();
        self.fn_decl(&mut f);
        f
    }

    /// A function that asks for a class takes the class's methods, after its
    /// own parameters; its body is expanded.
    fn dictionary_parameter(
        &mut self,
        class: &ClassDecl,
        method: &FnDecl,
        parameters: &[Name],
    ) -> Name {
        let member = member_fn(class, &method.name);
        let key = assume_dictionary_key(parameters);
        self.dictionaries
            .entry((member.clone(), key.clone()))
            .or_insert_with(|| {
                tauto_surface::identity::LocalRef::fresh(format!("{member}@{key}")).into()
            })
            .clone()
    }

    fn fn_decl(&mut self, f: &mut FnDecl) {
        let mut added = Vec::new();
        for c in &f.where_ {
            let Some(class) = self.class(&c.class).cloned() else {
                continue;
            };
            let args: Vec<SurfaceTerm> = std::iter::once(c.ty.clone())
                .chain(c.arguments.iter().cloned())
                .collect();
            if args.iter().any(|a| !matches!(&*a.kind, TermKind::Var(_))) {
                continue;
            }
            let keys: Vec<Name> = args
                .iter()
                .map(|a| match &*a.kind {
                    TermKind::Var(n) => n.clone(),
                    _ => unreachable!(),
                })
                .collect();
            for m in class
                .methods
                .iter()
                .filter(|m| super::type_functions::executable(m))
            {
                added.push((
                    self.dictionary_parameter(&class, m, &keys),
                    class.clone(),
                    m.clone(),
                    args.clone(),
                ));
            }
        }
        // `@assoc(H, C::t(G))`: in the methods of `C(G)`, `C::t(…)` is `H`.
        let associated: Vec<(Name, Name, Name)> = f
            .where_
            .iter()
            .filter(|c| c.class.as_str() == super::type_functions::ASSOC)
            .filter_map(|c| {
                let TermKind::Var(h) = &*c.ty.kind else {
                    return None;
                };
                let TermKind::App {
                    function,
                    arguments,
                } = &*c.arguments.first()?.kind
                else {
                    return None;
                };
                let (TermKind::Var(member), [g]) = (&*function.kind, arguments.as_slice()) else {
                    return None;
                };
                let TermKind::Var(g) = &*g.kind else {
                    return None;
                };
                Some((member.clone(), g.clone(), h.clone()))
            })
            .collect();
        self.origin = Some((f.body.id(), true));
        self.count = 0;
        for (name, class, m, args) in added {
            let mut ty = self.method_type(&class, &m, &args);
            if let Some(TermKind::Var(g)) = args.first().map(|a| &*a.kind) {
                walk::term(&mut ty, &mut |t| {
                    let head = match &*t.kind {
                        TermKind::App { function, .. } => function.as_ref(),
                        _ => return,
                    };
                    if let TermKind::Var(n) = &*head.kind
                        && let Some((_, _, h)) =
                            associated.iter().find(|(m, x, _)| m == n && x == g)
                    {
                        *t = t.with_kind(TermKind::Var(h.clone()), t.span);
                    }
                });
            }
            f.params.push(name.into());
            f.param_types.push(Some(ty));
            f.borrows.push(None);
        }
        let kept: Vec<bool> = f
            .where_
            .iter()
            .map(|c| self.kept_or_structural(c))
            .collect();
        let mut kept = kept.into_iter();
        f.where_.retain(|_| kept.next().unwrap_or(false));
        self.go(&mut f.body);
    }

    fn method_type(
        &mut self,
        class: &ClassDecl,
        m: &FnDecl,
        class_args: &[SurfaceTerm],
    ) -> SurfaceTerm {
        let at = |t: &SurfaceTerm| instantiate_class_args(t, class, class_args);
        let mut params = Vec::new();
        // The method's own type generics make the dictionary polymorphic:
        // `(A: Shared, B: Type, …)` leads.
        for (n, g) in m.generics.iter().enumerate() {
            let kind = match m.bounds.get(n).cloned().flatten() {
                None => "affine".to_string(),
                // `shared+noborrow` stays whole: the reader of the type
                // keeps the `NoBorrow` of the binder.
                Some(b) => match super::without_no_borrow(&b) {
                    (None, true) => b.to_string(),
                    (Some(k), _) if Kind::parse(&k).is_some() => b.to_string(),
                    _ => continue,
                },
            };
            let kind = self.term(TermKind::Var(kind.into()));
            params.push((Some(g.clone()), kind));
        }
        for (n, t) in m.param_types.iter().enumerate() {
            let t = match t {
                Some(t) => at(t),
                None => self.unit_type(),
            };
            let t = match m.borrows.get(n).copied().flatten() {
                Some(mutable) => self.term(TermKind::Borrow {
                    orig: false,
                    rc: false,
                    mutable,
                    term: Box::new(t),
                }),
                None => t,
            };
            params.push((None, t));
        }
        // The evidence the method's own `where` asks for follows the
        // parameters, one method value for each method of each class.
        for c in &m.where_ {
            let Some(asked) = self.class(&c.class).cloned() else {
                continue;
            };
            let nested: Vec<SurfaceTerm> = std::iter::once(c.ty.clone())
                .chain(c.arguments.iter().cloned())
                .map(|a| at(&a))
                .collect();
            for held in asked
                .methods
                .iter()
                .filter(|m| super::type_functions::executable(m))
            {
                let ty = self.method_type(&asked, held, &nested);
                params.push((None, ty));
            }
        }
        let result = match &m.result {
            Some(r) => at(r),
            None => self.unit_type(),
        };
        self.term(TermKind::Pi {
            params,
            unused: Vec::new(),
            result: Box::new(result),
            effects: m.effects.clone(),
        })
    }

    /// The unit `#()`.
    fn unit(&mut self) -> SurfaceTerm {
        self.var(tauto_surface::bindings::star_reference().clone())
    }

    /// The unit type `Unit`.
    fn unit_type(&mut self) -> SurfaceTerm {
        self.var(tauto_surface::bindings::unit_reference().clone())
    }

    fn evidence(&self, t: &SurfaceTerm) -> Option<Vec<Ev>> {
        self.report.evidence.get(&t.id()).cloned()
    }

    /// `C::m`, the method of a class. A static reference reads as one name
    /// (`Var("Ord::compare")`); a function `C::m` of a module `C` is not one.
    fn method_use(&self, t: &SurfaceTerm) -> Option<(Name, String)> {
        match &*t.kind {
            TermKind::Field { base, name } => match &*base.kind {
                TermKind::Var(c) if self.class(c).is_some() => Some((c.clone(), name.clone())),
                _ => None,
            },
            TermKind::Var(reference) => self.report.classes.values().find_map(|class| {
                class
                    .methods
                    .iter()
                    .find(|method| member_fn(class, &method.name) == *reference)
                    .map(|method| (class.name.clone(), method.name.to_string()))
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
        let host =
            |t: &SurfaceTerm| matches!(&*t.kind, TermKind::Var(n) if self.externs.contains(n));
        let own = self.evidence(t).filter(|_| !host(t));
        let callee = match &*t.kind {
            TermKind::App { function, .. } if !host(function) => self.evidence(function),
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
                // `C(T)::m(…)`: the class's arguments chose the instance; the
                // function the call becomes does not take them.
                if self.method_use(function).is_some() {
                    drop_class_arguments(arguments);
                }
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

    fn call_target(
        &mut self,
        function: &SurfaceTerm,
        evs: &[Ev],
    ) -> (SurfaceTerm, Vec<SurfaceTerm>) {
        if let Some((class, method)) = self.method_use(function) {
            // The evidence for the method's own `where` follows the class's.
            let own = self.dictionaries(evs.get(1..).unwrap_or_default());
            let (target, mut extra) = match evs.first() {
                Some(Ev::Assume(_, gs)) => {
                    let descriptor = self.class(&class).expect("checked class").clone();
                    let method = descriptor
                        .methods
                        .iter()
                        .find(|m| m.name.as_str() == method)
                        .expect("checked method");
                    let keys: Vec<Name> = gs.iter().map(|g| g.reference().clone()).collect();
                    let parameter = self.dictionary_parameter(&descriptor, method, &keys);
                    (self.var(parameter), Vec::new())
                }
                Some(ev @ Ev::Union(..)) => {
                    let descriptor = self.class(&class).expect("checked class").clone();
                    let method = descriptor
                        .methods
                        .iter()
                        .find(|m| m.name.as_str() == method)
                        .expect("checked method")
                        .clone();
                    let ev = ev.clone();
                    (self.method_value(&descriptor, &method, &ev), Vec::new())
                }
                Some(Ev::Inst(_, head, _, subs)) => {
                    let callee = self.var(instance_fn(
                        self.class(&class).expect("checked class"),
                        &method,
                        head,
                    ));
                    (callee, self.dictionaries(subs))
                }
                _ => (function.clone(), Vec::new()),
            };
            extra.extend(own);
            return (target, extra);
        }
        (function.clone(), self.dictionaries(evs))
    }

    /// The arguments that stand for the evidence: one for each method of each
    /// class.
    fn dictionaries(&mut self, evs: &[Ev]) -> Vec<SurfaceTerm> {
        let mut out = Vec::new();
        for ev in evs {
            let class = match ev {
                Ev::Assume(c, _) | Ev::Inst(c, ..) | Ev::Union(c, _) => c,
                _ => continue,
            };
            let Some(class) = self.class(class).cloned() else {
                continue;
            };
            // A method that is not executable is a type: no dictionary holds it.
            for m in class
                .methods
                .iter()
                .filter(|m| super::type_functions::executable(m))
            {
                out.push(self.method_value(&class, m, ev));
            }
        }
        out
    }

    fn method_value(&mut self, class: &ClassDecl, m: &FnDecl, ev: &Ev) -> SurfaceTerm {
        match ev {
            Ev::Assume(_, gs) => {
                let keys: Vec<Name> = gs.iter().map(|g| g.reference().clone()).collect();
                let parameter = self.dictionary_parameter(class, m, &keys);
                self.var(parameter)
            }
            Ev::Inst(_, head, _, subs) => {
                let name = instance_fn(class, &m.name, head);
                let extra = self.dictionaries(subs);
                if extra.is_empty() {
                    return self.var(name);
                }
                let names: Vec<String> = (0..m.params.len())
                    .map(|n| format!("{}@{n}", m.name))
                    .collect();
                // The method's own evidence is passed through, after the
                // instance's.
                let held = m
                    .where_
                    .iter()
                    .filter_map(|c| self.class(&c.class).cloned())
                    .flat_map(|c| {
                        c.methods
                            .iter()
                            .filter(|m| super::type_functions::executable(m))
                            .map(|held| format!("{}@{}", member_fn(&c, &held.name), m.name))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                let mut arguments: Vec<SurfaceTerm> =
                    names.iter().map(|n| self.var(n.clone())).collect();
                arguments.extend(extra);
                arguments.extend(held.iter().map(|n| self.var(n.clone())));
                let callee = self.var(name);
                let call = self.term(TermKind::App {
                    function: Box::new(callee),
                    arguments,
                });
                let mut borrows = m.borrows.clone();
                let mut names = names;
                names.extend(held);
                borrows.resize(names.len(), None);
                self.closure(names, borrows, call)
            }
            // `(x) => match x { y0: T0 => debug@T0(&y0), … }`: the method of
            // the member the union holds.
            Ev::Union(_, members) => {
                let x = "debug@union".to_string();
                // The parameter's type is not known where the `match` is
                // checked: the scrutinee says it, `x: &{T0 | T1 | …}`.
                let written: Vec<SurfaceTerm> = members
                    .iter()
                    .map(|(ty, _)| self.ty_term(ty).expect("a member with a head"))
                    .collect();
                let union = self.term(TermKind::Union(written));
                let ty = union;
                let at = self.var(x.clone());
                let scrutinee = self.term(TermKind::Ascribe {
                    term: Box::new(at),
                    ty: Box::new(ty),
                });
                let mut arms = Vec::new();
                for (i, (ty, ev)) in members.iter().enumerate() {
                    let y = format!("debug@member{i}");
                    let ty = self.ty_term(ty).expect("a member with a head");
                    let f = self.method_value(class, m, ev);
                    let at = self.var(y.clone());
                    let borrowed = self.term(TermKind::Borrow {
                        orig: false,
                        rc: false,
                        mutable: false,
                        term: Box::new(at),
                    });
                    let body = self.term(TermKind::App {
                        function: Box::new(f),
                        arguments: vec![borrowed],
                    });
                    arms.push(tauto_surface::surface::MatchArm {
                        pattern: tauto_surface::surface::Pattern::Typed {
                            name: Name::from(y),
                            ty: Box::new(ty),
                            unused: None,
                        },
                        guard: None,
                        goal: None,
                        body,
                    });
                }
                let body = self.term(TermKind::Match {
                    scrutinee: Box::new(scrutinee),
                    result: None,
                    binder: None,
                    binder_unused: None,
                    arms,
                });
                self.closure(vec![x], m.borrows.clone(), body)
            }
            _ => self.unit(),
        }
    }

    /// A member's type as written.
    fn ty_term(&mut self, t: &super::Ty) -> Option<SurfaceTerm> {
        let written = super::indices::surface_of(t, Span::new(0, 0))?;
        Some(self.respan(&written))
    }

    fn respan(&mut self, t: &SurfaceTerm) -> SurfaceTerm {
        match &*t.kind {
            TermKind::Var(n) => self.var(n.clone()),
            TermKind::App {
                function,
                arguments,
            } => {
                let function = self.respan(function);
                let arguments = arguments.iter().map(|a| self.respan(a)).collect();
                self.term(TermKind::App {
                    function: Box::new(function),
                    arguments,
                })
            }
            other => self.term(other.clone()),
        }
    }

    fn closure(
        &mut self,
        params: Vec<String>,
        borrows: Vec<Option<bool>>,
        body: SurfaceTerm,
    ) -> SurfaceTerm {
        let lam = self.term(TermKind::Lam {
            params: params.into_iter().map(Name::from).collect(),
            unused_params: Vec::new(),
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
            let found = self.class(&class).cloned();
            let method = found
                .as_ref()
                .and_then(|c| c.methods.iter().find(|m| m.name.as_str() == method));
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

/// A local function is inside the type parameters of the function it is in,
/// and may assume their `where` (`types.rs`). It is given the enclosing
/// `where` as its own, so that it takes the dictionaries as parameters, and
/// its calls in the enclosing function pass the ones that function has: a
/// local function captures no dictionary.
fn inherit_local_where(program: &mut Program) {
    fn in_fn(f: &mut FnDecl, outer: &[Constraint]) {
        for c in outer {
            let shadowed = match &*c.ty.kind {
                TermKind::Var(g) => f.generics.iter().any(|n| n.as_str() == g.as_str()),
                _ => true,
            };
            let written = f
                .where_
                .iter()
                .any(|w| w.class == c.class && same_term(&w.ty, &c.ty));
            if !shadowed && !written {
                f.where_.push(c.clone());
            }
        }
        if f.where_.is_empty() {
            return;
        }
        let here = f.where_.clone();
        walk::term(&mut f.body, &mut |t| {
            if let TermKind::Block(stmts) = &*t.kind
                && stmts.iter().any(|s| matches!(s, Stmt::Fn(_)))
            {
                let TermKind::Block(stmts) = std::sync::Arc::make_mut(&mut t.kind) else {
                    unreachable!()
                };
                for s in stmts {
                    if let Stmt::Fn(g) = s {
                        in_fn(g, &here);
                    }
                }
            }
        });
    }
    fn same_term(a: &SurfaceTerm, b: &SurfaceTerm) -> bool {
        matches!((&*a.kind, &*b.kind), (TermKind::Var(x), TermKind::Var(y)) if x.as_str() == y.as_str())
    }
    fn stmts(ss: &mut [Stmt]) {
        for s in ss {
            match s {
                Stmt::Fn(f) if !f.where_.is_empty() => in_fn(f, &[]),
                Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => stmts(items),
                _ => {}
            }
        }
    }
    stmts(&mut program.stmts);
}

/// The implicit record of `C(T)::m(…)` without the class's arguments, and
/// no record when nothing else is named.
fn drop_class_arguments(arguments: &mut Vec<SurfaceTerm>) {
    let Some(first) = arguments.first_mut() else {
        return;
    };
    let TermKind::Record { name, fields, .. } = Arc::make_mut(&mut first.kind) else {
        return;
    };
    if name.spelling() != Some(tauto_surface::IMPLICITS) {
        return;
    }
    fields.retain(|(f, _)| tauto_surface::class_argument_index(f).is_none());
    if fields.is_empty() {
        arguments.remove(0);
    }
}

/// A method of an instance the program writes, as the class expansion makes
/// it a function: what an export of the instance names.
#[derive(Debug, Clone)]
pub struct InstanceMethod {
    /// The function the expansion makes of it.
    pub function: Name,
    pub class: Name,
    /// Where the class is declared.
    pub class_span: Span,
    /// The class's arguments the instance is for: `Circle` of `Named(Circle)`.
    pub heads: Vec<SurfaceTerm>,
    pub method: Name,
    /// Whether the instance has generics (`instance Named(List(T))`).
    pub generic: bool,
    pub span: Span,
}

/// The methods that run of the instances `program` and `per_file` write, read
/// before the class expansion makes them functions.
pub fn instance_methods(program: &Program, per_file: &[Vec<Stmt>]) -> Vec<InstanceMethod> {
    let all = || {
        prelude_source_for(program)
            .stmts
            .iter()
            .chain(&program.stmts)
            .chain(per_file.iter().flatten())
    };
    let classes: HashMap<&Name, &ClassDecl> = all()
        .filter_map(|s| match s {
            Stmt::Class(c) => Some((&c.name, c)),
            _ => None,
        })
        .collect();
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for s in program.stmts.iter().chain(per_file.iter().flatten()) {
        let Stmt::Instance(i) = s else { continue };
        if super::debug::is_made(i.span) || !seen.insert(i.span) {
            continue;
        }
        let Some(class) = classes.get(&i.class) else {
            continue;
        };
        for m in i
            .methods
            .iter()
            .filter(|m| super::type_functions::executable(m))
        {
            if !class.methods.iter().any(|c| c.name == m.name) {
                continue;
            }
            let resolved = member_fn(class, &m.name).as_global().is_some();
            out.push(InstanceMethod {
                function: instance_fn(class, &m.name, &instance_heads_name(i, resolved)),
                class: i.class.clone(),
                class_span: class.span,
                heads: std::iter::once(&i.head)
                    .chain(&i.arguments)
                    .cloned()
                    .collect(),
                method: m.name.clone(),
                generic: !i.generics.is_empty(),
                span: m.span,
            });
        }
    }
    out
}
