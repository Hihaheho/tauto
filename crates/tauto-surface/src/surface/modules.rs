//! `module M { … }` and the names `M::f`: modules
//! are flattened where the program is read, so what follows sees plain names
//! with `::` in them (`File::open`).
//!
//! Functions (and the functions of `extern` blocks), theorems and types
//! (`struct`, `enum`, `inductive`) take the module's name: a type `T` of
//! `module M` is `M::T`, and its constructor `C` is `M::T::C` (a struct's one
//! constructor is the type's name, `M::T`). Inside the module they are written
//! `T`, `C` and `T::C`; outside, `M::T` and `M::T::C`. Effects take the
//! module path as well.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::span::Span;
use tauto_message::{Message, msg};

use super::program::{ExportAlias, FnDecl, Handler, Pattern, Stmt, Vis};
use super::qualify::SEPARATOR;
use super::{Name, SurfaceTerm, TermId, TermKind};

/// Flattens the modules of `stmts`, and writes out the sets of effects
/// (`effect_sets`).
pub fn resolve(stmts: Vec<Stmt>) -> (Vec<Stmt>, Vec<(Message, Span)>) {
    resolve_with(stmts, &super::effect_sets::Sets::new(), &[])
}

/// Flattens module names against the prelude without consuming effect sets.
/// `ctors` are the constructors the files read before declare: a pattern
/// that writes one alone matches it, even when a module of the prelude has
/// its name (`Pending` of an imported `enum State { Pending, … }` is not the
/// prelude's module `Pending`).
pub fn flatten_in_prelude(
    stmts: Vec<Stmt>,
    ctors: &HashSet<String>,
) -> (Vec<Stmt>, Vec<(Message, Span)>) {
    let mut r = Resolver::default();
    r.know(prelude_fns().iter().map(|n| n.as_str()));
    r.program_ctors = ctors.clone();
    flatten_with(stmts, r)
}

/// The constructors `stmts` declare, by their full names and their short
/// ones, as a pattern may write them.
pub fn declared_ctors(stmts: &[Stmt], names: &mut HashSet<String>) {
    constructors(stmts, names)
}

/// [`resolve`] where the functions of the prelude's modules (`Code.term`,
/// `Eq.trans`) are known: statements read apart from the program, such as
/// the files before a macro, name them as the program does.
pub fn resolve_in_prelude(stmts: Vec<Stmt>) -> (Vec<Stmt>, Vec<(Message, Span)>) {
    resolve_in_prelude_against(stmts, std::iter::empty())
}

/// [`resolve_in_prelude`] of statements that also use the functions `known`
/// declared elsewhere.
pub fn resolve_in_prelude_against<'a>(
    stmts: Vec<Stmt>,
    known: impl IntoIterator<Item = &'a str>,
) -> (Vec<Stmt>, Vec<(Message, Span)>) {
    let mut r = Resolver::default();
    r.know(prelude_fns().iter().map(|n| n.as_str()));
    r.know(known);
    // The files read apart are joined here, though a file sees only the
    // modules of the files it imports: whether a local takes the name of a
    // module its file sees was told when that file was read with its imports
    // ([`flatten_files`]), and the modules of the others are not its to take.
    r.joined_files = true;
    let (mut stmts, mut errors) = flatten_with(stmts, r);
    errors.extend(super::effect_sets::expand(
        &mut stmts,
        &super::effect_sets::Sets::new(),
    ));
    (stmts, errors)
}

fn prelude_fns() -> &'static [String] {
    static NAMES: std::sync::OnceLock<Vec<String>> = std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        let mut names = Vec::new();
        for text in [
            crate::nibstd::PRELUDE,
            crate::nibstd::KERNEL,
            include_str!("../../../tauto-kernel/src/prelude_nat.taut"),
            include_str!("../../../tauto-kernel/src/prelude_deq.taut"),
            include_str!("../../../tauto-kernel/src/prelude_eq.taut"),
        ] {
            if let Ok(p) = super::program::parse_builtin_at(text, 0) {
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
) -> (Vec<Stmt>, Vec<(Message, Span)>) {
    resolve_with_files(stmts, others, known, false)
}

/// [`resolve_with`] of the statements of several files joined: a file sees
/// only the modules of the files it imports, and a local that takes the name
/// of a module its file sees was reported when that file was read with its
/// imports ([`flatten_files`]). Here the modules of the others are not its
/// to take.
pub fn resolve_joined_files(
    stmts: Vec<Stmt>,
    others: &super::effect_sets::Sets,
    known: &[String],
) -> (Vec<Stmt>, Vec<(Message, Span)>) {
    resolve_with_files(stmts, others, known, true)
}

fn resolve_with_files(
    stmts: Vec<Stmt>,
    others: &super::effect_sets::Sets,
    known: &[String],
    joined_files: bool,
) -> (Vec<Stmt>, Vec<(Message, Span)>) {
    let (mut stmts, mut errors) = if known.is_empty() && !joined_files {
        flatten(stmts)
    } else {
        let mut r = Resolver::default();
        r.know(known.iter().map(|k| k.as_str()));
        r.joined_files = joined_files;
        flatten_with(stmts, r)
    };
    errors.extend(super::effect_sets::expand(&mut stmts, others));
    (stmts, errors)
}

/// A term written outside a module already names its declarations by their path.
pub fn resolve_term_against<'a>(
    term: &SurfaceTerm,
    _known: impl IntoIterator<Item = &'a str>,
) -> SurfaceTerm {
    term.clone()
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
    _modules: &[String],
    imports: Option<&[Vec<usize>]>,
    warnings: &mut Vec<(Message, Span)>,
) -> Vec<(Message, Span)> {
    if imports.is_none() && !files.iter().any(|file| has_module(file)) {
        return Vec::new();
    }
    let base: Vec<String> = known.into_iter().map(str::to_string).collect();
    let by_file: Vec<Vec<String>> = files
        .iter()
        .map(|f| {
            let mut names = declared(f);
            names.extend(declared_flat(f));
            names
        })
        .collect();
    let by_top: Vec<HashSet<String>> = files.iter().map(|f| top_level(f)).collect();
    let mut errors = Vec::new();
    for (i, f) in files.iter_mut().enumerate() {
        // A file knows the modules of the prelude, of itself and of the files
        // it imports directly; the other files of the program do not change
        // what its names mean.
        let mut r = Resolver {
            check_imported_paths: imports.is_some(),
            ..Resolver::default()
        };
        match imports {
            Some(imports) => {
                r.know(by_file[i].iter().map(|k| k.as_str()));
                for &j in &imports[i] {
                    if j != i {
                        r.know(by_file[j].iter().map(|k| k.as_str()));
                    }
                }
            }
            None => {
                for names in &by_file {
                    r.know(names.iter().map(|k| k.as_str()));
                }
            }
        }
        r.binding_modules = r.modules.clone();
        // A file of the library's prelude reaches `files` without its
        // declarations (its names arrive with `base`), so the modules it adds
        // to what a file sees are those `hidden_prelude` lists for the
        // prelude files this one imports.
        if let Some(imports) = imports {
            let stems: HashSet<&str> = imports[i]
                .iter()
                .filter_map(|&j| {
                    _modules
                        .get(j)?
                        .strip_prefix(super::qualify::BUILTIN_MODULE)?
                        .strip_prefix(SEPARATOR)
                })
                .collect();
            if !stems.is_empty() {
                for (name, files) in super::qualify::hidden_prelude() {
                    if files.iter().any(|f| stems.contains(f.as_str())) {
                        let mut at = 0;
                        while let Some(k) = name[at..].find(SEPARATOR) {
                            r.binding_modules.insert(name[..at + k].to_string());
                            at += k + SEPARATOR.len();
                        }
                        if at == 0 && r.modules.contains(name.as_str()) {
                            r.binding_modules.insert(name.clone());
                        }
                    }
                }
            }
        }
        r.know(base.iter().map(|k| k.as_str()));
        r.program_ctors = ctors.clone();
        r.outer
            .extend(super::qualify::prelude_names().iter().cloned());
        let visible: Vec<usize> = match imports {
            Some(imports) => imports[i].clone(),
            None => (0..by_top.len()).collect(),
        };
        for &j in &visible {
            r.outer.extend(by_top[j].iter().cloned());
        }
        // The files this one reaches only through its imports' imports: what
        // it may have meant by a name it does not see.
        if let Some(imports) = imports {
            let mut seen: HashSet<usize> = visible.iter().copied().chain([i]).collect();
            let mut stack = visible.clone();
            while let Some(j) = stack.pop() {
                for &k in &imports[j] {
                    if seen.insert(k) {
                        r.unseen_outer.extend(by_top[k].iter().cloned());
                        stack.push(k);
                    }
                }
            }
        }
        let (stmts, mut e, mut w) = flatten_warned(std::mem::take(f), r);
        *f = stmts;
        errors.append(&mut e);
        warnings.append(&mut w);
    }
    errors
}

fn flatten(stmts: Vec<Stmt>) -> (Vec<Stmt>, Vec<(Message, Span)>) {
    if !has_module(&stmts) {
        return (stmts, Vec::new());
    }
    flatten_with(stmts, Resolver::default())
}

fn constructors(statements: &[Stmt], names: &mut HashSet<String>) {
    for statement in statements {
        match statement {
            Stmt::Struct(data) | Stmt::Enum(data) => {
                for constructor in &data.constructors {
                    names.insert(constructor.name.to_string());
                    names.insert(constructor.name.rsplit("::").next().unwrap().to_string());
                }
            }
            Stmt::Inductive(data) => {
                for constructor in &data.constructors {
                    names.insert(constructor.name.to_string());
                    names.insert(constructor.name.rsplit("::").next().unwrap().to_string());
                }
            }
            Stmt::Module { items, .. } | Stmt::Mutual { items, .. } => constructors(items, names),
            Stmt::Attributed { stmt, .. } => constructors(std::slice::from_ref(stmt), names),
            _ => {}
        }
    }
}

/// The short names the top level of `stmts` declares, outside every module.
fn top_level(stmts: &[Stmt]) -> HashSet<String> {
    let mut names = HashSet::new();
    for s in stmts {
        super::qualify::declared(s, &mut |n| {
            if !n.contains(SEPARATOR) {
                names.insert(n.to_string());
            }
        });
    }
    names
}

fn flatten_with(stmts: Vec<Stmt>, r: Resolver) -> (Vec<Stmt>, Vec<(Message, Span)>) {
    let (out, errors, _) = flatten_warned(stmts, r);
    (out, errors)
}

/// [`flatten_with`], and the warnings of what it read.
fn flatten_warned(
    stmts: Vec<Stmt>,
    mut r: Resolver,
) -> (Vec<Stmt>, Vec<(Message, Span)>, Vec<(Message, Span)>) {
    if !has_module(&stmts) && !r.check_imported_paths {
        return (stmts, Vec::new(), Vec::new());
    }
    constructors(&stmts, &mut r.program_ctors);
    r.outer
        .extend(super::qualify::BUILTIN_TYPES.iter().map(|n| n.to_string()));
    r.outer.extend(top_level(&stmts));
    r.classes = stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Class(c) => Some(c.name.to_string()),
            _ => None,
        })
        .collect();
    r.collect(&stmts, &mut Vec::new());
    r.reexports(&stmts, &mut Vec::new());
    let mut out = Vec::new();
    r.flatten(stmts, &mut Vec::new(), &mut out);
    (out, r.errors.into_inner(), r.warnings.into_inner())
}

fn has_module(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| {
        matches!(
            s,
            Stmt::Module { .. } | Stmt::Reexport { aliases: None, .. }
        )
    })
}

#[derive(Clone, Copy)]
enum EffectAccess {
    Row,
    Perform,
    Handle,
}

#[derive(Default)]
struct Resolver {
    /// The statements are the files of a program joined, not one file's.
    joined_files: bool,
    check_imported_paths: bool,
    modules: HashSet<String>,
    binding_modules: HashSet<String>,
    explicit_modules: HashMap<String, Vis>,
    members: HashMap<String, Vis>,
    effects: HashMap<String, Vis>,
    effect_scopes: HashMap<String, TermId>,
    exports: HashMap<String, String>,
    effect_exports: HashMap<String, String>,
    fns: HashSet<String>,
    types: HashSet<String>,
    /// The constructors of the types in a module, by the module and the short
    /// name (`A::C`), each with its full name (`A::T::C`); a short name two types
    /// of one module share is `None`, written `T::C`.
    ctors: std::collections::HashMap<String, Option<String>>,
    /// Every class: its members are the flat names `Class::member`, so a
    /// module of the same name would put its functions among them.
    classes: HashSet<String>,
    errors: RefCell<Vec<(Message, Span)>>,
    warnings: RefCell<Vec<(Message, Span)>>,
    /// The constructors of the program: a pattern that writes one alone
    /// matches it and binds nothing (the names are not qualified yet).
    program_ctors: HashSet<String>,
    locals: RefCell<Vec<String>>,
    /// The short names declared outside every module: the prelude's (and the
    /// builtin types), and the top level of this file and of the files it
    /// imports. Writing such a name short in a module that also declares it
    /// is ambiguous ([`Resolver::name_at`]).
    outer: HashSet<String>,
    /// The short names declared outside every module by a file of the program
    /// this file does not import: not in `outer`, so a module's own
    /// declaration of the name is read where it is written short, which the
    /// writer may not have meant ([`Resolver::name_at`]).
    unseen_outer: HashSet<String>,
}

/// The full names of the functions and theorems the modules of `stmts` declare: what another file
/// of the program may name.
pub fn declared(stmts: &[Stmt]) -> Vec<String> {
    let mut r = Resolver::default();
    r.collect(stmts, &mut Vec::new());
    // A function written with its prefix (`fn Nat::add`) is declared as one of a module is.
    r.fns.extend(declared_flat(stmts));
    r.fns.into_iter().collect()
}

/// The names of functions and theorems of `stmts` that are already full (`M::f`).
pub fn declared_flat(stmts: &[Stmt]) -> Vec<String> {
    let mut names = Vec::new();
    for s in stmts {
        match s {
            Stmt::Fn(f) => names.push(f.name.to_string()),
            Stmt::Theorem(t) | Stmt::Def(t) => names.push(t.name.to_string()),
            Stmt::Extern { fns, .. } => names.extend(fns.iter().map(|f| f.name.to_string())),
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
                Stmt::Module {
                    name,
                    vis,
                    items,
                    span,
                } => {
                    let full = join(path, name);
                    if self.classes.contains(&full)
                        || (!path.is_empty() && self.classes.contains(name))
                    {
                        self.errors.borrow_mut().push((
                            msg!(
                                "surface-module-collides-with-class",
                                module = &full,
                                name = name
                            ),
                            *span,
                        ));
                    }
                    if self.explicit_modules.insert(full.clone(), *vis).is_some() {
                        self.errors.borrow_mut().push((
                            msg!("surface-module-duplicate", name = full.as_str()),
                            *span,
                        ));
                    }
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
                    let full = join(path, &f.name);
                    self.members.insert(full.clone(), f.vis);
                    self.fns.insert(full);
                }
                Stmt::Theorem(t) | Stmt::Def(t) if !path.is_empty() => {
                    let full = join(path, &t.name);
                    self.members.insert(full.clone(), t.vis);
                    self.fns.insert(full);
                }
                Stmt::Effect(e) if !path.is_empty() => {
                    let full = join(path, &e.name);
                    self.effect_scopes
                        .insert(full.clone(), TermId::fresh(e.span));
                    self.effects.insert(full, e.vis);
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

    fn reexports(&mut self, stmts: &[Stmt], path: &mut Vec<String>) {
        for s in stmts {
            match s {
                Stmt::Module { name, items, .. } => {
                    path.push(name.clone());
                    self.reexports(items, path);
                    path.pop();
                }
                Stmt::Reexport {
                    module,
                    names,
                    span,
                    aliases: None,
                } => {
                    let module = join(path, module);
                    if !self.explicit_modules.contains_key(&module) {
                        self.errors.borrow_mut().push((
                            msg!("surface-module-unknown", name = module.as_str()),
                            *span,
                        ));
                        continue;
                    }
                    let mut selected = HashSet::new();
                    for (name, at) in names {
                        if !selected.insert(name) {
                            self.errors.borrow_mut().push((
                                msg!("surface-module-export-duplicate", name = name.as_str()),
                                *at,
                            ));
                            continue;
                        }
                        let original = join(std::slice::from_ref(&module), name);
                        let export = join(path, name.split('#').next().unwrap_or(name));
                        let mut found = false;
                        for (members, exports) in [
                            (&self.members, &mut self.exports),
                            (&self.effects, &mut self.effect_exports),
                        ] {
                            if members
                                .get(&original)
                                .is_some_and(|vis| *vis != Vis::Private)
                            {
                                if exports.contains_key(&export) {
                                    self.errors.borrow_mut().push((
                                        msg!(
                                            "surface-module-export-duplicate",
                                            name = export.as_str()
                                        ),
                                        *at,
                                    ));
                                } else {
                                    exports.insert(export.clone(), original.clone());
                                }
                                found = true;
                            }
                        }
                        if !found {
                            self.errors.borrow_mut().push((
                                msg!("surface-module-export", name = original.as_str()),
                                *at,
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn member_name(&self, name: &str, path: &[String], span: Span) -> String {
        if let Some(Vis::Private) = self.members.get(name) {
            self.check_member(name, path, span);
        }
        if self.locals.borrow().iter().any(|local| local == name) {
            return name.to_string();
        }
        self.exports
            .get(&join(path, name))
            .or_else(|| self.exports.get(name))
            .cloned()
            .unwrap_or_else(|| name.to_string())
    }

    fn check_member(&self, name: &str, path: &[String], span: Span) {
        if let Some((owner, _)) = name.rsplit_once(SEPARATOR)
            && !Self::inside(path, owner)
        {
            self.errors
                .borrow_mut()
                .push((msg!("surface-module-member-private", name = name), span));
        }
    }

    fn inside(path: &[String], owner: &str) -> bool {
        let path = path.join(SEPARATOR);
        path == owner
            || path
                .strip_prefix(owner)
                .is_some_and(|suffix| suffix.starts_with(SEPARATOR))
    }

    fn effect_ref(
        &self,
        name: &mut String,
        path: &[String],
        span: Span,
        access: EffectAccess,
    ) -> Option<TermId> {
        let qualified = (0..=path.len())
            .rev()
            .map(|depth| join(&path[..depth], name))
            .find(|candidate| self.effects.contains_key(candidate))
            .or_else(|| {
                self.effect_exports
                    .get(&join(path, name))
                    .or_else(|| self.effect_exports.get(name))
                    .cloned()
            });
        let qualified = qualified?;
        let vis = self.effects[&qualified];
        let (owner, _) = qualified.rsplit_once(SEPARATOR).expect("module effect");
        let inside = Self::inside(path, owner);
        if !inside {
            let message = match (vis, access) {
                (Vis::Private, _) => Some(msg!(
                    "surface-module-member-private",
                    name = qualified.as_str()
                )),
                (Vis::Handle, EffectAccess::Perform) => {
                    Some(msg!("surface-sealed-perform", name = name.as_str()))
                }
                (Vis::Pub, EffectAccess::Handle) => {
                    Some(msg!("surface-module-sealed-handle", name = name.as_str()))
                }
                _ => None,
            };
            if let Some(message) = message {
                self.errors.borrow_mut().push((message, span));
            }
        }
        let scope = inside.then_some(self.effect_scopes[&qualified]);
        *name = qualified;
        scope
    }

    fn row(&self, row: &mut [Name], path: &[String], span: Span) {
        for entry in row {
            if let Name::Written(written) = entry {
                *entry = Name::Written(Arc::new(written.edited(
                    |head| {
                        self.effect_ref(head, path, span, EffectAccess::Row);
                    },
                    |argument| self.term(argument, path),
                )));
            } else {
                entry.edit_spelling(|name| {
                    self.effect_ref(name, path, span, EffectAccess::Row);
                });
            }
        }
    }

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
                Stmt::Reexport {
                    module,
                    names,
                    aliases: None,
                    span,
                } => {
                    let full = join(path, &module);
                    let aliases = names
                        .iter()
                        .flat_map(|(leaf, _)| {
                            let target = join(std::slice::from_ref(&full), leaf);
                            let name = join(path, leaf.split('#').next().unwrap_or(leaf));
                            [(&self.exports, false), (&self.effect_exports, true)]
                                .into_iter()
                                .filter_map(move |(exports, effect)| {
                                    (exports.get(&name) == Some(&target)).then(|| ExportAlias {
                                        name: name.clone(),
                                        target: target.clone(),
                                        effect,
                                    })
                                })
                        })
                        .collect();
                    out.push(Stmt::Reexport {
                        module,
                        names,
                        aliases: Some(aliases),
                        span,
                    });
                }
                mut s => {
                    self.scoped(|| self.stmt(&mut s, path));
                    if !path.is_empty() {
                        self.rename(&mut s, path);
                        self.file_visibility(&mut s);
                    }
                    out.push(s);
                }
            }
        }
    }

    fn file_visibility(&self, statement: &mut Stmt) {
        let outside_private_module = |name: &str| {
            name.match_indices(SEPARATOR)
                .all(|(end, _)| self.explicit_modules.get(&name[..end]) != Some(&Vis::Private))
        };
        let visible = match statement {
            Stmt::Fn(f) => outside_private_module(&f.name),
            Stmt::Theorem(d) | Stmt::Def(d) => outside_private_module(&d.name),
            Stmt::Effect(e) => outside_private_module(&e.name),
            Stmt::Struct(d) | Stmt::Enum(d) => outside_private_module(&d.name),
            Stmt::Inductive(d) => outside_private_module(&d.name),
            Stmt::Macro { name, public, .. } => {
                *public &= outside_private_module(name);
                return;
            }
            Stmt::Extern { fns, .. } => {
                for f in fns {
                    if !outside_private_module(&f.name) {
                        f.vis = Vis::Private;
                    }
                }
                return;
            }
            Stmt::Mutual { items, .. } => {
                items.iter_mut().for_each(|s| self.file_visibility(s));
                return;
            }
            Stmt::Attributed { stmt, .. } => {
                self.file_visibility(stmt);
                return;
            }
            _ => return,
        };
        if !visible && let Some(vis) = statement.vis_mut() {
            *vis = Vis::Private;
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
            if let Some(row) = &mut f.effects {
                self.row(row, path, f.span);
            }
            self.term(&mut f.body, path);
        })
    }

    fn rename(&self, s: &mut Stmt, path: &[String]) {
        let ordinary = |name: &mut String| *name = join(path, name);
        match s {
            Stmt::Fn(f) => f.name.edit_spelling(ordinary),
            Stmt::Effect(e) => {
                let full = join(path, &e.name);
                if let Some(scope) = self.effect_scopes.get(&full) {
                    e.module_scope = Some((*scope, e.vis));
                }
                e.name.edit_spelling(|name| *name = full);
            }
            Stmt::Theorem(t) | Stmt::Def(t) => t.name.edit_spelling(ordinary),
            Stmt::Extern { fns, .. } => {
                for f in fns {
                    f.name.edit_spelling(|n| *n = join(path, n));
                }
            }
            Stmt::Mutual { items, .. } => {
                for i in items {
                    self.rename(i, path);
                }
            }
            Stmt::Attributed { stmt, .. } => self.rename(stmt, path),
            // A macro of a module is named, as its function is, by the path:
            // `module Trace { macro fn info … }` is called `Trace::info!(…)`.
            Stmt::Macro { name, function, .. } => {
                *name = join(path, name);
                *function = join(path, function);
            }
            Stmt::Struct(d) | Stmt::Enum(d) => {
                let full = if d.name.is_resolved() {
                    d.name.to_string()
                } else {
                    join(path, &d.name)
                };
                for c in &mut d.constructors {
                    if c.name.is_resolved() {
                        continue;
                    }
                    c.name = if c.name == d.name {
                        crate::identity::Name::Spelled(full.clone())
                    } else {
                        format!("{full}{SEPARATOR}{}", c.name).into()
                    };
                }
                d.name.edit_spelling(|name| *name = full);
            }
            Stmt::Inductive(d) => {
                let full = if d.name.is_resolved() {
                    d.name.to_string()
                } else {
                    join(path, &d.name)
                };
                for c in &mut d.constructors {
                    c.name
                        .edit_spelling(|name| *name = format!("{full}{SEPARATOR}{name}"));
                }
                d.name.edit_spelling(|name| *name = full);
            }
            _ => {}
        }
    }

    /// The full name of `name` written in the module `path`. A name that
    /// the module (or an inner one) and an outer module both declare is
    /// ambiguous (the outer one is written with its module path, `A::f`);
    /// `span`, when given, is where that is reported. A name declared outside
    /// every module (the prelude's, a builtin type, the top level of the file
    /// or of an imported file) that the module also declares is an error
    /// too: `u8` written in `module Font { fn u8 … }` neither silently means
    /// `Font::u8` nor silently means the builtin type. The module's one is
    /// written `Font::u8`; the outer one has no path, so the module's
    /// declaration is renamed to write it.
    fn name_at(&self, name: &str, path: &[String], span: Option<Span>) -> String {
        if self.locals.borrow().iter().any(|bound| bound == name) {
            return name.to_string();
        }
        let mut found: Vec<String> = Vec::new();
        for n in (1..=path.len()).rev() {
            let full = join(&path[..n], name);
            if self.fns.contains(&full) {
                found.push(full);
            } else if let Some(Some(ctor)) = self.ctors.get(&full) {
                found.push(ctor.clone());
            }
        }
        if !found.is_empty()
            && self.outer.contains(name)
            && let Some(span) = span
        {
            self.errors.borrow_mut().push((
                msg!("surface-name-shadows-outer", name = name, inner = &found[0]),
                span,
            ));
        } else if !found.is_empty()
            && self.unseen_outer.contains(name)
            && !self.outer.contains(name)
            && let Some(span) = span
        {
            self.warnings.borrow_mut().push((
                msg!(
                    "surface-name-outer-not-imported",
                    name = name,
                    inner = &found[0]
                ),
                span,
            ));
        } else if found.len() > 1
            && let Some(span) = span
        {
            self.errors.borrow_mut().push((
                msg!(
                    "surface-name-shadowed",
                    name = name,
                    names = found.join(", ")
                ),
                span,
            ));
        }
        found.into_iter().next().unwrap_or_else(|| name.to_string())
    }

    fn name(&self, name: &str, path: &[String]) -> String {
        self.name_at(name, path, None)
    }

    /// The full name of a name written with dots (`M::T::C`, `T::C` inside
    /// `M`): its first part a module or a type of a module.
    fn dotted_name(&self, parts: &[&str], path: &[String]) -> Option<String> {
        if self.locals.borrow().iter().any(|bound| bound == parts[0]) {
            return None;
        }
        let first = match self.module_of_path(parts[0], path) {
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
                    (name).edit_spelling(|spelling| self.ctor_name(spelling, path));
                }
                for a in args {
                    self.pattern(a, path);
                }
            }
            Pattern::Record { name, fields } => {
                (name).edit_spelling(|spelling| self.ctor_name(spelling, path));
                for (_, f) in fields {
                    self.pattern(f, path);
                }
            }
            // A constructor without fields, written bare (`C` of `M::T::C`).
            Pattern::Bind {
                name: crate::identity::Name::Spelled(n),
                ..
            } => {
                let full = self.name(n, path);
                if full != *n && self.ctors.values().any(|c| c.as_deref() == Some(&full)) {
                    *p = Pattern::Ctor {
                        name: crate::identity::Name::Spelled(full),
                        args: Vec::new(),
                    };
                }
            }
            _ => {}
        }
    }

    fn module(&self, m: &str, path: &[String]) -> Option<String> {
        for n in (0..=path.len()).rev() {
            let full = join(&path[..n], m);
            if self.modules.contains(&full) {
                return Some(full);
            }
        }
        None
    }

    /// The module a qualified name `m::…` starts with, written in the module
    /// `path`: the nearest module `m` of the modules `path` is in, or a top-level
    /// one. A module is not named by its own name from inside it (`b` inside
    /// `a::b` is not `a::b`), so a full name that starts with the name of an
    /// enclosing module (`app::src::app::T` inside `app::src::app`) is read
    /// from the top level, as written.
    fn module_of_path(&self, m: &str, path: &[String]) -> Option<String> {
        for n in (0..=path.len()).rev() {
            if n > 0 && path.get(n).is_some_and(|p| p == m) {
                continue;
            }
            let full = join(&path[..n], m);
            if self.modules.contains(&full) {
                return Some(full);
            }
        }
        None
    }

    fn dotted(t: &SurfaceTerm) -> Option<Vec<&str>> {
        match &*t.kind {
            TermKind::Var(crate::identity::Name::Spelled(n)) => Some(vec![n.as_str()]),
            TermKind::Field { base, name } => {
                let mut v = Self::dotted(base)?;
                v.push(name.as_str());
                Some(v)
            }
            _ => None,
        }
    }

    fn check_local(&self, name: &str, path: &[String], span: Span) {
        if !self.joined_files
            && self.module(name, path).is_some_and(|module| {
                self.explicit_modules.contains_key(&module)
                    || self.binding_modules.contains(&module)
            })
        {
            self.errors
                .borrow_mut()
                .push((msg!("surface-name-of-a-module", name = name), span));
        }
    }

    fn scoped(&self, f: impl FnOnce()) {
        let depth = self.locals.borrow().len();
        f();
        self.locals.borrow_mut().truncate(depth);
    }

    fn bind<N: AsRef<str>>(&self, names: &[N], path: &[String], span: Span) {
        for name in names {
            if self.program_ctors.contains(name.as_ref()) {
                continue;
            }
            self.check_local(name.as_ref(), path, span);
            self.locals.borrow_mut().push(name.as_ref().to_string());
        }
    }

    fn pattern_names(pattern: &Pattern, names: &mut Vec<String>) {
        match pattern {
            Pattern::Bind {
                name: crate::identity::Name::Spelled(name),
                ..
            } => names.push(name.clone()),
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
                self.locals.borrow_mut().push(name.to_string());
            }
            Stmt::Assign { value, .. } => self.term(value, path),
            Stmt::Fn(f) => self.fn_decl(f, path),
            Stmt::Effect(e) => {
                if let Some(row) = &mut e.set {
                    self.row(row, path, e.span);
                }
                for param in e.params.iter_mut().flatten() {
                    self.term(param, path);
                }
                if let Some(result) = &mut e.result {
                    self.term(result, path);
                }
            }
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
            Stmt::For { source, body, .. } => {
                self.term(source, path);
                self.term(body, path)
            }
            Stmt::Loop { body: e }
            | Stmt::Break(Some(e))
            | Stmt::Return(Some(e))
            | Stmt::Expr(e) => self.term(e, path),
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
        if let TermKind::Var(crate::identity::Name::Spelled(n)) = &*t.kind
            && n.contains(SEPARATOR)
        {
            let parts: Vec<&str> = n.split(SEPARATOR).collect();
            if let Some(full) = self.dotted_name(&parts, path) {
                t.kind = Arc::new(TermKind::Var(self.member_name(&full, path, t.span).into()));
            }
            return;
        }
        // `.` takes a field only: `M::f` over a module is written `M::f`.
        if !self.explicit_modules.is_empty()
            && let TermKind::Field { .. } = &*t.kind
            && let Some(parts) = Self::dotted(t)
            && let Some(full) = self.dotted_name(&parts, path)
        {
            self.errors.borrow_mut().push((
                msg!(
                    "surface-dot-names-a-declaration",
                    name = parts.join(SEPARATOR)
                ),
                t.span,
            ));
            t.kind = Arc::new(TermKind::Var(crate::identity::Name::Spelled(full)));
            return;
        }
        let span = t.span;
        match Arc::make_mut(&mut t.kind) {
            TermKind::Var(crate::identity::Name::Spelled(n)) => {
                let full = self.name_at(n, path, Some(span));
                *n = self.member_name(&full, path, span);
            }
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
                ..
            } => self.scoped(|| {
                for ty in types.iter_mut().flatten() {
                    self.term(ty, path);
                }
                self.bind(params, path, t.span);
                self.term(body, path);
            }),
            TermKind::Pi {
                params,
                result,
                effects,
                ..
            } => self.scoped(|| {
                if let Some(row) = effects {
                    self.row(row, path, span);
                }
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
                ..
            } => self.scoped(|| {
                self.term(domain, path);
                self.bind(std::slice::from_ref(binder), path, t.span);
                self.term(body, path);
            }),
            TermKind::Union(ts) => {
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
                if name.spelling() != Some(crate::IMPLICITS) {
                    (name).edit_spelling(|spelling| self.ctor_name(spelling, path));
                }
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
            TermKind::Perform { effect, args } => {
                effect.edit_spelling(|name| {
                    if let Some(scope) = self.effect_ref(name, path, span, EffectAccess::Perform) {
                        t.perform_scope = Some(scope);
                    }
                });
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
                            effect,
                            patterns,
                            cont,
                            body,
                            guard,
                            ..
                        } => self.scoped(|| {
                            effect.edit_spelling(|name| {
                                self.effect_ref(name, path, span, EffectAccess::Handle);
                            });
                            let mut names = Vec::new();
                            for pattern in patterns {
                                Self::pattern_names(pattern, &mut names);
                            }
                            names.extend(cont.iter().map(ToString::to_string));
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
                ..
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
                        names.extend(binder.iter().map(ToString::to_string));
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
mod bound_declaration_tests {
    use super::*;
    use crate::identity::{DeclRef, Name};
    use crate::surface::program::{DataConstructor, DataDecl, Vis};

    #[test]
    fn module_declaration_renaming_preserves_existing_identities() {
        let owner = DeclRef::fresh("T");
        let constructor = owner.constructor(0, "C");
        let mut statement = Stmt::Enum(DataDecl {
            kind: None,
            name: owner.clone().into(),
            vis: Vis::Private,
            generics: vec![],
            unused_generics: Vec::new(),
            unused_fields: Vec::new(),
            rows: vec![],
            host: false,
            borrowed: false,
            coerce: None,
            span: Span::new(0, 1),
            constructors: vec![DataConstructor {
                name: constructor.clone().into(),
                fields: vec![],
            }],
        });
        Resolver::default().rename(&mut statement, &["M".into()]);
        let Stmt::Enum(data) = statement else {
            unreachable!()
        };
        assert_eq!(data.name, Name::Global(owner));
        assert_eq!(data.constructors[0].name, Name::Global(constructor));
    }

    #[test]
    fn model_renaming_preserves_an_already_bound_reference() {
        let reference = Name::Global(DeclRef::fresh("Text::of_nat"));
        let mut statements = [Stmt::Expr(SurfaceTerm::var(&reference, Span::new(0, 1)))];
        super::super::qualify::rename_models(
            &mut statements,
            &[super::super::qualify::Model {
                file: 0,
                name: "Text::of_nat".into(),
                full: "std::Text::Text::of_nat".into(),
            }],
        );
        let Stmt::Expr(term) = &statements[0] else {
            unreachable!()
        };
        assert!(matches!(&*term.kind, TermKind::Var(name) if name == &reference));
    }
}
