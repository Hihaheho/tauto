//! Every declaration is told apart by its full name: the module of the file
//! that declares it and its own name (`app::List`, `std::List::List::filter`,
//! `std::prelude::List`); a constructor's full name has its type before its
//! own name (`std::Text::Text::Mk`). Where the program is read, each file's statements
//! are rewritten so that a name means one declaration only, whatever other
//! file or the prelude declares under the same name.
//!
//! A name written in a file means, in this order: the file's own
//! declaration, the declaration of another file of the program, and the
//! prelude's. A name two other files declare, and the file does not, is
//! ambiguous; its full name (`a.N`) says which one is meant. A name the
//! prelude declares and a file the file reaches through its imports (the
//! imports of an import included) declares too is that file's: the imports
//! say which declaration is meant, as for any other name, so a name the
//! prelude takes on later does not change what a file's names mean. A file
//! of the standard library is reached the same way: a prelude name it
//! declares is the model the proofs see of that builtin
//! (`std::Text::Text::len` of `text_len`). A name the prelude declares and a
//! file the file does not reach declares too (another file of the tote that
//! no importer of the file brings in, or a file of a tote the tote depends
//! on directly) is ambiguous: taking the prelude's would hide that declaration
//! without a word, and taking the other would depend on what the file does
//! not import. The types the
//! language itself has and the standard library declares (`Text`, `Never`)
//! are read as prelude names: another declaration of the name (a constructor
//! `Text`) is meant only where it is declared or imported.
//!
//! A name the file's imports declare, directly or through their own imports,
//! means only what they declare: a file that imports this one cannot change
//! what its names mean. What a file of a tote imports from another tote, the
//! standard library included (`std::Text`, say), is reached by the files of
//! that tote only: the files of other totes that import the tote import it
//! themselves to see it.
//!
//! A declaration keeps its short name when nothing else declares that
//! name, so that the passes after this one and what they print see the name
//! as written. Any other declaration is renamed to its full name, and so is
//! every use of it; the prelude keeps its names. A full name written in the
//! source is read as the declaration it names, the prelude's included.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, OnceLock};

use tauto_message::{Message, msg};
use tauto_parol::Span;

use super::program::{Handler, NOT_A_DECLARATION, Pattern, Stmt, Vis};
use super::{Name, SurfaceTerm, TermKind};

pub const PRELUDE_MODULE: &str = "std::prelude";

pub const SEPARATOR: &str = "::";

/// Effects are named apart from the rest (an effect `test` and a theorem
/// `test` are two names): an effect's name is kept with this mark before it.
const EFFECT: &str = "!";
/// Marks, in the names a file uses, the name of a macro or a syntax it calls.
pub const CALLED: &str = "\u{1}";

/// What the kernel makes for an inductive type `T`, named `T::rec`, …: it
/// is renamed with `T`.
const GENERATED: &[&str] = &[
    "::rec",
    "::ind",
    "::noconf",
    "::nc",
    "::nc_diag",
    "::beq",
    "::beq_sound",
    "::beq_refl",
    "::deq",
    "::eq",
];

/// Whether two modules are files of one tote: the first part of a module
/// is the tote's name (`app::src::types`).
fn same_tote(a: &str, b: &str) -> bool {
    let tote = |m: &str| m.split(SEPARATOR).next().unwrap_or("").to_string();
    a.contains(SEPARATOR) && b.contains(SEPARATOR) && tote(a) == tote(b)
}

/// What a full name of the prelude (`std::prelude::Text`) names (`Text`).
fn without_prelude_module(full: &str) -> Option<&str> {
    full.strip_prefix(PRELUDE_MODULE)?.strip_prefix(SEPARATOR)
}

/// The root of the standard library's modules (`std::List`). A tote cannot
/// take it as its name (the manifest rejects it), so a module under it is the
/// library's, and this is the one place that reads a module's root.
pub const STD_ROOT: &str = "std";

/// A module path split into its root and the rest (`std::List` into `std`
/// and `List`).
pub fn module_root(module: &str) -> (&str, Option<&str>) {
    match module.split_once(SEPARATOR) {
        Some((root, rest)) => (root, Some(rest)),
        None => (module, None),
    }
}

/// The path of the library's module `module` within the library (`List` of
/// `std::List`); none for a module of a tote and for the prelude's.
pub fn std_module_path(module: &str) -> Option<&str> {
    match module_root(module) {
        (STD_ROOT, Some(path)) if module_root(path).0 != "prelude" => Some(path),
        _ => None,
    }
}

/// Whether the full name `full` is declared by the library, the prelude
/// included.
fn is_library_name(full: &str) -> bool {
    matches!(module_root(full), (STD_ROOT, Some(_)))
}

fn is_std(module: &str) -> bool {
    std_module_path(module).is_some()
}

/// Whether `name` is a full name: it starts with the module of a file (or
/// the prelude's). A module's function (`List::append`) has a `::` too and
/// is not one.
fn is_full(name: &str, modules: &[String]) -> bool {
    let name = bare(name);
    let in_module = |m: &str| {
        name.strip_prefix(m)
            .is_some_and(|r| r.starts_with(SEPARATOR))
    };
    in_module(PRELUDE_MODULE) || modules.iter().any(|m| in_module(m))
}

fn bare(key: &str) -> &str {
    key.strip_prefix(EFFECT).unwrap_or(key)
}

/// A full name as a source file writes it, with `.` between its parts: how
/// a message shows a name, so what it suggests can be written as it is.
pub fn written(name: &str) -> String {
    name.to_string()
}

/// The source spelling of a bound reference, or of syntax being qualified.
/// References retain this spelling independently of later source reads.
pub trait SourceSpelling {
    fn source_spelling(&self) -> &str;
}

impl<T: SourceSpelling + ?Sized> SourceSpelling for &T {
    fn source_spelling(&self) -> &str {
        (*self).source_spelling()
    }
}

impl SourceSpelling for str {
    fn source_spelling(&self) -> &str {
        short_spelling(self)
    }
}
impl SourceSpelling for String {
    fn source_spelling(&self) -> &str {
        short_spelling(self)
    }
}
impl SourceSpelling for Name {
    fn source_spelling(&self) -> &str {
        match self {
            Name::Global(reference) => {
                let display = reference.source_display();
                without_prelude_module(display).unwrap_or(display)
            }
            Name::Spelled(spelling) => short_spelling(spelling),
            _ => self.as_str(),
        }
    }
}

/// The source spelling without the file module, retaining nested modules and owners.
pub fn short<N: SourceSpelling + ?Sized>(name: &N) -> &str {
    name.source_spelling()
}

/// `a::b::C` → `C`.
fn last_segment(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

fn short_spelling(name: &str) -> &str {
    if let Some(rest) = name
        .strip_prefix(PRELUDE_MODULE)
        .and_then(|r| r.strip_prefix(SEPARATOR))
    {
        return rest;
    }
    with_known_modules(|known| {
        let mut best: Option<&str> = None;
        let mut at = 0;
        while let Some(i) = name[at..].find(SEPARATOR) {
            let end = at + i;
            if known.contains(&name[..end]) {
                best = Some(&name[end + SEPARATOR.len()..]);
            }
            at = end + SEPARATOR.len();
        }
        best.unwrap_or(name)
    })
}

thread_local! {
    static SOURCE_MODULES: std::cell::RefCell<HashSet<String>> = Default::default();
}

fn with_known_modules<R>(f: impl FnOnce(&HashSet<String>) -> R) -> R {
    SOURCE_MODULES.with(|modules| f(&modules.borrow()))
}

fn register_modules(modules: &[String]) {
    SOURCE_MODULES.with(|known| *known.borrow_mut() = modules.iter().cloned().collect());
}

/// The types the language itself has and no file declares. They are named
/// as the prelude's are: a file's declaration of the same name (the
/// constructor `u64` of `std::UInt`) is renamed to its full name, so a file
/// that does not import it still means the type, whatever else the program
/// reads and in whatever order. `Text` and `Never` are not among them: the
/// standard library declares those types itself.
pub const BUILTIN_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "nat", "Bool", "Float", "Float32",
    "Decimal",
];

/// The types the language itself has and the standard library declares:
/// a text literal is a `Text`. The standard library's `inductive` of one is
/// the type itself and keeps its name; any other declaration of the name (a
/// constructor `Text` of a file's type) is renamed to its full name, as a
/// prelude name is, so that it neither hides the type nor makes it ambiguous.
const LANGUAGE_TYPES: &[&str] = &["Text", "Never"];

/// The kernel's sort a file may declare a type of: the file's declaration is
/// named apart. A declaration of `Type` is rejected as reserved, and so is an
/// `inductive Prop`, which keeps its name for the kernel to reject.
const SORTS: &[&str] = &["Prop"];

/// The sort an `inductive` of `s` is named as: the kernel rejects it as
/// reserved, so it keeps its name and cannot stand for the sort elsewhere.
fn inductive_sort(s: &Stmt) -> Option<&str> {
    match s {
        Stmt::Inductive(d) if SORTS.contains(&d.name.as_str()) => Some(&d.name),
        Stmt::Attributed { stmt, .. } => inductive_sort(stmt),
        _ => None,
    }
}

/// The language's type (`Never`, `Text`) that `s` declares, when `s` is in
/// the file of `std` with the module `module`: that declaration is the type,
/// as the prelude names it. A tote's copy of the file declares its own.
pub fn std_language_type<'a>(module: &str, s: &'a Stmt) -> Option<&'a str> {
    language_type(s).filter(|_| is_std(module) || module.starts_with(PRELUDE_MODULE))
}

/// The language's type `s` declares as the standard library does, the
/// `inductive` the proofs see of it, wherever its file is read from.
fn language_type(s: &Stmt) -> Option<&str> {
    match s {
        Stmt::Inductive(d) if LANGUAGE_TYPES.contains(&d.name.as_str()) => Some(&d.name),
        Stmt::Attributed { stmt, .. } => language_type(stmt),
        _ => None,
    }
}

/// Every name the prelude declares: the library prelude, the kernel's and
/// the builtin types.
pub fn prelude_names() -> &'static HashSet<String> {
    static NAMES: OnceLock<HashSet<String>> = OnceLock::new();
    NAMES.get_or_init(|| {
        let mut names: HashSet<String> = BUILTIN_TYPES.iter().map(|n| n.to_string()).collect();
        for text in [crate::nibstd::PRELUDE, crate::nibstd::KERNEL] {
            if let Ok(program) = super::program::prelude_as_written(text) {
                for s in &program.stmts {
                    declared(s, &mut |n| {
                        names.insert(n.to_string());
                    });
                }
            }
        }
        names
    })
}

fn prelude_file_module(file: &str) -> String {
    format!("{PRELUDE_MODULE}{SEPARATOR}{file}")
}

/// The names a prelude text declares, and the modules it opens (by their
/// full names): the top-level declarations (effects marked with `!`), the
/// functions of modules (`Text::join`), and the modules themselves.
fn prelude_text_names(text: &str, public_only: bool) -> (HashSet<String>, HashSet<String>) {
    fn modules_of(s: &Stmt, at: &mut Vec<String>, out: &mut HashSet<String>) {
        match s {
            Stmt::Module { name, items, .. } => {
                at.push(name.clone());
                out.insert(at.join(SEPARATOR));
                items.iter().for_each(|i| modules_of(i, at, out));
                at.pop();
            }
            Stmt::Attributed { stmt, .. } => modules_of(stmt, at, out),
            _ => {}
        }
    }
    let mut decls = HashSet::new();
    let mut mods = HashSet::new();
    if let Ok(program) = super::program::prelude_unresolved(text) {
        for s in &program.stmts {
            // A declaration without `pub` is the file's own: no file that
            // imports it sees the name, so it meets no name of theirs.
            if !(public_only && matches!(s.vis(), Some(super::program::Vis::Private))) {
                declared(s, &mut |n| {
                    decls.insert(n.to_string());
                });
            }
            modules_of(s, &mut Vec::new(), &mut mods);
        }
        decls.extend(super::modules::declared(&program.stmts));
    }
    (decls, mods)
}

/// The names only a non-core prelude file declares, each with the files
/// (`Os`, …) that do: what a file sees only by importing
/// `std::prelude::<file>`. A name the core declares (a type, a function, or a
/// module such as `Text` whose functions other files add to) is not among
/// them, but a function a non-core file adds to a core module (`Text::join`)
/// is.
pub fn hidden_prelude() -> &'static HashMap<String, Vec<String>> {
    static HIDDEN: OnceLock<HashMap<String, Vec<String>>> = OnceLock::new();
    HIDDEN.get_or_init(|| {
        let mut core_decls: HashSet<String> = BUILTIN_TYPES
            .iter()
            .chain(LANGUAGE_TYPES)
            .chain(SORTS)
            .map(|n| n.to_string())
            .collect();
        let mut core_mods: HashSet<String> = HashSet::new();
        let core_texts = std::iter::once(crate::nibstd::KERNEL)
            .chain(crate::nibstd::KERNEL_MODULES.iter().copied())
            .chain(
                crate::nibstd::PRELUDE_FILES
                    .iter()
                    .filter(|(path, _)| crate::nibstd::is_core_prelude_file(path))
                    .map(|(_, text)| *text),
            );
        for text in core_texts {
            let (d, m) = prelude_text_names(text, false);
            core_decls.extend(d);
            core_mods.extend(m);
        }
        let mut hidden: HashMap<String, Vec<String>> = HashMap::new();
        let mut mod_names: Vec<(String, String)> = Vec::new();
        for (path, text) in crate::nibstd::PRELUDE_FILES {
            let stem = prelude_stem(path);
            if crate::nibstd::is_core_prelude_file(path) {
                continue;
            }
            let (d, m) = prelude_text_names(text, true);
            for n in d {
                if !core_decls.contains(&n) {
                    let files = hidden.entry(n).or_default();
                    if !files.iter().any(|f| f == stem) {
                        files.push(stem.to_string());
                    }
                }
            }
            mod_names.extend(m.into_iter().map(|m| (m, stem.to_string())));
        }
        // A module no declaration has the name of (`Ct`, `Pending`).
        for (m, stem) in mod_names {
            if core_decls.contains(&m) || core_mods.contains(&m) {
                continue;
            }
            let files = hidden.entry(m).or_default();
            if !files.iter().any(|f| *f == stem) {
                files.push(stem);
            }
        }
        hidden
    })
}

/// The names the core files of the library's prelude (`Std`, `Text`, `Num`, the files not in
/// [`crate::nibstd::CORE_PRELUDE_FILES`]) declare and the kernel's prelude does not, each with the files that
/// do: what a file of a tote without the prelude (`package { prelude = false }`) sees only by
/// importing `std::prelude::<file>`. The language's types and sorts are not among them.
pub fn core_prelude() -> &'static HashMap<String, Vec<String>> {
    static CORE: OnceLock<HashMap<String, Vec<String>>> = OnceLock::new();
    CORE.get_or_init(|| {
        let mut kernel: HashSet<String> = BUILTIN_TYPES
            .iter()
            .chain(LANGUAGE_TYPES)
            .chain(SORTS)
            .map(|n| n.to_string())
            .collect();
        for text in std::iter::once(crate::nibstd::KERNEL)
            .chain(crate::nibstd::KERNEL_MODULES.iter().copied())
        {
            let (d, m) = prelude_text_names(text, false);
            kernel.extend(d);
            kernel.extend(m);
        }
        let mut core: HashMap<String, Vec<String>> = HashMap::new();
        for (path, text) in crate::nibstd::PRELUDE_FILES {
            let stem = prelude_stem(path);
            if !crate::nibstd::is_core_prelude_file(path) {
                continue;
            }
            let (d, m) = prelude_text_names(text, true);
            for n in d.into_iter().chain(m) {
                if kernel.contains(&n) {
                    continue;
                }
                let files = core.entry(n).or_default();
                if !files.iter().any(|f| f == stem) {
                    files.push(stem.to_string());
                }
            }
        }
        core
    })
}

/// The item an import list names a name of the prelude by: a constructor's type
/// (`Option` of `Some`), a module's name for its function (`List` of `List::map`), an effect
/// without its mark, any other name itself.
fn prelude_item(n: &str) -> String {
    let b = bare(n);
    if n.starts_with(EFFECT) {
        return b.to_string();
    }
    if let Some((ty, _)) = prelude_ctors()
        .iter()
        .find(|(ty, cs)| *ty != b && cs.contains_key(b))
    {
        return ty.clone();
    }
    b.split(SEPARATOR).next().unwrap_or(b).to_string()
}

fn prelude_stem(path: &str) -> &str {
    let file = path.rsplit('/').next().unwrap_or(path);
    file.strip_suffix(".taut").unwrap_or(file)
}

/// The functions of the prelude's modules, by their full names
/// (`U64::of_nat`, `Nat::lt`): the library prelude's and the kernel's.
fn prelude_fns() -> &'static Vec<String> {
    static FNS: OnceLock<Vec<String>> = OnceLock::new();
    FNS.get_or_init(|| {
        let mut fns: Vec<String> = prelude_names()
            .iter()
            .filter(|n| n.contains(SEPARATOR))
            .cloned()
            .collect();
        for text in crate::nibstd::KERNEL_MODULES {
            if let Ok(program) = super::program::prelude_unresolved(text) {
                fns.extend(super::modules::declared(&program.stmts));
            }
        }
        fns
    })
}

fn prelude_ctors() -> &'static HashMap<String, HashMap<String, String>> {
    static CTORS: OnceLock<HashMap<String, HashMap<String, String>>> = OnceLock::new();
    CTORS.get_or_init(|| {
        let mut out = HashMap::new();
        for text in [crate::nibstd::PRELUDE, crate::nibstd::KERNEL] {
            if let Ok(program) = super::program::prelude_as_written(text) {
                for s in &program.stmts {
                    ctors_of(s, &mut |ty, c| {
                        out.entry(ty.to_string())
                            .or_insert_with(HashMap::new)
                            .insert(c.to_string(), c.to_string());
                    });
                }
            }
        }
        out
    })
}

/// The type of each field of the prelude's constructors, by their names.
fn prelude_fields() -> &'static HashMap<String, Vec<Option<Shape>>> {
    static FIELDS: OnceLock<HashMap<String, Vec<Option<Shape>>>> = OnceLock::new();
    FIELDS.get_or_init(|| {
        let mut out = HashMap::new();
        // A name constructors of several types have (`Mk`) says no type here.
        let mut shared = HashSet::new();
        for text in [crate::nibstd::PRELUDE, crate::nibstd::KERNEL] {
            if let Ok(program) = super::program::prelude_as_written(text) {
                for s in &program.stmts {
                    field_types(
                        s,
                        &mut |_, c, tys| {
                            if out.insert(c.to_string(), tys).is_some() {
                                shared.insert(c.to_string());
                            }
                        },
                        &|n| n.to_string(),
                    );
                }
            }
        }
        out.retain(|c, _| !shared.contains(c));
        out
    })
}

fn ctors_of(s: &Stmt, out: &mut dyn FnMut(&str, &str)) {
    match s {
        Stmt::Struct(d) | Stmt::Enum(d) => {
            d.constructors.iter().for_each(|c| out(&d.name, &c.name))
        }
        Stmt::Inductive(d) => d.constructors.iter().for_each(|c| out(&d.name, &c.name)),
        Stmt::Mutual { items, .. } => items.iter().for_each(|i| ctors_of(i, out)),
        Stmt::Attributed { stmt, .. } => ctors_of(stmt, out),
        _ => {}
    }
}

/// The head of a written type (`T` of `T(A)`), when it is a name.
fn type_head(t: &SurfaceTerm) -> Option<String> {
    match &*t.kind {
        TermKind::Var(h) => Some(h.to_string()),
        TermKind::App { function, .. } => match &*function.kind {
            TermKind::Var(h) => Some(h.to_string()),
            _ => None,
        },
        _ => None,
    }
}

/// A type as far as this pass reads it: a parameter of a family (by its
/// place) or a named type over its arguments, each known or not.
#[derive(Debug, Clone)]
enum Shape {
    Param(usize),
    Named(String, Vec<Option<Shape>>),
}

impl Shape {
    fn head(&self) -> Option<&str> {
        match self {
            Shape::Named(h, _) => Some(h),
            Shape::Param(_) => None,
        }
    }

    /// The type with the family's arguments `args` put for its parameters.
    fn instantiate(&self, args: &[Option<Shape>]) -> Option<Shape> {
        match self {
            Shape::Param(k) => args.get(*k).cloned().flatten(),
            Shape::Named(h, xs) => Some(Shape::Named(
                h.clone(),
                xs.iter()
                    .map(|x| x.as_ref().and_then(|x| x.instantiate(args)))
                    .collect(),
            )),
        }
    }

    /// A field's type as written in its family's declaration: a parameter of
    /// the family is its place in `params`; a name another field binds (a
    /// dependent field) names no type here. `named` gives a type's name as
    /// after this pass.
    fn of_field(
        t: &SurfaceTerm,
        params: &[super::Name],
        bound: &[super::Name],
        named: &dyn Fn(&str) -> String,
    ) -> Option<Shape> {
        let (head, args) = match &*t.kind {
            TermKind::App {
                function,
                arguments,
            } => (&**function, arguments.as_slice()),
            _ => (t, &[][..]),
        };
        let TermKind::Var(h) = &*head.kind else {
            return None;
        };
        if bound.contains(h) {
            return None;
        }
        if let Some(k) = params.iter().position(|p| p == h) {
            return args.is_empty().then_some(Shape::Param(k));
        }
        Some(Shape::Named(
            named(h),
            args.iter()
                .map(|a| Shape::of_field(a, params, bound, named))
                .collect(),
        ))
    }
}

/// The type of each explicit field of the constructors `s` declares, by the
/// constructor's name as written and its family's: `out(family, ctor, fields)`.
fn field_types(
    s: &Stmt,
    out: &mut dyn FnMut(&str, &str, Vec<Option<Shape>>),
    named: &dyn Fn(&str) -> String,
) {
    match s {
        Stmt::Inductive(d) => {
            let params: Vec<super::Name> = d.params.iter().map(|(n, _)| n.clone()).collect();
            for c in &d.constructors {
                let mut bound: Vec<super::Name> = Vec::new();
                let mut fields = Vec::new();
                for (k, (n, t)) in c.params.iter().enumerate() {
                    if k >= c.implicit {
                        fields.push(Shape::of_field(t, &params, &bound, named));
                    }
                    bound.push(n.clone());
                }
                out(&d.name, &c.name, fields);
            }
        }
        Stmt::Struct(d) | Stmt::Enum(d) => {
            for c in &d.constructors {
                let fields = c
                    .fields
                    .iter()
                    .map(|(_, t)| Shape::of_field(t, &d.generics, &[], named))
                    .collect();
                out(&d.name, &c.name, fields);
            }
        }
        Stmt::Mutual { items, .. } => items.iter().for_each(|i| field_types(i, out, named)),
        Stmt::Attributed { stmt, .. } => field_types(stmt, out, named),
        _ => {}
    }
}

/// Each function, theorem and constructor a top-level statement declares,
/// with its name, whether it is a constructor, its type (a constructor's) and
/// its explicit parameters, each with the name it binds and the type it is
/// written with (none where that type is a generic of the declaration).
fn arg_types(s: &Stmt, out: &mut dyn FnMut(&str, bool, &str, Vec<(String, Option<SurfaceTerm>)>)) {
    let generics = |gs: &[super::Name]| -> Vec<(String, Option<SurfaceTerm>)> {
        gs.iter().map(|g| (g.to_string(), None)).collect()
    };
    match s {
        Stmt::Fn(f) => {
            let params = f
                .params
                .iter()
                .map(ToString::to_string)
                .zip(f.param_types.iter().cloned())
                .collect();
            out(
                &f.name,
                false,
                "",
                without_generics(generics(&f.generics), params),
            );
        }
        Stmt::Theorem(d) | Stmt::Def(d) => {
            let params: Vec<(String, Option<SurfaceTerm>)> = d
                .params
                .iter()
                .map(|(n, t)| (n.to_string(), Some(t.clone())))
                .collect();
            let (implicit, explicit) = params.split_at(d.implicit.min(params.len()));
            out(
                &d.name,
                false,
                "",
                without_generics(implicit.to_vec(), explicit.to_vec()),
            );
        }
        Stmt::Inductive(d) => {
            let family: Vec<(String, Option<SurfaceTerm>)> = d
                .params
                .iter()
                .map(|(n, _)| (n.to_string(), None))
                .collect();
            for c in &d.constructors {
                let params: Vec<(String, Option<SurfaceTerm>)> = c
                    .params
                    .iter()
                    .map(|(n, t)| (n.to_string(), Some(t.clone())))
                    .collect();
                let (implicit, explicit) = params.split_at(c.implicit.min(params.len()));
                let mut bound = family.clone();
                bound.extend(implicit.iter().cloned());
                out(
                    &c.name,
                    true,
                    &d.name,
                    without_generics(bound, explicit.to_vec()),
                );
            }
        }
        Stmt::Struct(d) | Stmt::Enum(d) => {
            for c in &d.constructors {
                let fields: Vec<(String, Option<SurfaceTerm>)> = c
                    .fields
                    .iter()
                    .map(|(n, t)| (n.clone().unwrap_or_default(), Some(t.clone())))
                    .collect();
                out(
                    &c.name,
                    true,
                    &d.name,
                    without_generics(generics(&d.generics), fields),
                );
            }
        }
        Stmt::Mutual { items, .. } => items.iter().for_each(|i| arg_types(i, out)),
        Stmt::Attributed { stmt, .. } => arg_types(stmt, out),
        _ => {}
    }
}

/// The explicit parameters `explicit`, without the type of one whose type is
/// a name `bound` binds (a generic `A`), which names no type.
fn without_generics(
    bound: Vec<(String, Option<SurfaceTerm>)>,
    explicit: Vec<(String, Option<SurfaceTerm>)>,
) -> Vec<(String, Option<SurfaceTerm>)> {
    let names: Vec<String> = bound.into_iter().map(|(n, _)| n).collect();
    explicit
        .into_iter()
        .map(|(n, t)| {
            let t = t.filter(|t| type_head(t).is_none_or(|h| !names.contains(&h)));
            (n, t)
        })
        .collect()
}

/// Each `inductive` (and `inductive enum`) a top-level statement declares,
/// with each of its constructors.
fn inductive_ctors(s: &Stmt, out: &mut dyn FnMut(&str, &str)) {
    match s {
        Stmt::Inductive(d) => d.constructors.iter().for_each(|c| out(&d.name, &c.name)),
        Stmt::Enum(d) if crate::inductive_data::is_inductive(d) => {
            d.constructors.iter().for_each(|c| out(&d.name, &c.name))
        }
        Stmt::Mutual { items, .. } => items.iter().for_each(|i| inductive_ctors(i, out)),
        Stmt::Attributed { stmt, .. } => inductive_ctors(stmt, out),
        _ => {}
    }
}

/// The constructor names two or more `inductive` types of one file share,
/// each with those types: as the constructors of Nib's enums, they are told
/// apart by their type (`A::start`, `B::start`).
fn shared_ctors(stmts: &[Stmt]) -> HashMap<String, Vec<String>> {
    let mut types: HashMap<String, Vec<String>> = HashMap::new();
    for s in stmts {
        inductive_ctors(s, &mut |ty, c| {
            if c.contains(SEPARATOR) {
                return;
            }
            let v = types.entry(c.to_string()).or_default();
            if !v.iter().any(|t| t == ty) {
                v.push(ty.to_string());
            }
        });
    }
    types.retain(|_, v| v.len() > 1);
    types
}

/// The names a top-level statement declares: its functions, types,
/// constructors, effects (marked with `!`), classes and theorems.
pub fn declared(s: &Stmt, out: &mut dyn FnMut(&str)) {
    match s {
        Stmt::Fn(f) => out(&f.name),
        Stmt::Extern { fns, .. } => fns.iter().for_each(|f| out(&f.name)),
        Stmt::Struct(d) | Stmt::Enum(d) => {
            out(&d.name);
            for c in &d.constructors {
                if c.name != d.name {
                    out(&c.name);
                }
            }
        }
        Stmt::Effect(e) => out(&format!("{EFFECT}{}", e.name)),
        Stmt::Inductive(d) => {
            out(&d.name);
            d.constructors.iter().for_each(|c| out(&c.name));
            for suffix in GENERATED {
                out(&format!("{}{suffix}", d.name));
            }
        }
        Stmt::Theorem(d) | Stmt::Def(d) => out(&d.name),
        Stmt::Class(c) => out(&c.name),
        Stmt::Mutual { items, .. } => items.iter().for_each(|i| declared(i, out)),
        Stmt::Attributed { stmt, .. } => declared(stmt, out),
        _ => {}
    }
}

/// What a top-level statement declares, and the name a top-level `let` or
/// `var` binds. The program reads those names in one scope across its files,
/// so where another file declares the name too, each is renamed to its full
/// name like any declaration, and neither file reads the other's.
fn declared_or_bound(s: &Stmt, out: &mut dyn FnMut(&str)) {
    match s {
        Stmt::Let { name, .. } | Stmt::Var { name, .. } => out(name),
        _ => declared(s, out),
    }
}

/// How the file `here` writes the import of the file `target`, by their indices,
/// from the paths the program is read from and the dependencies of their totes.
pub type Spell<'a> = &'a dyn Fn(usize, usize) -> String;

/// How the file `here` imports the file `target`: by `spell` when the program
/// is read from files, else by their modules ([`import_spelling`]).
fn spelling(spell: Option<Spell>, modules: &[String], here: usize, target: usize) -> String {
    match spell {
        Some(spell) => spell(here, target),
        None => import_spelling(&modules[here], &modules[target]),
    }
}

/// How the file `here` imports the file `target`, both by module: a file of the
/// standard library as `std::List`; a file of the same tote by its path from
/// `here`'s directory, quoted (`"Setoid.taut"`, `"../src/Setoid.taut"`); a file
/// of another tote, the dependency's name and the module path the dependency
/// gives it: the path from `src` for a file of `src` (`compiler::compiler`)
/// and the whole path for a file of an additional source
/// (`compiler::proof::compiler`).
fn import_spelling(here: &str, target: &str) -> String {
    let parts = |m: &str| m.split(SEPARATOR).map(str::to_string).collect::<Vec<_>>();
    let (h, t) = (parts(here), parts(target));
    if is_std(target) || target.starts_with(PRELUDE_MODULE) {
        return target.to_string();
    }
    if h.len() < 2 || t.len() < 2 || h[0] == t[0] {
        let dir = &h[..h.len().saturating_sub(1)];
        let common = dir.iter().zip(&t).take_while(|(a, b)| a == b).count();
        let common = common.min(t.len() - 1);
        let ups = dir.len() - common;
        let path = std::iter::repeat_n("..".to_string(), ups)
            .chain(t[common..].iter().cloned())
            .collect::<Vec<_>>()
            .join("/");
        return format!("\"{path}.taut\"");
    }
    let rest = if t[1] == "src" && t.len() > 2 {
        &t[2..]
    } else {
        &t[1..]
    };
    format!("{}{SEPARATOR}{}", t[0], rest.join(SEPARATOR))
}

/// The module of a file, by the parts of its path relative to the root the
/// program is read from: each part without the file's extension, joined by
/// `::`, which cannot be in a name written `_`.
pub fn module_of(parts: &[&str]) -> String {
    let last = parts.len().saturating_sub(1);
    parts
        .iter()
        .enumerate()
        .filter(|(_, p)| !p.is_empty() && **p != ".")
        .map(|(i, p)| {
            let p = match p.rsplit_once('.') {
                Some((stem, _)) if i == last && !stem.is_empty() => stem,
                _ => p,
            };
            p.chars()
                .map(|c| {
                    if c.is_alphanumeric() || c == '_' {
                        c
                    } else {
                        '_'
                    }
                })
                .collect::<String>()
        })
        .collect::<Vec<_>>()
        .join(SEPARATOR)
}

/// Rewrites the files of a program, `files[i]` the statements of the file
/// whose module is `modules[i]`, so that each name means one declaration.
/// `imports[i]`, when the files import each other, are the files the file
/// `i` imports; a name another file declares is looked for there first.
/// Returns what is ambiguous, where it is written.
///
/// It may run again on its own output, after the macros have made more
/// declarations: a full name it wrote stays as it is.
pub fn files(
    files: &mut [Vec<Stmt>],
    modules: &[String],
    imports: Option<&[Vec<usize>]>,
) -> Vec<(Message, Span)> {
    files_with_totes(files, modules, imports, None)
}

/// [`files`], with `below[i]` the files of the totes the tote of the file
/// `i` depends on, directly or through other totes. A prelude name one of
/// them declares, and the file does not import, is not taken as the
/// prelude's without a word, as a file of its own tote is not.
pub fn files_with_totes(
    files: &mut [Vec<Stmt>],
    modules: &[String],
    imports: Option<&[Vec<usize>]>,
    below: Option<&[HashSet<usize>]>,
) -> Vec<(Message, Span)> {
    files_seeing(files, modules, imports, below).0
}

/// [`files_with_totes`], with what each file's short names mean where this
/// pass renamed what they name (`arg` to `narrative::src::story::arg`): a
/// name a macro of the file writes means that too, wherever it is expanded.
pub fn files_seeing(
    files: &mut [Vec<Stmt>],
    modules: &[String],
    imports: Option<&[Vec<usize>]>,
    below: Option<&[HashSet<usize>]>,
) -> (Vec<(Message, Span)>, Vec<HashMap<String, String>>) {
    let (errors, seeing, _) = qualify(
        files,
        modules,
        imports,
        below,
        false,
        None,
        None,
        &mut Vec::new(),
        &mut Vec::new(),
    );
    (errors, seeing)
}

/// [`files_seeing`] before the macros are expanded, for the pass that runs
/// again on their output: a full name of the prelude (`std::prelude::Text`)
/// is kept as written. Written short, it would be read again as whatever the
/// macros declare by that name (a grammar's terminal `Text`), and the full
/// name is how a file says it means the prelude's whatever it declares.
/// Also gives the names one import would make seen ([`MissingImport`]).
pub fn files_before_macros(
    files: &mut [Vec<Stmt>],
    modules: &[String],
    imports: Option<&[Vec<usize>]>,
    below: Option<&[HashSet<usize>]>,
    spell: Option<Spell>,
) -> (
    Vec<(Message, Span)>,
    Vec<HashMap<String, String>>,
    Vec<MissingImport>,
) {
    qualify(
        files,
        modules,
        imports,
        below,
        true,
        spell,
        None,
        &mut Vec::new(),
        &mut Vec::new(),
    )
}

/// [`files_before_macros`], with `lists[i]` the imports of the file `i`: an import with a list
/// brings only what it lists. The lists are checked after the macros
/// ([`files_after_macros_listed`]).
pub fn files_before_macros_listed(
    files: &mut [Vec<Stmt>],
    modules: &[String],
    imports: Option<&[Vec<usize>]>,
    below: Option<&[HashSet<usize>]>,
    spell: Option<Spell>,
    lists: &[Vec<ImportList>],
    bare: &[bool],
    quoted: &Quoted,
) -> (
    Vec<(Message, Span)>,
    Vec<HashMap<String, String>>,
    Vec<MissingImport>,
) {
    qualify(
        files,
        modules,
        imports,
        below,
        true,
        spell,
        Some((lists, bare, quoted)),
        &mut Vec::new(),
        &mut Vec::new(),
    )
}

/// [`files_with_totes`] on macro output. Resolved references retain their
/// declaration identities; source spellings obey the imports of this file.
/// Also gives the names one import would make seen ([`MissingImport`]).
pub fn files_after_macros(
    files: &mut [Vec<Stmt>],
    modules: &[String],
    imports: Option<&[Vec<usize>]>,
    below: Option<&[HashSet<usize>]>,
    spell: Option<Spell>,
) -> (Vec<(Message, Span)>, Vec<MissingImport>) {
    let (errors, _, missing) = qualify(
        files,
        modules,
        imports,
        below,
        false,
        spell,
        None,
        &mut Vec::new(),
        &mut Vec::new(),
    );
    (errors, missing)
}

/// Source references captured before macro expansion. Import lists are checked
/// against these uses without resolving the expanded references again.
pub type Quoted = std::cell::RefCell<Vec<Vec<SourceUse>>>;

#[derive(Clone, Debug)]
pub struct SourceUse {
    path: String,
    written: String,
    span: Span,
    /// A name read after expansion: it keeps a listed name used, but asks for no
    /// name to be listed (the source's own uses do).
    keeps_only: bool,
}

/// Adds to `quoted` the macro calls a macro's output makes (`CALLED` and the macro's name):
/// the file, the name, and where. They are expanded away before the pass after expansion
/// reads the file, so it does not see them.
pub fn quote_written(quoted: &Quoted, written: impl IntoIterator<Item = (usize, String, Span)>) {
    let mut quoted = quoted.borrow_mut();
    for (file, name, span) in written {
        if quoted.len() <= file {
            quoted.resize(file + 1, Vec::new());
        }
        let uses = &mut quoted[file];
        if !uses.iter().any(|u| u.span == span) {
            uses.push(SourceUse {
                path: name.clone(),
                written: name,
                span,
                keeps_only: true,
            });
        }
    }
}
impl SourceUse {
    pub fn new(path: String, written: String, span: Span) -> Self {
        Self {
            path,
            written,
            span,
            keeps_only: false,
        }
    }
}

/// The title of the edit that writes an import's list of the names the file uses through it;
/// `tauto lint --fix` applies the edits with it.
pub const IMPORT_FIX_TITLE: &str = "Write the list of what the import brings";

/// The title of the edit that takes away an import through which the file uses nothing;
/// `tauto lint --fix` applies it when the file checks as well without the import.
pub const UNUSED_IMPORT_FIX_TITLE: &str = "Remove the import";

/// An `import` of a file, as [`files_after_macros_listed`] holds the file to it.
#[derive(Debug, Clone)]
pub struct ImportList {
    /// The imported file, by its index among the files; `None` when it is not one of them.
    pub target: Option<usize>,
    /// The import as written after `import`: `std::Text`, `"value.taut"`.
    pub spelling: String,
    /// The names written in its list, if it has one.
    pub names: Option<Vec<(String, Span)>>,
    /// The whole `import` statement.
    pub span: Span,
}

/// [`files_after_macros`], with `lists[i]` the imports of the file `i`. An import with a list
/// brings only the names it lists, a type with its constructors: a name the file uses through it
/// and does not list, a listed name the file does not use and a listed name the imported file does
/// not declare for other files are errors. Returns the errors and, for every import through which
/// the file uses a name, the edit that writes its list ([`IMPORT_FIX_TITLE`]), by the span of the
/// import.
pub fn files_after_macros_listed(
    files: &mut [Vec<Stmt>],
    modules: &[String],
    imports: Option<&[Vec<usize>]>,
    below: Option<&[HashSet<usize>]>,
    spell: Option<Spell>,
    lists: &[Vec<ImportList>],
    bare: &[bool],
    quoted: &Quoted,
) -> (
    Vec<(Message, Span)>,
    Vec<HashMap<String, String>>,
    Vec<MissingImport>,
    Vec<(Span, super::Fix)>,
    Vec<(Message, Span)>,
) {
    let mut fixes = Vec::new();
    let mut warnings = Vec::new();
    let (errors, seeing, missing) = qualify(
        files,
        modules,
        imports,
        below,
        false,
        spell,
        Some((lists, bare, quoted)),
        &mut fixes,
        &mut warnings,
    );
    (errors, seeing, missing, fixes, warnings)
}

/// Whether `module` is a file of the prelude (`std::prelude::Os`) that declares `item`: the
/// prelude's names are read as the prelude's, not as that file's, so a list keeps them as written.
fn prelude_declares(module: &str, item: &str) -> bool {
    let Some(file) = module
        .strip_prefix(PRELUDE_MODULE)
        .and_then(|r| r.strip_prefix(SEPARATOR))
    else {
        return false;
    };
    let declares = |n: &str| {
        hidden_prelude()
            .get(n)
            .is_some_and(|fs| fs.iter().any(|f| f == file))
    };
    declares(item)
        || declares(&format!("{EFFECT}{item}"))
        || prelude_names().contains(item)
        || prelude_names().contains(&format!("{EFFECT}{item}"))
}

/// The import lists of the file `i`, held to the names it used through each import (`used`, as the
/// renaming read them). A use is held to the item a list names it by: a constructor's or a
/// generated name's type (`Value` of `Vtext`, of `Value::rec`), a module's name for its function
/// (`List` of `List::map`), an effect without its mark, any other name itself.
#[allow(clippy::too_many_arguments)]
fn check_import_lists(
    bare_file: bool,
    i: usize,
    files: &[Vec<Stmt>],
    modules: &[String],
    owners: &HashMap<String, Vec<usize>>,
    reach: &[HashSet<usize>],
    private: &[HashSet<String>],
    ctor_type: &[HashMap<String, String>],
    language: &HashSet<String>,
    lists: &[ImportList],
    used: &[SourceUse],
    errors: &mut Vec<(Message, Span)>,
    warnings: &mut Vec<(Message, Span)>,
    fixes: &mut Vec<(Span, super::Fix)>,
) {
    let public_source_item = |file: usize, item: &str| {
        let full = format!("{}{SEPARATOR}{item}", modules[file]);
        files[file].iter().any(|statement| {
            if matches!(statement.vis(), Some(super::program::Vis::Private)) {
                return false;
            }
            let mut found = false;
            declared(statement, &mut |name| {
                found |= !private[file].contains(name)
                    && (bare(name) == full
                        || bare(name)
                            .strip_prefix(&full)
                            .is_some_and(|tail| tail.starts_with(SEPARATOR)));
            });
            found
        })
    };
    let keeps_only: HashSet<Span> = used
        .iter()
        .filter(|u| u.keeps_only)
        .map(|u| u.span)
        .collect();
    // The item, the name as read and where it is used, by the imported file.
    let mut by_file: HashMap<usize, Vec<(String, String, Span)>> = HashMap::new();
    for usage in used {
        let n = &usage.path;
        let span = &usage.span;
        // A macro or a syntax the file calls: the file it reaches that declares it.
        if let Some(called) = n.strip_prefix(CALLED) {
            let declares = |j: usize| {
                files[j].iter().any(|s| match s {
                    Stmt::Macro { name, .. } | Stmt::Syntax { name, .. } => name == called,
                    _ => false,
                }) || owners
                    .get(called)
                    .is_some_and(|o| o.contains(&j) && !private[j].contains(called))
                    || public_source_item(j, called)
            };
            // The file's own macro is its own.
            let own = files[i].iter().any(|s| {
                matches!(s, Stmt::Macro { name, .. } | Stmt::Syntax { name, .. } if name == called)
            }) || owners.get(called).is_some_and(|o| o.contains(&i));
            if !own && let Some(j) = reach[i].iter().copied().find(|&j| declares(j)) {
                by_file
                    .entry(j)
                    .or_default()
                    .push((called.to_string(), called.to_string(), *span));
            }
            continue;
        }
        let effect = n.starts_with(EFFECT);
        let b = bare(n);
        // Source uses captured before expansion can name a constructor that a
        // syntax declaration subsequently creates. Its owning type determines
        // the import item even after the constructor carries a qualified ID.
        if !effect && !b.contains(SEPARATOR) && !owners.contains_key(n.as_str()) {
            let mut candidates = reach[i]
                .iter()
                .filter_map(|&j| ctor_type[j].get(b).map(|owner| (j, owner)));
            if let (Some((j, owner)), None) = (candidates.next(), candidates.next()) {
                by_file
                    .entry(j)
                    .or_default()
                    .push((owner.clone(), usage.written.clone(), *span));
                continue;
            }
        }
        // A full name: the file whose module it starts with, the longest one.
        let by_module = reach[i]
            .iter()
            .copied()
            .filter_map(|j| {
                let rest = b
                    .strip_prefix(modules[j].as_str())
                    .and_then(|r| r.strip_prefix(SEPARATOR))?;
                Some((modules[j].len(), j, rest.to_string()))
            })
            .max_by_key(|(len, _, _)| *len);
        let (j, rel) = match by_module {
            Some((_, j, rest)) => (j, rest),
            None => {
                let Some(o) = owners.get(n.as_str()) else {
                    // A name of the prelude the file sees only through the import of its
                    // file (`std::prelude::Os`) is held to that import.
                    let files_of = hidden_prelude()
                        .get(n.as_str())
                        .or_else(|| bare_file.then(core_prelude).and_then(|c| c.get(n.as_str())));
                    let from = files_of
                        .and_then(|fs| {
                            reach[i]
                                .iter()
                                .copied()
                                .find(|&j| fs.iter().any(|f| modules[j] == prelude_file_module(f)))
                        })
                        // A type of the language a file it reaches declares (`Text` of
                        // `std::Text`).
                        .or_else(|| {
                            reach[i].iter().copied().find(|&j| {
                                language.contains(&format!("{}{SEPARATOR}{b}", modules[j]))
                            })
                        });
                    if let Some(j) = from {
                        by_file.entry(j).or_default().push((
                            prelude_item(n),
                            usage.written.clone(),
                            *span,
                        ));
                    }
                    continue;
                };
                // The file's own declaration is its own.
                if o.contains(&i) {
                    continue;
                }
                let mut from = o
                    .iter()
                    .copied()
                    .filter(|&j| reach[i].contains(&j) && !private[j].contains(n.as_str()));
                match (from.next(), from.next()) {
                    (Some(j), None) => (j, b.to_string()),
                    _ => continue,
                }
            }
        };
        let item = if effect {
            rel.clone()
        } else if let Some(ty) = ctor_type[j].get(&rel) {
            ty.clone()
        } else {
            rel.split(SEPARATOR).next().unwrap_or(&rel).to_string()
        };
        by_file
            .entry(j)
            .or_default()
            .push((item, usage.written.clone(), *span));
    }
    // What the imported file declares for other files, by the item a list names it with, and
    // its macros and syntaxes, which this pass does not see used.
    let exported = |j: usize, item: &str| {
        let public =
            |k: &str| owners.get(k).is_some_and(|o| o.contains(&j)) && !private[j].contains(k);
        public(item)
            || public_source_item(j, item)
            || public(&format!("{EFFECT}{item}"))
            || owners.iter().any(|(k, o)| {
                o.contains(&j)
                    && k.strip_prefix(item)
                        .is_some_and(|r| r.starts_with(SEPARATOR))
            })
    };
    // A macro or a syntax, whose calls the macros read, and a type of the language the file
    // declares (`Text` of `std::Text`), which a file sees whatever it imports: kept as listed.
    let macro_named = |j: usize, item: &str| {
        language.contains(&format!("{}{SEPARATOR}{item}", modules[j]))
            || prelude_declares(&modules[j], item)
            || files[j].iter().any(|s| match s {
                Stmt::Macro { name, .. } => name == item,
                Stmt::Syntax { name, .. } => name == item,
                _ => false,
            })
    };
    for import in lists {
        let Some(j) = import.target else {
            continue;
        };
        let used_here = by_file.get(&j).map(Vec::as_slice).unwrap_or(&[]);
        let mut wanted: Vec<String> = used_here.iter().map(|(item, _, _)| item.clone()).collect();
        let mut found: Vec<(Message, Span)> = Vec::new();
        let mut unused: Vec<(Message, Span)> = Vec::new();
        if let Some(names) = &import.names {
            for (item, name, span) in used_here {
                if !keeps_only.contains(span) && !names.iter().any(|(l, _)| l == item) {
                    found.push((
                        msg!(
                            "surface-import-not-listed",
                            name = name.as_str(),
                            item = item.as_str(),
                            spelling = import.spelling.as_str()
                        ),
                        *span,
                    ));
                }
            }
            for (l, span) in names {
                if macro_named(j, l) {
                    // A macro or a syntax is kept as listed: its calls are read by the macros.
                    wanted.push(l.clone());
                } else if !exported(j, l) {
                    found.push((
                        msg!(
                            "surface-import-listed-unknown",
                            name = l.as_str(),
                            spelling = import.spelling.as_str()
                        ),
                        *span,
                    ));
                } else if !used_here.iter().any(|(item, _, _)| item == l) {
                    // A name listed but not used changes nothing the file means: a warning.
                    // The standard library keeps its lists exact, so there it is an error.
                    unused.push((
                        msg!(
                            "surface-import-listed-unused",
                            name = l.as_str(),
                            spelling = import.spelling.as_str()
                        ),
                        *span,
                    ));
                }
            }
        }
        wanted.sort();
        wanted.dedup();
        // An import through which the file uses nothing is taken away; `tauto lint --fix`
        // checks the file again without it and keeps it if it is needed after all.
        if wanted.is_empty() {
            fixes.push((
                import.span,
                super::Fix {
                    title: UNUSED_IMPORT_FIX_TITLE.into(),
                    span: import.span,
                    text: String::new(),
                },
            ));
        } else {
            let fix = super::Fix {
                title: IMPORT_FIX_TITLE.into(),
                span: import.span,
                text: format!("import {} {{ {} }}", import.spelling, wanted.join(", ")),
            };
            // The edit is the fix of the import and of each error its list has.
            fixes.push((import.span, fix.clone()));
            fixes.extend(
                found
                    .iter()
                    .chain(&unused)
                    .map(|(_, at)| (*at, fix.clone())),
            );
        }
        errors.extend(found);
        if is_std(&modules[i]) {
            errors.extend(unused);
        } else {
            warnings.extend(unused);
        }
    }
}

/// The files each file sees through its imports: the files it imports
/// directly. An import of an import is not seen.
fn reaches(modules: &[String], imports: Option<&[Vec<usize>]>) -> Vec<HashSet<usize>> {
    (0..modules.len())
        .map(|i| {
            imports.map_or_else(HashSet::new, |im| {
                im[i].iter().copied().filter(|&j| j != i).collect()
            })
        })
        .collect()
}

fn qualify(
    files: &mut [Vec<Stmt>],
    modules: &[String],
    imports: Option<&[Vec<usize>]>,
    below: Option<&[HashSet<usize>]>,
    keep_prelude: bool,
    spell: Option<Spell>,
    lists: Option<(&[Vec<ImportList>], &[bool], &Quoted)>,
    fixes: &mut Vec<(Span, super::Fix)>,
    warnings: &mut Vec<(Message, Span)>,
) -> (
    Vec<(Message, Span)>,
    Vec<HashMap<String, String>>,
    Vec<MissingImport>,
) {
    register_modules(modules);
    let (lists, no_prelude, quoted) = match lists {
        Some((lists, no_prelude, quoted)) => (Some(lists), no_prelude, Some(quoted)),
        None => (None, &[][..], None),
    };
    let bare_at = |i: usize| no_prelude.get(i).copied().unwrap_or(false);
    // A function of a module is named `M::f` like any declaration: the
    // modules are flattened first, so this pass tells it apart from another
    // file's `M::f` and the prelude's.
    let mut ctors: HashSet<String> = prelude_ctors()
        .values()
        .flat_map(|cs| cs.keys().cloned())
        .collect();
    for stmts in files.iter() {
        for s in stmts {
            ctors_of(s, &mut |_, c| {
                ctors.insert(c.to_string());
            });
        }
    }
    let mut flattened = super::modules::flatten_files(
        files,
        prelude_fns().iter().map(|n| n.as_str()),
        &ctors,
        imports,
    );
    let mut prelude = prelude_names().clone();
    prelude.extend(LANGUAGE_TYPES.iter().map(|n| n.to_string()));
    // The kernel's sorts are the prelude's too: a file's declaration of
    // `Prop` is renamed to its full name, so another file's `Prop` still
    // means the sort, whatever else the importer reads.
    prelude.extend(SORTS.iter().map(|n| n.to_string()));
    let mut owners: HashMap<String, Vec<usize>> = HashMap::new();
    let mut written: Vec<(usize, String)> = Vec::new();
    // The language's types as the standard library declares them: they are
    // the prelude's, by their full names too.
    let mut language: Vec<String> = Vec::new();
    // The names each file declares as the language's type: they keep their
    // names in that file, whatever other file declares them too.
    let mut own_language: Vec<HashSet<String>> = vec![HashSet::new(); files.len()];
    // When the standard library is read, its declaration is the type and no
    // other is: a tote's copy of `std/Text.taut` is that tote's own `Text`,
    // and does not take the type's constructors from the library.
    let from_std: HashSet<&str> = files
        .iter()
        .enumerate()
        .filter(|(i, _)| is_std(&modules[*i]))
        .flat_map(|(_, stmts)| stmts.iter().filter_map(language_type))
        .collect();
    for (i, stmts) in files.iter().enumerate() {
        for s in stmts.iter() {
            let ty = language_type(s).filter(|t| is_std(&modules[i]) || !from_std.contains(t));
            let sort = inductive_sort(s);
            declared_or_bound(s, &mut |n| {
                if sort == Some(n) {
                    return;
                }
                if is_full(n, modules) {
                    written.push((i, n.to_string()));
                    return;
                }
                if ty.is_some_and(|t| {
                    n == t || GENERATED.iter().any(|g| n.strip_suffix(g) == Some(t))
                }) {
                    language.push(format!("{}{SEPARATOR}{n}", modules[i]));
                    own_language[i].insert(n.to_string());
                    return;
                }
                let v = owners.entry(n.to_string()).or_default();
                if !v.contains(&i) {
                    v.push(i);
                }
            });
        }
    }
    // The files each file sees: the files it imports directly, never what
    // those import.
    let reach = reaches(modules, imports);
    // A file the program reads only because a file importing this one
    // reads it too: what this file's names mean does not depend on it.
    // Whether `j` imports `i`, directly or through other files: `j` is one of
    // the importers of `i`.
    let imports_through = |j: usize, i: usize| {
        let mut seen = vec![false; reach.len()];
        let mut stack = vec![j];
        while let Some(k) = stack.pop() {
            if std::mem::replace(&mut seen[k], true) {
                continue;
            }
            for &m in &reach[k] {
                if m == i {
                    return true;
                }
                stack.push(m);
            }
        }
        false
    };
    let hidden = |i: usize, j: usize| {
        imports.is_some()
            && i != j
            && !reach[i].contains(&j)
            && reach.iter().any(|r| r.contains(&i) && r.contains(&j))
    };
    // The names each file declares without `pub`: another file does not see
    // them (`docs/design/visibility.md`), so they neither take a name it
    // writes nor make it ambiguous, and it may declare the name itself.
    let private: Vec<HashSet<String>> = files.iter().map(|stmts| private_names(stmts)).collect();
    let private_to = |i: usize, j: usize, n: &str| i != j && private[j].contains(n);
    // The names each file binds in a pattern (`p3(x, w1, z)`).
    let binds: Vec<HashSet<String>> = files.iter().map(|stmts| pattern_binders(stmts)).collect();
    // A file binds a name that a constructor with fields of a file it does
    // not see has (a bare name is never a pattern of such a constructor):
    // that constructor is named apart, so that the name there stays the
    // file's binder, whatever else its importer reads.
    let file_ctors: Vec<HashSet<String>> = files
        .iter()
        .map(|stmts| {
            let mut out = HashSet::new();
            stmts.iter().for_each(|s| ctors_with_fields(s, &mut out));
            out
        })
        .collect();
    let bound_apart = |n: &str, j: usize| {
        file_ctors[j].contains(n) && (0..binds.len()).any(|i| hidden(i, j) && binds[i].contains(n))
    };
    // The constructor names types of one file share, and the full name of
    // each: the module, the type and the name.
    let shared: Vec<HashMap<String, Vec<String>>> =
        files.iter().map(|stmts| shared_ctors(stmts)).collect();
    // The type of each constructor of a file that no other type of the file
    // shares the name of: a constructor's full name has its type too.
    let ctor_type: Vec<HashMap<String, String>> = files
        .iter()
        .enumerate()
        .map(|(i, stmts)| {
            let mut types: HashMap<String, Vec<String>> = HashMap::new();
            for s in stmts {
                ctors_of(s, &mut |ty, c| {
                    let c = c
                        .strip_prefix(ty)
                        .and_then(|rest| rest.strip_prefix(SEPARATOR))
                        .filter(|leaf| !leaf.contains(SEPARATOR))
                        .unwrap_or(c);
                    if c == ty || c.contains(SEPARATOR) || shared[i].contains_key(c) {
                        return;
                    }
                    let v = types.entry(c.to_string()).or_default();
                    if !v.iter().any(|t| t == ty) {
                        v.push(ty.to_string());
                    }
                });
            }
            types
                .into_iter()
                .filter_map(|(c, mut v)| (v.len() == 1).then(|| (c, v.remove(0))))
                .collect()
        })
        .collect();
    let scoped =
        |i: usize, ty: &str, n: &str| format!("{}{SEPARATOR}{ty}{SEPARATOR}{n}", modules[i]);
    let full = |i: usize, n: &str| match ctor_type[i].get(bare(n)) {
        Some(ty) => scoped(i, ty, bare(n)),
        None => format!("{}{SEPARATOR}{}", modules[i], bare(n)),
    };
    let fulls = |i: usize, n: &str| -> Vec<String> {
        match shared[i].get(n) {
            Some(types) => types.iter().map(|ty| scoped(i, ty, n)).collect(),
            None => vec![full(i, n)],
        }
    };
    // The bare names each file writes in a pattern: each binds a name unless
    // a constructor the file sees has it.
    let bound: Vec<HashSet<String>> = files.iter().map(|stmts| pattern_names(stmts)).collect();
    // A file that reaches no declaration of `n`, in its tote or through its
    // imports, and writes `n` alone in a pattern binds `n`: a constructor of a
    // file it does not import does not take the name (Safe by Default).
    let file_count = files.len();
    let ctor_names: Vec<HashSet<String>> = files
        .iter()
        .map(|stmts| {
            let mut out = HashSet::new();
            for s in stmts {
                ctors_of(s, &mut |_, c| {
                    out.insert(c.to_string());
                });
            }
            out
        })
        .collect();
    let binds_apart = |n: &str, owners_of: &[usize]| -> bool {
        imports.is_some()
            && owners_of.iter().all(|&j| ctor_names[j].contains(n))
            && (0..file_count).any(|i| {
                bound[i].contains(n)
                    && !owners_of.contains(&i)
                    && owners_of
                        .iter()
                        .all(|&j| !reach[i].contains(&j) && !same_tote(&modules[i], &modules[j]))
            })
    };
    let uses: Vec<HashSet<String>> = files.iter().map(|stmts| var_names(stmts)).collect();
    // A name only the standard library declares, written by a file of the
    // program that does not reach that declaration: the file did not import
    // it, so it does not mean it, in its tote or another (Safe by Default).
    // Where the name is the prelude's built-in too (`text_concat`), the file
    // runs it as written, as it would were the library not read at all.
    let unreached = |i: usize, n: &str, owners_of: &[usize]| {
        imports.is_some()
            && !owners_of.contains(&i)
            && owners_of.iter().all(|&j| !reach[i].contains(&j))
            && !prelude.contains(n)
    };
    let not_imported = |i: usize, n: &str, owners_of: &[usize]| {
        uses[i].contains(bare(n)) && unreached(i, n, owners_of)
    };
    // A declaration is renamed when another file, the prelude or another
    // type of its file has its name, or a file that does not reach it binds
    // the name in a pattern.
    let clash = |n: &str, owners_of: &[usize]| {
        owners_of.len() > 1
            || prelude.contains(n)
            || owners_of.iter().any(|&j| bound_apart(n, j))
            || owners_of.iter().any(|&i| shared[i].contains_key(n))
            || binds_apart(n, owners_of)
    };
    let renamed = |n: &str, owners_of: &[usize]| {
        clash(n, owners_of)
            || GENERATED.iter().any(|g| {
                n.strip_suffix(g)
                    .and_then(|t| Some((t, owners.get(t)?)))
                    .is_some_and(|(t, o)| clash(t, o))
            })
    };
    let any_not_imported = || {
        owners
            .iter()
            .any(|(n, o)| (0..file_count).any(|i| not_imported(i, n, o)))
    };
    if !owners.iter().any(|(n, o)| renamed(n, o))
        && written.is_empty()
        && !has_full_name(files, modules)
        && !any_not_imported()
        // A non-core prelude name is seen only through its import.
        && imports.is_none()
    {
        flattened.extend(record_bases(files));
        return (flattened, vec![HashMap::new(); files.len()], Vec::new());
    }
    // Renaming depends on declarations and import reachability, which stay
    // fixed while each file's reference environment is built.
    let renamed: HashSet<&str> = owners
        .iter()
        .filter(|(name, from)| renamed(name, from))
        .map(|(name, _)| name.as_str())
        .collect();
    let mut by_full: HashMap<String, String> = HashMap::new();
    for (n, o) in &owners {
        for &i in o {
            let mark = if n.starts_with(EFFECT) { EFFECT } else { "" };
            for f in fulls(i, n) {
                let to = if renamed.contains(n.as_str()) {
                    f.clone()
                } else {
                    bare(n).to_string()
                };
                by_full.insert(format!("{mark}{f}"), to);
            }
        }
    }
    for n in &prelude {
        let mark = if n.starts_with(EFFECT) { EFFECT } else { "" };
        by_full.insert(
            format!("{mark}{PRELUDE_MODULE}{SEPARATOR}{}", bare(n)),
            bare(n).to_string(),
        );
    }
    for (_, n) in &written {
        by_full.insert(n.clone(), bare(n).to_string());
    }
    let language_full: HashSet<String> = language.iter().cloned().collect();
    for n in language {
        let to = short(&n).to_string();
        by_full.insert(n, to);
    }
    let after = |i: usize, n: &str| match owners.get(n) {
        Some(_) if renamed.contains(n) => full(i, n),
        _ => n.to_string(),
    };
    // The functions and theorems of modules (`M::f`): those of a module written in the file
    // and those already flattened to their full names, as the modules are before this pass. A
    // reference to one is the declaration's own name, even when a type named `M` is renamed
    // because another file has a constructor of that name.
    let module_fns: HashSet<String> = files
        .iter()
        .flat_map(|stmts| {
            let mut names = super::modules::declared(stmts);
            names.extend(super::modules::declared_flat(stmts));
            names
        })
        .collect();
    let mut ctors = prelude_ctors().clone();
    // The constructors without fields, by those names: a bare name in a
    // pattern may be one of them.
    let mut nullary: HashSet<String> = HashSet::new();
    for (i, stmts) in files.iter().enumerate() {
        for s in stmts.iter() {
            ctors_of(s, &mut |ty, c| {
                let to = match shared[i].get(c) {
                    Some(types) if types.iter().any(|t| t == ty) => scoped(i, ty, c),
                    _ => after(i, c),
                };
                if !file_ctors[i].contains(c) {
                    nullary.insert(to.clone());
                }
                // On this pass's own output a renamed constructor is already
                // `m::T::C`, whose short name keeps its type (`T::C`): it is
                // `C` of `T`.
                let c = short(c);
                let c = c
                    .strip_prefix(short(ty))
                    .and_then(|c| c.strip_prefix(SEPARATOR))
                    .unwrap_or(c);
                ctors
                    .entry(after(i, ty))
                    .or_default()
                    .insert(c.to_string(), to);
            });
        }
    }
    // The type of each explicit argument of the functions and constructors,
    // by the names they have after this pass.
    let mut args: HashMap<String, Vec<Option<String>>> = HashMap::new();
    for (i, stmts) in files.iter().enumerate() {
        let named = |ty: &SurfaceTerm, bound: &[&str]| {
            type_head(ty)
                .filter(|h| !bound.contains(&h.as_str()))
                .map(|h| after(i, &h))
        };
        for s in stmts.iter() {
            arg_types(s, &mut |name, is_ctor, ty, tys| {
                let key = if is_ctor {
                    match ctors.get(&after(i, ty)).and_then(|cs| cs.get(short(name))) {
                        Some(to) => to.clone(),
                        None => return,
                    }
                } else {
                    after(i, name)
                };
                let bound: Vec<&str> = tys.iter().map(|(n, _)| n.as_str()).collect();
                let wanted = tys
                    .iter()
                    .enumerate()
                    .map(|(k, (_, t))| t.as_ref().and_then(|t| named(t, &bound[..k])))
                    .collect();
                args.insert(key, wanted);
            });
        }
    }
    // The type of each field of the constructors, by the names they have
    // after this pass.
    let mut fields = prelude_fields().clone();
    for (i, stmts) in files.iter().enumerate() {
        for s in stmts.iter() {
            field_types(
                s,
                &mut |ty, name, tys| {
                    if let Some(to) = ctors.get(&after(i, ty)).and_then(|cs| cs.get(short(name))) {
                        fields.insert(to.clone(), tys);
                    }
                },
                &|n| after(i, n),
            );
        }
    }
    let errors = std::cell::RefCell::new(redeclared(
        files,
        modules,
        &owners,
        &reach,
        &private,
        &ctor_names,
    ));
    let mut seeing = Vec::new();
    let missing = std::cell::RefCell::new(Vec::new());
    // The prelude's module functions the files of `std` model, by file.
    let modelled: Vec<HashSet<String>> = files
        .iter()
        .enumerate()
        .map(|(j, stmts)| models_in(j, stmts, modules))
        .collect();
    // Source meanings for each file's import environment.
    // What each file's imports with lists bring of each file, by the items of the lists; a
    // file imported without a list at least once brings everything (no entry).
    let brings: Vec<HashMap<usize, HashSet<String>>> = (0..files.len())
        .map(|i| {
            let mut out: HashMap<usize, HashSet<String>> = HashMap::new();
            let mut whole: HashSet<usize> = HashSet::new();
            for import in lists.and_then(|l| l.get(i)).into_iter().flatten() {
                let Some(j) = import.target else {
                    continue;
                };
                match &import.names {
                    Some(names) => out
                        .entry(j)
                        .or_default()
                        .extend(names.iter().map(|(n, _)| n.clone())),
                    None => {
                        whole.insert(j);
                    }
                }
            }
            out.retain(|j, _| !whole.contains(j));
            out
        })
        .collect();
    // Whether the file `i` imports `j` with lists none of which brings the name `n` of `j`:
    // a constructor's or a generated name's type, a module's function's module, an effect.
    let unlisted = |i: usize, j: usize, n: &str| {
        let Some(items) = brings[i].get(&j) else {
            return false;
        };
        let b = bare(n);
        let item = if n.starts_with(EFFECT) {
            b.to_string()
        } else if let Some(ty) = ctor_type[j].get(b) {
            ty.clone()
        } else {
            b.split(SEPARATOR).next().unwrap_or(b).to_string()
        };
        !items.contains(&item)
    };
    let mut all_names: Vec<HashMap<String, Meaning>> = Vec::new();
    let mut all_unseen: Vec<HashSet<String>> = Vec::new();
    let mut all_plain: Vec<HashMap<String, String>> = Vec::new();
    // The names each file declares that this pass renames, with the full
    // name each declaration takes: where a name is ambiguous to read (a
    // non-core prelude name the file imports and declares too), the
    // declaration is still the file's own.
    let mut all_declares: Vec<HashMap<String, String>> = Vec::new();
    let mut all_prelude_files: Vec<HashMap<String, String>> = Vec::new();
    for i in 0..files.len() {
        let mut names: HashMap<String, Meaning> = HashMap::new();
        let mut declares: HashMap<String, String> = HashMap::new();
        // The names the file sees both from the prelude file it imports
        // and from a declaration of its own or of its imports, with that
        // prelude file.
        let mut prelude_files: HashMap<String, String> = HashMap::new();
        let mut unseen: HashSet<String> = HashSet::new();
        let mut plain: HashMap<String, String> = HashMap::new();
        for (n, all) in &owners {
            if not_imported(i, n, all) || (n.starts_with(EFFECT) && unreached(i, n, all)) {
                names.insert(
                    n.clone(),
                    Meaning::NotImported(
                        modules[all[0]].clone(),
                        spelling(spell, modules, i, all[0]),
                        all.len() == 1,
                    ),
                );
                continue;
            }
            if !renamed.contains(n.as_str()) {
                // A name that keeps its short name is still the declaration
                // of the one file this one sees that declares it: a macro of
                // this file that writes it means that one wherever it is
                // expanded, the importer of the macro's file not importing it.
                if imports.is_some() && !own_language[i].contains(n) {
                    let mut visible = all
                        .iter()
                        .copied()
                        .filter(|&j| (j == i || reach[i].contains(&j)) && !private_to(i, j, n));
                    if let (Some(_), None) = (visible.next(), visible.next()) {
                        plain.insert(n.clone(), n.clone());
                    }
                }
                continue;
            }
            if own_language[i].contains(n) {
                continue;
            }
            // A name only private declarations of other files have still
            // means them, so that the use is reported as private.
            let seen: Vec<usize> = all
                .iter()
                .copied()
                .filter(|&j| !private_to(i, j, n))
                .collect();
            // An import with a list brings only what it lists: a file it does not bring the
            // name from does not take it. Where no file brings it, the name is kept to the files
            // that declare it, and the list's check says which list to write it in.
            let brought: Vec<usize> = seen
                .iter()
                .copied()
                .filter(|&j| !unlisted(i, j, n))
                .collect();
            let seen = if brought.is_empty() { seen } else { brought };
            let o = if seen.is_empty() { all } else { &seen };
            let meaning = if o.contains(&i) {
                // The file's own, unless types of the file share the name.
                match fulls(i, n).as_slice() {
                    [one] => {
                        declares.insert(n.clone(), one.clone());
                        Meaning::To(one.clone())
                    }
                    all => Meaning::Ambiguous(all.to_vec()),
                }
            } else {
                // The files this one imports, then, for the prelude's names,
                // the prelude, then any file of the program.
                let imported: Vec<usize> = match imports {
                    Some(imports) => o
                        .iter()
                        .copied()
                        .filter(|j| imports[i].contains(j))
                        .collect(),
                    None => o.clone(),
                };
                // The language's type, unless this file imports another
                // declaration of its name: that one is not read as the type
                // without a word (Safe by Default).
                if LANGUAGE_TYPES.contains(&n.as_str())
                    && (imports.is_none() || imported.is_empty())
                {
                    continue;
                }
                // A prelude name a file this one reaches through its imports
                // declares is that file's: the imports say which declaration
                // is meant, as they do for any other name, and a name the
                // prelude takes on later does not change what it means.
                let reached_prelude: Vec<usize> = match imports {
                    Some(_) if imported.is_empty() && prelude.contains(n) => {
                        o.iter().copied().filter(|j| reach[i].contains(j)).collect()
                    }
                    _ => Vec::new(),
                };
                // A prelude name a file of the same tote or of a tote it
                // depends on directly declares, and this file does not reach, is not
                // taken as either one: both are named and the full name is to
                // be written. A file of `std` is left out: it is the model of
                // the prelude's builtin.
                // A file of the tote that a file importing this one reaches is
                // left out too: it is read because the importer imports it, and
                // what this file's names mean does not depend on its importers.
                let behind: Vec<usize> = match imports {
                    Some(_)
                        if imported.is_empty()
                            && reached_prelude.is_empty()
                            && prelude.contains(n) =>
                    {
                        o.iter()
                            .copied()
                            .filter(|&j| {
                                (same_tote(&modules[i], &modules[j])
                                    && !is_std(&modules[j])
                                    && !reach.iter().any(|r| r.contains(&i) && r.contains(&j))
                                    && !imports_through(j, i))
                                    || below.is_some_and(|b| b[i].contains(&j))
                            })
                            .collect()
                    }
                    _ => Vec::new(),
                };
                // Except the standard library's: a file of `std` that declares
                // a prelude name is the model the proofs see of that builtin
                // (`std::Text::Text::len` of `text_len`), and a file that reaches
                // it means that one.
                let std_behind: Vec<usize> = behind
                    .iter()
                    .copied()
                    .filter(|&j| is_std(&modules[j]))
                    .collect();
                let behind = if std_behind.len() == 1 && behind.len() == 1 {
                    names.insert(n.clone(), Meaning::To(full(std_behind[0], n)));
                    continue;
                } else {
                    behind
                };
                let through = imported.is_empty() && !behind.is_empty();
                // A file the imports reach, the imports of those included:
                // what a file's names mean is fixed by its own imports, never
                // by a file only its importer reads.
                let reached: Vec<usize> = match imports {
                    Some(_) => o.iter().copied().filter(|j| reach[i].contains(j)).collect(),
                    None => Vec::new(),
                };
                let from = if !imported.is_empty() {
                    imported
                } else if !reached_prelude.is_empty() {
                    reached_prelude
                } else if through {
                    behind
                } else if prelude.contains(n) {
                    continue;
                } else if !reached.is_empty() {
                    reached
                } else if imports.is_some()
                    && bound[i].contains(n)
                    && !o.iter().any(|&j| same_tote(&modules[i], &modules[j]))
                {
                    // Written alone in a pattern, a name no import declares binds it.
                    unseen.insert(n.clone());
                    continue;
                } else {
                    if o.iter().all(|&j| bound_apart(n, j) && hidden(i, j))
                        && binds[i].contains(n.as_str())
                    {
                        unseen.insert(n.clone());
                        continue;
                    }
                    // No import reaches a declaration of the name: it is not
                    // visible here, whichever file of the program declares it.
                    if imports.is_some() {
                        names.insert(
                            n.clone(),
                            Meaning::NotImported(
                                modules[o[0]].clone(),
                                spelling(spell, modules, i, o[0]),
                                o.len() == 1,
                            ),
                        );
                        continue;
                    }
                    o.clone()
                };
                let mut others: Vec<String> = from.iter().flat_map(|&j| fulls(j, n)).collect();
                if through {
                    others.push(format!("{PRELUDE_MODULE}{SEPARATOR}{}", bare(n)));
                }
                match others.as_slice() {
                    [one] => Meaning::To(one.clone()),
                    _ => Meaning::Ambiguous(others),
                }
            };
            names.insert(n.clone(), meaning);
        }
        for (name, effect_owners) in owners.iter().filter(|(name, _)| name.starts_with(EFFECT)) {
            for &owner in effect_owners {
                if imports.is_some() && owner != i && !reach[i].contains(&owner) {
                    for full in fulls(owner, name) {
                        names.insert(
                            format!("{EFFECT}{full}"),
                            Meaning::NotImported(
                                modules[owner].clone(),
                                spelling(spell, modules, i, owner),
                                true,
                            ),
                        );
                    }
                }
            }
        }
        // A prelude file that is not core is seen through its import only
        // (`import std::prelude::Os`): a name only it declares, written
        // without the import, is not visible; with the import, a file's own
        // or imported declaration of the same name is ambiguous with it.
        if imports.is_some() {
            // A preceding binding pass may have given a constructor its owner's
            // qualified name. Its source alias remains visible with that owner.
            let mut visible_constructors = HashSet::new();
            for j in std::iter::once(i).chain(reach[i].iter().copied()) {
                for statement in &files[j] {
                    ctors_of(statement, &mut |family, constructor| {
                        if j == i || (!private_to(i, j, family) && !unlisted(i, j, short(family))) {
                            visible_constructors
                                .insert(constructor.rsplit(SEPARATOR).next().unwrap().to_string());
                        }
                    });
                }
            }
            // What the file declares itself, a module by its name: its own, whatever the
            // prelude file it does not import declares by that name.
            let own: HashSet<&str> = owners
                .iter()
                .filter(|(_, o)| o.contains(&i))
                .map(|(k, _)| k.split(SEPARATOR).next().unwrap_or(k))
                .collect();
            // A file of a tote without the prelude sees the core prelude's names the same way.
            let core = bare_at(i).then(core_prelude).into_iter().flatten();
            for (n, files) in hidden_prelude().iter().chain(core) {
                // A core name a file this one reaches declares (the standard library's model
                // of a builtin) means that declaration, as it does where the prelude is seen.
                if !hidden_prelude().contains_key(n) && names.contains_key(n) {
                    continue;
                }
                // An import with a list brings only what it lists.
                let granted = files.iter().any(|f| {
                    let module = prelude_file_module(f);
                    reach[i].iter().any(|&j| {
                        modules[j] == module
                            && brings[i]
                                .get(&j)
                                .is_none_or(|items| items.contains(&prelude_item(n)))
                    })
                });
                let prelude_full = format!("{PRELUDE_MODULE}{SEPARATOR}{}", bare(n));
                match (names.get_mut(n), granted) {
                    // The file imports the prelude file that declares it: a macro of
                    // this file that writes it means that declaration wherever it is
                    // expanded, the importer of the macro's file not importing it.
                    (None, true) => {
                        plain.insert(n.clone(), n.clone());
                    }
                    (None, false) if own.contains(n.as_str()) => {}
                    // A declaration of that name the file's imports bring (`U64` of
                    // `import "UInt.taut" { U64 }`) is the one the name means.
                    (None, false)
                        if owners.get(n).is_some_and(|all| {
                            all.iter().any(|&j| {
                                reach[i].contains(&j) && !private_to(i, j, n) && !unlisted(i, j, n)
                            })
                        }) => {}
                    // A constructor the file sees by that name (`I64` of a type `Width`)
                    // is read as that constructor, as it is where the prelude file is
                    // imported.
                    (None, false) if visible_constructors.contains(n.as_str()) => {}
                    (None, false) => {
                        names.insert(
                            n.clone(),
                            Meaning::NotImported(
                                prelude_file_module(&files[0]),
                                prelude_file_module(&files[0]),
                                true,
                            ),
                        );
                    }
                    (Some(Meaning::To(to)), true) if !is_library_name(to) => {
                        let both = vec![std::mem::take(to), prelude_full];
                        names.insert(n.clone(), Meaning::Ambiguous(both));
                        prelude_files.insert(n.clone(), prelude_file_module(&files[0]));
                    }
                    (Some(Meaning::Ambiguous(all)), true)
                        if !all.iter().any(|a| is_library_name(a)) =>
                    {
                        all.push(prelude_full);
                        prelude_files.insert(n.clone(), prelude_file_module(&files[0]));
                    }
                    _ => {}
                }
            }
        }
        all_names.push(names);
        all_unseen.push(unseen);
        all_plain.push(plain);
        all_declares.push(declares);
        all_prelude_files.push(prelude_files);
    }
    // The global names each file writes, as read, when its import lists are checked.
    let used: Vec<std::cell::RefCell<Vec<SourceUse>>> =
        (0..files.len()).map(|_| Default::default()).collect();
    for (i, stmts) in files.iter_mut().enumerate() {
        let names = &all_names[i];
        let plain = std::mem::take(&mut all_plain[i]);
        let r = Renamer {
            names,
            by_full: &by_full,
            module_fns: &module_fns,
            ctors: &ctors,
            nullary: &nullary,
            args: &args,
            fields: &fields,
            unseen: &all_unseen[i],
            locals: Default::default(),
            typed: Default::default(),
            returns: Default::default(),
            errors: &errors,
            sealed: None,
            seen: None,
            missing: Some((&missing, i)),
            declares: Some(&all_declares[i]),
            prelude_files: Some(&all_prelude_files[i]),
            keep_prelude,
            used: lists.map(|_| &used[i]),
            quoting: Default::default(),
        };
        for s in stmts.iter_mut() {
            r.top(s);
        }
        let library = crate::bindings::library_bindings();
        let implicit = library
            .bindings()
            .filter(|(name, _)| {
                let item = prelude_item(name);
                !names.contains_key(*name)
                    && !names.contains_key(&item)
                    && !hidden_prelude().contains_key(*name)
                    && !hidden_prelude().contains_key(&item)
                    && (!bare_at(i)
                        || (!core_prelude().contains_key(*name)
                            && !core_prelude().contains_key(&item)))
            })
            .map(|(name, _)| (name.to_string(), name.to_string()));
        seeing.push(
            implicit
                .chain(names.iter().flat_map(|(n, m)| {
                    match m {
                        Meaning::To(to) => vec![(n.clone(), to.clone()), (to.clone(), to.clone())],
                        // A shared short spelling hides neither declaration's
                        // full path from the file's reference environment.
                        Meaning::Ambiguous(all) => all
                            .iter()
                            .map(|full| (full.clone(), full.clone()))
                            .collect(),
                        Meaning::NotImported(..) => Vec::new(),
                    }
                }))
                // A module function of the prelude that no file this one
                // reaches models (`Text::of_nat` without `std::Text`) is the
                // builtin: a macro of the file that writes it means that,
                // wherever it is expanded ([`split_models`]).
                .chain(
                    runtime_module_fns()
                        .iter()
                        .filter(|_| keep_prelude && imports.is_some())
                        .filter(|n| {
                            !matches!(
                                names.get(*n),
                                Some(Meaning::NotImported(..) | Meaning::Ambiguous(_))
                            )
                        })
                        .filter(|n| {
                            !std::iter::once(&i)
                                .chain(&reach[i])
                                .any(|&j| modelled[j].contains(*n))
                        })
                        .map(|n| (n.clone(), format!("{PRELUDE_MODULE}{SEPARATOR}{n}"))),
                )
                .chain(written.iter().filter_map(|(owner, name)| {
                    let local = bare(name)
                        .strip_prefix(&format!("{}{SEPARATOR}", modules[*owner]))
                        .unwrap_or(bare(name));
                    (*owner == i
                        || (reach[i].contains(owner)
                            && !private_to(i, *owner, name)
                            && !unlisted(i, *owner, local)))
                    .then(|| (name.clone(), name.clone()))
                }))
                .chain(plain)
                .collect(),
        );
    }
    // Capture source uses before expansion. A generated reference belongs to the
    // macro definition's imports; it does not add an import use at the call site.
    if let Some(quoted) = quoted {
        let mut quoted = quoted.borrow_mut();
        quoted.resize(files.len(), Vec::new());
        for (q, u) in quoted.iter_mut().zip(&used) {
            if keep_prelude {
                *q = u.take();
            } else {
                u.borrow_mut().extend(q.iter().cloned());
            }
        }
    }
    let mut errors = errors.into_inner();
    if let Some(lists) = lists.filter(|_| !keep_prelude) {
        for (i, file_lists) in lists.iter().enumerate().take(files.len()) {
            check_import_lists(
                bare_at(i),
                i,
                files,
                modules,
                &owners,
                &reach,
                &private,
                &ctor_type,
                &language_full,
                file_lists,
                &used[i].borrow(),
                &mut errors,
                warnings,
                fixes,
            );
        }
    }
    flattened.extend(errors);
    flattened.extend(record_bases(files));
    (flattened, seeing, missing.into_inner())
}

/// The name a base that is not a name is bound to: `@` keeps it from any
/// name a program writes.
const RECORD_BASE: &str = "base@record";

/// Writes out each `S { f: e, ..b }` of `files` as the literal with every
/// field: a field not written is `b`'s, `b.g`. A base that is not a name is
/// bound first, so it is evaluated once, before the fields:
/// `{ let base@record = b; S { f: e, g: base@record.g } }`. The kernel and
/// the passes that run a program get a literal they already read. Returns
/// the literals whose name is not a struct's, and those whose fields are all
/// written, where `..b` would be read for nothing.
pub fn record_bases(files: &mut [Vec<Stmt>]) -> Vec<(Message, Span)> {
    // A struct a module declares is also named with its module, `M::P`.
    fn structs(stmts: &[Stmt], module: &str, out: &mut HashMap<String, Vec<String>>) {
        for s in stmts {
            match s {
                Stmt::Struct(d) => {
                    if let [c] = d.constructors.as_slice() {
                        let names: Vec<String> =
                            c.fields.iter().filter_map(|(n, _)| n.clone()).collect();
                        if !module.is_empty() {
                            out.insert(format!("{module}::{}", d.name), names.clone());
                        }
                        out.insert(d.name.to_string(), names);
                    }
                }
                Stmt::Mutual { items, .. } => structs(items, module, out),
                Stmt::Module { name, items, .. } => {
                    let inner = if module.is_empty() {
                        name.clone()
                    } else {
                        format!("{module}::{name}")
                    };
                    structs(items, &inner, out)
                }
                Stmt::Attributed { stmt, .. } => {
                    structs(std::slice::from_ref(&**stmt), module, out)
                }
                _ => {}
            }
        }
    }
    let mut fields = HashMap::new();
    for stmts in files.iter() {
        structs(stmts, "", &mut fields);
    }
    let mut errors = Vec::new();
    for stmts in files.iter_mut() {
        for s in stmts.iter_mut() {
            super::walk::stmt(s, &mut |t| {
                let span = t.span;
                let TermKind::Record {
                    name,
                    fields: written,
                    base,
                } = Arc::make_mut(&mut t.kind)
                else {
                    return;
                };
                let Some(b) = base.take() else {
                    return;
                };
                let Some(all) = fields.get(name.as_str()) else {
                    errors.push((
                        format!(
                            "`{name}` is not a struct: `..` takes the other fields of a struct"
                        ),
                        span,
                    ));
                    return;
                };
                let rest: Vec<&String> = all
                    .iter()
                    .filter(|f| !written.iter().any(|(w, _)| w == *f))
                    .collect();
                if rest.is_empty() {
                    errors.push((
                        format!("every field of `{name}` is written: `..` takes none of them"),
                        b.span,
                    ));
                    return;
                }
                let from = match &*b.kind {
                    TermKind::Var(_) => (*b).clone(),
                    _ => SurfaceTerm::var(RECORD_BASE, b.span),
                };
                for f in rest {
                    let value = SurfaceTerm::new(
                        TermKind::Field {
                            base: Box::new(from.clone()),
                            name: f.clone(),
                        },
                        b.span,
                    );
                    written.push((f.clone(), value));
                }
                if !matches!(&*b.kind, TermKind::Var(_)) {
                    let record = std::mem::replace(t, SurfaceTerm::var(RECORD_BASE, span));
                    *t = SurfaceTerm::new(
                        TermKind::Block(vec![
                            Stmt::Let {
                                name: RECORD_BASE.into(),
                                ty: None,
                                value: *b,
                                borrow: false,
                                borrow_mut: false,
                            },
                            Stmt::Expr(record),
                        ]),
                        span,
                    );
                }
            });
        }
    }
    errors
        .into_iter()
        .map(|(t, s): (String, Span)| (t.into(), s))
        .collect()
}

/// A file may not declare a name its imports already declare, directly or
/// through their own imports: the file's declaration would quietly take the
/// name over, and a file importing both would read one where it wrote the
/// other (Safe by Default). The name is given to one declaration only; the
/// other is named apart. Returns each declaration that reuses a name, once
/// per statement.
fn redeclared(
    files: &[Vec<Stmt>],
    modules: &[String],
    owners: &HashMap<String, Vec<usize>>,
    reach: &[HashSet<usize>],
    private: &[HashSet<String>],
    ctors: &[HashSet<String>],
) -> Vec<(Message, Span)> {
    let mut out = Vec::new();
    for (i, stmts) in files.iter().enumerate() {
        for s in stmts {
            let mut first: Option<(String, usize)> = None;
            // A constructor is named by its type: the same constructor name
            // in another file's type is not a redeclaration.
            let mut own_ctors: HashSet<String> = HashSet::new();
            inductive_ctors(s, &mut |_, c| {
                own_ctors.insert(c.to_string());
            });
            declared(s, &mut |n| {
                if first.is_some() {
                    return;
                }
                if own_ctors.contains(n)
                    && owners
                        .get(n)
                        .is_some_and(|o| o.iter().all(|&j| j == i || ctors[j].contains(n)))
                {
                    return;
                }
                let earlier = owners.get(n).and_then(|o| {
                    o.iter()
                        .copied()
                        .find(|&j| j != i && reach[i].contains(&j) && !private[j].contains(n))
                });
                if let Some(j) = earlier {
                    first = Some((n.to_string(), j));
                }
            });
            if let Some((n, j)) = first {
                out.push((
                    format!(
                        "`{}` is already declared as `{}::{}`, which this file imports; give this declaration another name",
                        bare(&n),
                        written(&modules[j]),
                        bare(&n)
                    ),
                    stmt_span(s),
                ));
            }
        }
    }
    out.into_iter()
        .map(|(t, s): (String, Span)| (t.into(), s))
        .collect()
}

fn stmt_span(s: &Stmt) -> Span {
    match s {
        Stmt::Theorem(t) | Stmt::Def(t) => t.span,
        Stmt::Inductive(i) => i.span,
        Stmt::Fn(f) => f.span,
        Stmt::Class(c) => c.span,
        Stmt::Mutual { span, .. } => *span,
        Stmt::Attributed { stmt, .. } => stmt_span(stmt),
        _ => Span::default(),
    }
}

/// A function of the standard library that has a prelude function's name is
/// the model the proofs see of that builtin, and a file that reaches it
/// means it instead of the builtin. So the two must take and give the same
/// things: else whether a file imports the model, directly or through any
/// file it imports, changes the type of a call written alike in both
/// (`U8::of_u64(U64::of_nat(n))`), and which one is meant cannot be read
/// from the call. The types are the same up to how a number is read: the
/// builtin's machine word (`u64`, `nat`) is the model's number (`U64`,
/// `Nat`); anything else (an `Option` added or dropped, `i64` for
/// `Ordering`) is a different function and takes a name of its own. Returns each model that differs.
pub fn std_models(files: &[Vec<Stmt>], modules: &[String]) -> Vec<(Message, Span)> {
    fn last(name: &str) -> &str {
        name.rsplit_once(SEPARATOR).map_or(name, |(_, n)| n)
    }
    // Each function with the modules it is written in: `U64::of_nat`.
    fn fns<'a>(s: &'a Stmt, at: &str, out: &mut Vec<(String, &'a super::program::FnDecl)>) {
        match s {
            Stmt::Fn(f) => out.push((format!("{at}{}", f.name), f)),
            Stmt::Extern { fns, .. } => {
                out.extend(fns.iter().map(|f| (format!("{at}{}", f.name), f)))
            }
            Stmt::Attributed { stmt, .. } => fns(stmt, at, out),
            Stmt::Mutual { items, .. } => items.iter().for_each(|i| fns(i, at, out)),
            Stmt::Module { name, items, .. } => {
                let at = format!("{at}{name}{SEPARATOR}");
                items.iter().for_each(|i| fns(i, &at, out))
            }
            _ => {}
        }
    }
    // The type as written, each name by its short name, with a number and
    // a truth value read as one.
    fn shape(t: &Option<SurfaceTerm>) -> Option<String> {
        const NUMBERS: &[&str] = &[
            "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "nat", "I8", "I16", "I32", "I64",
            "U8", "U16", "U32", "U64", "Nat",
        ];
        let text = super::print::print_term(t.as_ref()?);
        let mut out = String::new();
        let mut word = String::new();
        let flush = |word: &mut String, out: &mut String| {
            let w = last(word);
            out.push_str(if NUMBERS.contains(&w) { "#number" } else { w });
            word.clear();
        };
        for c in text.chars() {
            if c.is_alphanumeric() || c == '_' || c == ':' {
                word.push(c);
            } else {
                flush(&mut word, &mut out);
                if !c.is_whitespace() {
                    out.push(c);
                }
            }
        }
        flush(&mut word, &mut out);
        Some(out)
    }
    fn signature(f: &super::program::FnDecl) -> Option<(Vec<String>, String)> {
        let params = f
            .param_types
            .iter()
            .map(shape)
            .collect::<Option<Vec<_>>>()?;
        Some((params, shape(&f.result)?))
    }
    static BUILTINS: OnceLock<HashMap<String, (Vec<String>, String)>> = OnceLock::new();
    let builtins = BUILTINS.get_or_init(|| {
        let mut builtins = HashMap::new();
        if let Ok(program) = super::program::prelude_as_written(crate::nibstd::PRELUDE) {
            let mut found = Vec::new();
            program.stmts.iter().for_each(|s| fns(s, "", &mut found));
            for (name, f) in found {
                if let Some(sig) = signature(f) {
                    builtins.insert(short(&name).to_string(), sig);
                }
            }
        }
        builtins
    });
    let mut errors = Vec::new();
    for (stmts, module) in files.iter().zip(modules) {
        if !is_std(module) {
            continue;
        }
        let mut found = Vec::new();
        stmts.iter().for_each(|s| fns(s, "", &mut found));
        for (name, f) in found {
            // The name in the file: a full name has the file's module before it.
            let name = name
                .strip_prefix(module.as_str())
                .and_then(|n| n.strip_prefix(SEPARATOR))
                .unwrap_or(&name)
                .to_string();
            let (Some(builtin), Some(model)) = (builtins.get(&name), signature(f)) else {
                continue;
            };
            if *builtin != model {
                errors.push((
                    format!(
                        "`{module}{SEPARATOR}{name}` has the name of the builtin `{name}` but not its type: a model of a builtin takes and gives what the builtin does (a number read as the model's); give a different function a name of its own"
                    ),
                    f.span,
                ));
            }
        }
    }
    errors
        .into_iter()
        .map(|(t, s): (String, Span)| (t.into(), s))
        .collect()
}

/// The `extern` functions of a tote are its own: a file of another tote may
/// not call one, so a library hands out its host access only through
/// functions it writes around it (Safe by Default). `totes[i]` is the tote of
/// the file `files[i]`, `None` for a file of no tote (the standard library, a
/// program read without a manifest), whose externs anyone may call. Runs on
/// the output of `files`, after the macros, so a macro of the tote cannot
/// hand its extern to another tote either. Returns each call from outside.
pub fn sealed_externs(files: &[Vec<Stmt>], totes: &[Option<String>]) -> Vec<(Message, Span)> {
    fn externs(s: &Stmt, out: &mut dyn FnMut(&str)) {
        match s {
            Stmt::Extern { fns, .. } => fns.iter().for_each(|f| out(&f.name)),
            Stmt::Attributed { stmt, .. } => externs(stmt, out),
            _ => {}
        }
    }
    let mut owner: HashMap<String, String> = HashMap::new();
    for (stmts, tote) in files.iter().zip(totes) {
        let Some(tote) = tote else { continue };
        for s in stmts {
            externs(s, &mut |n| {
                owner.insert(n.to_string(), tote.clone());
            });
        }
    }
    if owner.is_empty() {
        return Vec::new();
    }
    let (names, by_full, ctors) = (HashMap::new(), HashMap::new(), HashMap::new());
    let (nullary, module_fns) = (HashSet::new(), HashSet::new());
    let errors = std::cell::RefCell::new(Vec::new());
    for (stmts, tote) in files.iter().zip(totes) {
        let r = Renamer {
            names: &names,
            by_full: &by_full,
            module_fns: &module_fns,
            ctors: &ctors,
            nullary: &nullary,
            args: &HashMap::new(),
            fields: &HashMap::new(),
            unseen: &nullary,
            locals: Default::default(),
            typed: Default::default(),
            returns: Default::default(),
            errors: &errors,
            sealed: Some((&owner, tote.as_deref())),
            seen: None,
            missing: None,
            declares: None,
            prelude_files: None,
            keep_prelude: false,
            used: None,
            quoting: Default::default(),
        };
        // The walk renames nothing with empty tables; it runs on a copy so
        // that it only reads.
        for s in stmts.clone().iter_mut() {
            r.top(s);
        }
    }
    errors.into_inner()
}

/// Who declares each name of a program and how far it is seen, as
/// `sealed_visibility` reads it: the file, by its index (`PRELUDE_FILE` for
/// the prelude), and the `pub` written before the declaration.
pub struct Seen {
    names: HashMap<String, (usize, Vis)>,
    /// Each constructor, and what the kernel makes to take a type apart
    /// (`T::rec`), with its type.
    ctors: HashMap<String, (usize, Vis, String)>,
    effects: HashMap<String, (usize, Vis)>,
    /// Each class by its last name segment, with every file that declares
    /// one of that name.
    classes: HashMap<String, Vec<(usize, Vis)>>,
    /// Each field name, with every type that has it: a field of a struct or
    /// an enum, or a parameter of an inductive type's constructor.
    fields: HashMap<String, Vec<(usize, Vis, String)>>,
    modules: Vec<String>,
}

const PRELUDE_FILE: usize = usize::MAX;

/// What the kernel makes for an inductive type that takes its values apart:
/// written outside the type's file, it reads the constructors as a pattern
/// does.
const TAKES_APART: &[&str] = &["::rec", "::ind", "::noconf", "::nc", "::nc_diag"];

impl Seen {
    fn file(&self, i: usize) -> Message {
        match self.modules.get(i) {
            Some(m) => msg!("surface-the-file", file = m),
            None => msg!("surface-the-prelude"),
        }
    }

    fn add(&mut self, s: &Stmt, file: usize) {
        let insert = |names: &mut HashMap<String, (usize, Vis)>, n: &str, vis: Vis| {
            names.entry(n.to_string()).or_insert((file, vis));
        };
        match s {
            Stmt::Fn(f) => insert(&mut self.names, &f.name, f.vis),
            Stmt::Theorem(d) | Stmt::Def(d) => insert(&mut self.names, &d.name, d.vis),
            Stmt::Class(c) => {
                insert(&mut self.names, &c.name, c.vis);
                self.classes
                    .entry(last_segment(&c.name).to_string())
                    .or_default()
                    .push((file, c.vis));
            }
            Stmt::Struct(d) | Stmt::Enum(d) => {
                insert(&mut self.names, &d.name, d.vis);
                for c in &d.constructors {
                    self.ctors.entry(c.name.to_string()).or_insert((
                        file,
                        d.vis,
                        d.name.to_string(),
                    ));
                    for (f, _) in &c.fields {
                        let Some(f) = f else { continue };
                        self.fields.entry(f.to_string()).or_default().push((
                            file,
                            d.vis,
                            d.name.to_string(),
                        ));
                    }
                }
            }
            Stmt::Inductive(d) => {
                insert(&mut self.names, &d.name, d.vis);
                for c in &d.constructors {
                    self.ctors.entry(c.name.to_string()).or_insert((
                        file,
                        d.vis,
                        d.name.to_string(),
                    ));
                    // `x.f` reads a constructor's parameter `f` as a field.
                    for (f, _) in &c.params {
                        self.fields.entry(f.to_string()).or_default().push((
                            file,
                            d.vis,
                            d.name.to_string(),
                        ));
                    }
                }
                for g in GENERATED {
                    let n = format!("{}{g}", d.name);
                    if TAKES_APART.contains(g) {
                        self.ctors
                            .entry(n)
                            .or_insert((file, d.vis, d.name.to_string()));
                    } else {
                        insert(&mut self.names, &n, d.vis);
                    }
                }
            }
            Stmt::Effect(e) => {
                insert(&mut self.names, &format!("{EFFECT}{}", e.name), e.vis);
                self.effects
                    .entry(e.name.to_string())
                    .or_insert((file, e.vis));
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                items.iter().for_each(|i| self.add(i, file))
            }
            Stmt::Attributed { stmt, .. } => self.add(stmt, file),
            _ => {}
        }
    }
}

/// The prelude as `sealed_visibility` reads it: what is inside its types and
/// effects, which a program sees only where it is written `pub(open)`. Its
/// names are seen everywhere, so only what is inside is kept.
fn prelude_seen() -> &'static Seen {
    static SEEN: OnceLock<Seen> = OnceLock::new();
    SEEN.get_or_init(|| {
        let mut seen = Seen {
            names: HashMap::new(),
            ctors: HashMap::new(),
            effects: HashMap::new(),
            classes: HashMap::new(),
            fields: HashMap::new(),
            modules: Vec::new(),
        };
        for text in [crate::nibstd::PRELUDE, crate::nibstd::KERNEL] {
            if let Ok(program) = super::program::prelude_as_written(text) {
                for s in &program.stmts {
                    seen.add(s, PRELUDE_FILE);
                }
            }
        }
        seen.names.clear();
        seen
    })
}

/// A declaration is seen only in its file unless it is written `pub`, and
/// what is inside a type or an effect only with `pub(open)`
/// (`docs/design/visibility.md`): another file may not name a private
/// declaration, build or take apart a value of an abstract type (its
/// constructors, literals, patterns and fields, and what the kernel makes
/// to take it apart), or handle an effect that is not open. The prelude's
/// names are seen everywhere; what is inside its types and effects follows
/// the same rule. Runs on the output of `files`, after the macros, so what a
/// macro writes into another file is held to that file. Returns each use
/// that is not allowed.
pub fn sealed_visibility(files: &[Vec<Stmt>], modules: &[String]) -> Vec<(Message, Span)> {
    visibility(files, modules, false)
}

/// Checks source aliases before expansion replaces their uses with member effects.
pub fn effect_set_visibility(files: &[Vec<Stmt>], modules: &[String]) -> Vec<(Message, Span)> {
    visibility(files, modules, true)
}

fn visibility(files: &[Vec<Stmt>], modules: &[String], aliases_only: bool) -> Vec<(Message, Span)> {
    let prelude = prelude_seen();
    let mut seen = Seen {
        names: HashMap::new(),
        ctors: if aliases_only {
            HashMap::new()
        } else {
            prelude.ctors.clone()
        },
        effects: if aliases_only {
            HashMap::new()
        } else {
            prelude.effects.clone()
        },
        classes: if aliases_only {
            HashMap::new()
        } else {
            prelude.classes.clone()
        },
        fields: if aliases_only {
            HashMap::new()
        } else {
            prelude.fields.clone()
        },
        modules: modules.to_vec(),
    };
    for (i, stmts) in files.iter().enumerate() {
        for s in stmts {
            if !aliases_only || matches!(s, Stmt::Effect(e) if e.set.is_some()) {
                seen.add(s, i);
            }
        }
    }
    // A name the prelude declares stays the prelude's, wherever else it is declared.
    let prelude_names = prelude_names();
    seen.names
        .retain(|n, _| !prelude_names.contains(n.as_str()));
    let (names, by_full, ctors) = (HashMap::new(), HashMap::new(), HashMap::new());
    let (nullary, module_fns) = (HashSet::new(), HashSet::new());
    let errors = std::cell::RefCell::new(Vec::new());
    // A `pub` written before what declares nothing that it opens.
    for s in files.iter().flatten() {
        if !aliases_only
            && let Stmt::Other(what, span) = s
            && what.ends_with(NOT_A_DECLARATION)
        {
            errors
                .borrow_mut()
                .push((msg!("surface-pub-before-statement", what = what), *span));
        }
    }
    for (i, stmts) in files.iter().enumerate() {
        let r = Renamer {
            names: &names,
            by_full: &by_full,
            module_fns: &module_fns,
            ctors: &ctors,
            nullary: &nullary,
            args: &HashMap::new(),
            fields: &HashMap::new(),
            unseen: &nullary,
            locals: Default::default(),
            typed: Default::default(),
            returns: Default::default(),
            errors: &errors,
            sealed: None,
            seen: Some((&seen, i)),
            missing: None,
            declares: None,
            prelude_files: None,
            keep_prelude: false,
            used: None,
            quoting: Default::default(),
        };
        // The walk renames nothing with empty tables; it runs on a copy so
        // that it only reads.
        for s in stmts.clone().iter_mut() {
            r.top(s);
        }
    }
    errors.into_inner()
}

/// The names the statements of a file declare without `pub`, as
/// [`files`] keys them: what is inside a type is seen as far as the type.
fn private_names(stmts: &[Stmt]) -> HashSet<String> {
    let mut seen = Seen {
        names: HashMap::new(),
        ctors: HashMap::new(),
        effects: HashMap::new(),
        classes: HashMap::new(),
        fields: HashMap::new(),
        modules: Vec::new(),
    };
    stmts.iter().for_each(|s| seen.add(s, 0));
    let names = seen.names.into_iter().map(|(n, (_, v))| (n, v));
    let ctors = seen.ctors.into_iter().map(|(n, (_, v, _))| (n, v));
    names
        .chain(ctors)
        .filter(|(_, v)| *v == Vis::Private)
        .map(|(n, _)| n)
        .collect()
}

fn pattern_names(stmts: &[Stmt]) -> HashSet<String> {
    fn of(p: &Pattern, out: &mut HashSet<String>) {
        match p {
            Pattern::Bind(n) => {
                out.insert(n.to_string());
            }
            Pattern::Ctor { args, .. } => args.iter().for_each(|a| of(a, out)),
            Pattern::Record { fields, .. } => fields.iter().for_each(|(_, a)| of(a, out)),
            Pattern::Tuple(items) => items.iter().for_each(|a| of(a, out)),
            _ => {}
        }
    }
    let mut out = HashSet::new();
    for s in stmts {
        let mut s = s.clone();
        super::walk::stmt(&mut s, &mut |t| match &*t.kind {
            TermKind::Match { arms, .. } => arms.iter().for_each(|a| of(&a.pattern, &mut out)),
            TermKind::Handle { handlers, .. } => {
                for h in handlers {
                    match h {
                        Handler::Return { pattern, .. } => of(pattern, &mut out),
                        Handler::Operation { patterns, .. } => {
                            patterns.iter().for_each(|p| of(p, &mut out))
                        }
                    }
                }
            }
            _ => {}
        });
    }
    out
}

fn var_names(stmts: &[Stmt]) -> HashSet<String> {
    let mut out = HashSet::new();
    for s in stmts {
        let mut s = s.clone();
        super::walk::stmt(&mut s, &mut |t| {
            if let TermKind::Var(n) = &*t.kind {
                out.insert(n.to_string());
            }
        });
    }
    out
}

fn has_full_name(files: &[Vec<Stmt>], modules: &[String]) -> bool {
    let mut found = false;
    for stmts in files {
        for s in stmts {
            let mut s = s.clone();
            super::walk::stmt(&mut s, &mut |t| {
                if let TermKind::Var(n) = &*t.kind
                    && (is_full(n, modules)
                        || (n.contains(SEPARATOR) && n.starts_with(char::is_uppercase)))
                {
                    found = true;
                }
                // `Type::Ctor` written with `.`, which the reader reports.
                if let TermKind::Field { base, .. } = &*t.kind {
                    let mut root = base;
                    while let TermKind::Field { base, .. } = &*root.kind {
                        root = base;
                    }
                    if let TermKind::Var(n) = &*root.kind
                        && n.starts_with(char::is_uppercase)
                    {
                        found = true;
                    }
                }
            });
        }
    }
    found
}

/// The names the statements bind as a bare pattern (`Bind`), read from
/// their text: a name it finds that is not bound there only names a
/// constructor apart, which changes nothing a name means.
fn pattern_binders(stmts: &[Stmt]) -> HashSet<String> {
    let text = format!("{stmts:?}");
    text.split("Bind(\"")
        .skip(1)
        .filter_map(|rest| rest.split_once('"').map(|(n, _)| n.to_string()))
        .collect()
}

/// The constructors a top-level statement declares that have fields: a
/// bare name in a pattern is never one of them.
fn ctors_with_fields(s: &Stmt, out: &mut HashSet<String>) {
    match s {
        Stmt::Struct(d) | Stmt::Enum(d) => out.extend(
            d.constructors
                .iter()
                .filter(|c| !c.fields.is_empty())
                .map(|c| c.name.to_string()),
        ),
        Stmt::Inductive(d) => out.extend(
            d.constructors
                .iter()
                .filter(|c| c.params.len() > c.implicit)
                .map(|c| c.name.to_string()),
        ),
        Stmt::Mutual { items, .. } => items.iter().for_each(|i| ctors_with_fields(i, out)),
        Stmt::Attributed { stmt, .. } => ctors_with_fields(stmt, out),
        _ => {}
    }
}

/// A name the file does not see that one file declares: `import spelling` in the
/// file `file` makes it seen. `at` is where the name is written.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MissingImport {
    pub file: usize,
    pub at: Span,
    pub spelling: String,
}

enum Meaning {
    To(String),
    Ambiguous(Vec<String>),
    /// Declared by this file of the standard library only, which the file
    /// does not import, with how the file imports it (`std::Os`,
    /// `"Setoid.taut"`, `algebra::proof::Setoid`).
    /// Whether one file declares it, so that one import makes it seen.
    NotImported(String, String, bool),
}

struct Renamer<'a> {
    /// What the source spellings in this file mean.
    names: &'a HashMap<String, Meaning>,
    by_full: &'a HashMap<String, String>,
    /// The functions of the modules of the program, by their full names
    /// (`Bytes::values`): a module's name is not a type's, even where a type
    /// has that name and is renamed.
    module_fns: &'a HashSet<String>,
    ctors: &'a HashMap<String, HashMap<String, String>>,
    nullary: &'a HashSet<String>,
    /// The type each explicit argument of a function or constructor is
    /// written with (its head, named as after this pass), by the name the
    /// function or constructor is called: a constructor written there by its
    /// short name is read as that type's.
    args: &'a HashMap<String, Vec<Option<String>>>,
    /// The names this file binds in a pattern though another file, which
    /// it does not import, declares them.
    unseen: &'a HashSet<String>,
    /// The type of each field of a constructor, by the name it is called:
    /// a pattern variable in a field of a matched value of a known type has
    /// the field's type.
    fields: &'a HashMap<String, Vec<Option<Shape>>>,
    locals: std::cell::RefCell<Vec<(String, Option<Shape>)>>,
    /// The pattern variables of the arm being read whose type the matched
    /// value's type gives.
    typed: std::cell::RefCell<Vec<(String, Shape)>>,
    errors: &'a std::cell::RefCell<Vec<(Message, Span)>>,
    sealed: Option<(&'a HashMap<String, String>, Option<&'a str>)>,
    seen: Option<(&'a Seen, usize)>,
    /// Where the names one import would make seen are written, and the file being read.
    missing: Option<(&'a std::cell::RefCell<Vec<MissingImport>>, usize)>,
    returns: std::cell::RefCell<Option<String>>,
    /// The full names the file's own declarations take, by their short
    /// names; `None` where this walk renames no declaration.
    declares: Option<&'a HashMap<String, String>>,
    /// The prelude file (`std::prelude::Par`) the file imports that makes a
    /// name ambiguous with the file's own or imported declaration of it.
    prelude_files: Option<&'a HashMap<String, String>>,
    /// Whether a full name of the prelude is kept as written
    /// (`files_before_macros`).
    keep_prelude: bool,
    /// Where the global names this file writes itself are kept, as read,
    /// when its import lists are checked ([`check_import_lists`]).
    used: Option<&'a std::cell::RefCell<Vec<SourceUse>>>,
    /// How many quotes the name being read is in.
    quoting: std::cell::Cell<u32>,
}

impl Renamer<'_> {
    /// Records a name this file's scope binds: what removing the import would leave
    /// unbound. The pass before expansion reads what the file writes; the pass after it
    /// reads what is still unbound then, the names the file wrote in a literal that a
    /// macro put into its output. A name a macro made is bound in the macro definition's
    /// scope when it is made, so neither pass reads it.
    fn record(&self, n: &str, span: Span) {
        if let Some(used) = self.used {
            // A source constructor may acquire its owner's qualified display
            // when it is bound. Keep its source path before that happens.
            let mut paths = self
                .by_full
                .iter()
                .filter(|(full, target)| target.as_str() == n && !full.starts_with(PRELUDE_MODULE));
            let path = match (paths.next(), paths.next()) {
                (Some((full, _)), None) => full.as_str(),
                _ => n,
            };
            used.borrow_mut().push(SourceUse {
                path: path.to_string(),
                written: n.to_string(),
                span,
                keeps_only: false,
            });
        }
    }

    /// Keeps the names the laws of a class or an instance write, for the import lists: the laws
    /// are read by their own pass, so this reads a copy and keeps nothing else of it.
    fn record_laws(&self, laws: &[super::program::LawDecl]) {
        if self.used.is_none() || laws.is_empty() {
            return;
        }
        let errors = self.errors.borrow().len();
        let missing = self.missing.map(|(m, _)| m.borrow().len());
        for l in laws {
            let mut d = l.theorem.clone();
            self.scoped(|| {
                for (n, t) in &mut d.params {
                    self.term(t);
                    self.bind_typed(n, t);
                }
                self.term(&mut d.ty);
                if let Some(b) = &mut d.body {
                    self.term(b);
                }
            });
        }
        self.errors.borrow_mut().truncate(errors);
        if let (Some((m, _)), Some(n)) = (self.missing, missing) {
            m.borrow_mut().truncate(n);
        }
    }

    /// Keeps the name of a macro or a syntax the file calls, read before the macros run.
    fn record_call(&self, n: &str, span: Span) {
        if let Some(used) = self.used
            && self.keep_prelude
        {
            used.borrow_mut().push(SourceUse {
                path: format!("{CALLED}{n}"),
                written: n.to_string(),
                span,
                keeps_only: false,
            });
        }
    }

    fn scoped(&self, f: impl FnOnce()) {
        let depth = self.locals.borrow().len();
        f();
        self.locals.borrow_mut().truncate(depth);
    }

    fn bind<'b, N: AsRef<str> + 'b>(&self, names: impl IntoIterator<Item = &'b N>) {
        self.locals
            .borrow_mut()
            .extend(names.into_iter().map(|n| (n.as_ref().to_string(), None)));
    }

    /// The type a written type term names, read already: its head, unless
    /// that is a local (a generic `T`), which names no type here.
    fn type_named(&self, ty: &SurfaceTerm) -> Option<String> {
        // A type under a module is written `m.T`.
        fn head(t: &SurfaceTerm) -> Option<String> {
            match &*t.kind {
                TermKind::Var(h) => Some(h.to_string()),
                TermKind::Field { base, name } => Some(format!("{}{SEPARATOR}{name}", head(base)?)),
                _ => None,
            }
        }
        let head = match &*ty.kind {
            TermKind::App { function, .. } => head(function)?,
            _ => head(ty)?,
        };
        (!self.is_local(&head)).then_some(head)
    }

    /// Whether the type `ty` (`m.T`) is declared by nothing this pass sees: it is made by a
    /// `syntax!` whose types are declared once the macros run.
    fn pending_module_type(&self, ty: &str) -> bool {
        !self.by_full.contains_key(ty)
    }

    /// The constructor of the type `ty` (named as after this pass) whose
    /// short name is `n`, as it is called after this pass.
    fn ctor_of(&self, ty: &str, n: &str) -> Option<&String> {
        self.ctors.get(ty)?.get(n)
    }

    /// What a bare name written where a value of the type `ty` is wanted
    /// means, when that is not what it means elsewhere: the constructor of
    /// `ty` of that name, where the name is otherwise ambiguous or a
    /// constructor of another type, either of which the kernel would reject
    /// there. A name that means a function keeps meaning it.
    fn ctor_wanted(&self, ty: &str, n: &str) -> Option<String> {
        if n.contains(SEPARATOR) || self.is_local(n) {
            return None;
        }
        let c = self.ctor_of(ty, n)?;
        let means = match self.names.get(n) {
            Some(Meaning::Ambiguous(_)) => return Some(c.clone()),
            Some(Meaning::To(to)) => to.as_str(),
            Some(Meaning::NotImported(..)) | None => n,
        };
        let other_ctor = means != c
            && self
                .ctors
                .values()
                .any(|cs| cs.values().any(|v| v == means));
        other_ctor.then(|| c.clone())
    }

    /// What a bare name written where a type (`Prop`, `Type`) is wanted
    /// means, when this file declares it as a constructor and the prelude as
    /// a type: the prelude's. A constructor's value is never a type, so the
    /// kernel would reject the constructor there (`False` of an `enum Token
    /// { True, False }` in a proposition).
    fn sort_wanted(&self, ty: &str, n: &str) -> Option<super::Name> {
        if !matches!(ty, "Prop" | "Type") || n.contains(SEPARATOR) || self.is_local(n) {
            return None;
        }
        let Some(Meaning::To(means)) = self.names.get(n) else {
            return None;
        };
        // A native struct names its type as well as its value constructor.
        // In type position its own family takes precedence over the prelude.
        if self.ctors.contains_key(means) {
            return None;
        }
        let is_ctor = self
            .ctors
            .values()
            .any(|cs| cs.values().any(|v| v == means));
        if !is_ctor {
            return None;
        }
        let full = format!("{PRELUDE_MODULE}{SEPARATOR}{n}");
        self.by_full.get(&full)?;
        crate::bindings::library_bindings()
            .get(&full)
            .cloned()
            .map(super::Name::Global)
    }

    fn bind_typed(&self, name: &str, ty: &SurfaceTerm) {
        let shape = self.shape_named(ty);
        self.locals.borrow_mut().push((name.to_string(), shape));
    }

    /// A written type term, read already, as a type over its arguments.
    fn shape_named(&self, ty: &SurfaceTerm) -> Option<Shape> {
        let head = self.type_named(ty)?;
        let args = match &*ty.kind {
            TermKind::App { arguments, .. } => {
                arguments.iter().map(|a| self.shape_named(a)).collect()
            }
            _ => Vec::new(),
        };
        Some(Shape::Named(head, args))
    }

    /// The pattern variables of the arm just read are bound with the types
    /// the matched value's type gives their fields.
    fn bind_pattern_types(&self) {
        let typed = std::mem::take(&mut *self.typed.borrow_mut());
        let mut locals = self.locals.borrow_mut();
        for (n, shape) in typed {
            if let Some(l) = locals.iter_mut().rev().find(|(l, _)| *l == n) {
                l.1 = Some(shape);
            }
        }
    }

    fn is_local(&self, n: &str) -> bool {
        self.locals.borrow().iter().any(|(l, _)| l == n)
    }

    fn type_of(&self, scrutinee: &SurfaceTerm) -> Option<Shape> {
        let TermKind::Var(n) = &*scrutinee.kind else {
            return None;
        };
        let locals = self.locals.borrow();
        locals
            .iter()
            .rev()
            .find(|(l, _)| n.spelling() == Some(l.as_str()))?
            .1
            .clone()
    }

    fn effect(&self, n: &mut String, span: Span) {
        // `res(Pos)`: the effect, and each type its arguments name.
        if let Some((head, args)) = n.split_once('(') {
            let mut head = head.to_string();
            self.effect(&mut head, span);
            let mut out = head;
            out.push('(');
            let mut word = String::new();
            for c in args.chars() {
                if c.is_alphanumeric() || c == '_' || c == ':' {
                    word.push(c);
                    continue;
                }
                if !word.is_empty() {
                    self.name(&mut word, span);
                    out.push_str(&std::mem::take(&mut word));
                }
                out.push(c);
            }
            out.push_str(&word);
            *n = out;
            return;
        }
        if self.is_local(n) {
            return;
        }
        self.see(&format!("{EFFECT}{n}"), span);
        let mut key = format!("{EFFECT}{n}");
        if n.contains(SEPARATOR) {
            self.meaning(&mut key, span);
            self.record(&key, span);
            if let Some(to) = self.by_full.get(&key) {
                *n = to.clone();
            }
            return;
        }
        self.meaning(&mut key, span);
        self.record(&key, span);
        *n = bare(&key).to_string();
    }

    fn global(&self, n: &mut String, span: Span) {
        self.global_here(n, span);
        self.record(n, span);
    }

    fn global_here(&self, n: &mut String, span: Span) {
        self.see(n, span);
        if self.keep_prelude
            && n.strip_prefix(PRELUDE_MODULE)
                .is_some_and(|r| r.starts_with(SEPARATOR))
        {
            return;
        }
        if n.contains(SEPARATOR) {
            if let Some(to) = self.by_full.get(n.as_str()) {
                *n = to.clone();
                return;
            }
            if let Some((ty, ctor)) = n.rsplit_once(SEPARATOR) {
                // `T::C`, a constructor of the type `T`, written as the
                // constructor's name after this pass when that is not `C`
                // of the type named `T`.
                let mut to = ty.to_string();
                self.global(&mut to, span);
                if let Some(c) = self.ctors.get(&to).and_then(|cs| cs.get(ctor)) {
                    if to != ty || c != ctor {
                        *n = c.clone();
                    }
                    return;
                }
                if to != ty && !self.module_fns.contains(n.as_str()) {
                    *n = format!("{to}{SEPARATOR}{ctor}");
                    return;
                }
            }
        }
        self.meaning(n, span);
    }

    /// Whether `all`, full names, are constructors of types of one file
    /// (`m.A.Start`, `m.B.Start`): written with its type, `A::Start`, the
    /// name says which.
    fn ctors_of_one_file(&self, all: &[String]) -> bool {
        let module = |f: &str| {
            let mut parts = f.rsplitn(3, SEPARATOR);
            let (_, _, m) = (parts.next()?, parts.next()?, parts.next()?);
            Some(m.to_string())
        };
        let is_ctor = |f: &String| self.ctors.values().any(|cs| cs.values().any(|v| v == f));
        let Some(first) = all.first().and_then(|f| module(f)) else {
            return false;
        };
        all.len() > 1
            && all
                .iter()
                .all(|f| is_ctor(f) && module(f).as_deref() == Some(first.as_str()))
    }

    fn meaning(&self, n: &mut String, span: Span) {
        let names = self.names;
        match names.get(n.as_str()) {
            Some(Meaning::To(to)) => *n = to.clone(),
            Some(Meaning::Ambiguous(all)) => {
                let message = if self.ctors_of_one_file(all) {
                    // Constructors of several types of one file: the type
                    // says which.
                    msg!(
                        "surface-ambiguous-constructor",
                        name = bare(n),
                        names = names_and(all)
                    )
                } else if let Some(module) = self.prelude_files.and_then(|p| p.get(n.as_str())) {
                    // The file imports both: importing the other file again
                    // does not say which, but bringing only what the file
                    // uses from the prelude file does.
                    msg!(
                        "surface-ambiguous-imported-prelude",
                        name = bare(n),
                        names = names_and(all),
                        module = module
                    )
                } else if all.iter().any(|a| a.starts_with(PRELUDE_MODULE)) {
                    msg!(
                        "surface-ambiguous-prelude",
                        name = bare(n),
                        names = names_and(all)
                    )
                } else {
                    msg!("surface-ambiguous", name = bare(n), names = names_and(all))
                };
                self.errors.borrow_mut().push((message, span));
            }
            Some(Meaning::NotImported(module, spelling, one)) => {
                self.errors.borrow_mut().push((
                format!(
                    "`{}` is declared by `{module}`, which this file does not import (what another file or a dependency imports does not reach this one); `import {spelling}` in this file",
                    bare(n),
                    module = written(module),
                    spelling = spelling
                ).into(),
                span,
                ));
                if let (true, Some((missing, file))) = (*one, self.missing) {
                    missing.borrow_mut().push(MissingImport {
                        file,
                        at: span,
                        spelling: spelling.clone(),
                    });
                }
            }
            None => {}
        }
    }

    fn see(&self, n: &str, span: Span) {
        let Some((seen, here)) = self.seen else {
            return;
        };
        if let Some(&(file, Vis::Private)) = seen.names.get(n)
            && file != here
        {
            self.errors.borrow_mut().push((
                msg!("surface-private", name = short(n), file = seen.file(file)),
                span,
            ));
        }
    }

    /// `sealed_visibility`: a constructor `n` of the type `ty`, built or
    /// matched outside the file that declares the type, which shows its
    /// constructors only with `pub(open)`.
    fn see_inside(&self, file: usize, vis: Vis, here: usize, n: &str, ty: &str, span: Span) {
        let Some((seen, _)) = self.seen else {
            return;
        };
        if file == here || vis == Vis::Open {
            return;
        }
        self.errors.borrow_mut().push((
            msg!(
                "surface-sealed-constructor",
                name = short(n),
                ty = short(ty),
                file = seen.file(file)
            ),
            span,
        ));
    }

    /// An arm written as a name alone that binds, though a constructor
    /// the program reads has that name: the file does not see the
    /// constructor (no file it imports declares it), so the arm would take
    /// every value where the constructor was meant, and the arms after it
    /// would never be reached. Rejected (Safe by Default): the file imports
    /// the constructor's file to match it, or names its variable apart.
    fn binds_a_ctor_name(&self, n: &str, span: Span) {
        // The prelude's constructors are seen everywhere.
        if !self.unseen.contains(n) || prelude_ctors().values().any(|cs| cs.contains_key(n)) {
            return;
        }
        // Only a constructor without fields (a bare name is never one with
        // them) named apart, by its full name, for a file that does not see
        // it: one that keeps its short name is the constructor the pattern
        // matches.
        let mut types: Vec<&str> = self
            .ctors
            .iter()
            .filter(|(_, cs)| {
                cs.get(n)
                    .is_some_and(|c| c.contains(SEPARATOR) && self.nullary.contains(c))
            })
            .map(|(ty, _)| short(ty))
            .collect();
        if types.is_empty() {
            return;
        }
        types.sort_unstable();
        types.dedup();
        let of = types
            .iter()
            .map(|t| format!("`{t}`"))
            .collect::<Vec<_>>()
            .join(" and ");
        let mut cs = n.chars();
        let binder = cs.next().map_or(String::new(), |c| {
            c.to_lowercase().chain(cs).collect::<String>() + "_"
        });
        self.errors.borrow_mut().push((
            format!(
                "`{n}` alone in this pattern binds a new variable, which matches every value, but `{n}` is a constructor of {of}, which this file does not import: import the file that declares it to match the constructor, or to bind the value write a name that is not a constructor, like `{binder}`"
            ).into(),
            span,
        ));
    }

    fn see_ctor(&self, n: &str, span: Span) {
        if let Some((seen, here)) = self.seen
            && let Some((file, vis, ty)) = seen.ctors.get(n)
        {
            self.see_inside(*file, *vis, here, n, ty, span);
        }
    }

    /// `sealed_visibility`: `x.f` where only types another file keeps
    /// abstract have a field `f`.
    fn see_field(&self, base: &SurfaceTerm, f: &str, span: Span) {
        let Some((seen, here)) = self.seen else {
            return;
        };
        // `C::member` of a class names a member, not a field.
        if let TermKind::Var(b) = &*base.kind
            && !self.is_local(b)
        {
            return;
        }
        let Some(owners) = seen.fields.get(f) else {
            return;
        };
        if owners
            .iter()
            .any(|&(file, vis, _)| file == here || vis == Vis::Open)
        {
            return;
        }
        let (file, _, ty) = owners[0].clone();
        self.errors.borrow_mut().push((
            msg!(
                "surface-sealed-field",
                field = f,
                ty = short(&ty),
                file = seen.file(file)
            ),
            span,
        ));
    }

    /// `sealed_visibility`: an arm for the operation `op` outside the file
    /// that declares it, which lets other files answer it only with
    /// `pub(open)`.
    fn see_arm(&self, op: &str, span: Span) {
        let Some((seen, here)) = self.seen else {
            return;
        };
        if let Some(&(file, vis)) = seen.effects.get(op)
            && file != here
            && vis != Vis::Open
        {
            self.errors.borrow_mut().push((
                msg!(
                    "surface-sealed-effect",
                    name = short(op),
                    file = seen.file(file)
                ),
                span,
            ));
        }
    }

    /// `sealed_visibility`: an instance of the class `class` outside the
    /// file that declares it, which lets other files write instances only
    /// with `pub(open)`.
    fn see_instance(&self, class: &str, span: Span) {
        let Some((seen, here)) = self.seen else {
            return;
        };
        let Some(decls) = seen.classes.get(last_segment(class)) else {
            return;
        };
        if decls
            .iter()
            .any(|&(file, vis)| file == here || vis == Vis::Open)
        {
            return;
        }
        if let Some(&(file, Vis::Pub)) = decls.first() {
            self.errors.borrow_mut().push((
                msg!(
                    "surface-sealed-class",
                    name = short(class),
                    file = seen.file(file)
                ),
                span,
            ));
        }
    }

    /// `sealed_visibility`: a `pub` function whose `where` names a class
    /// its own file declares without `pub`, which no other file could meet.
    fn see_where(&self, f: &super::program::FnDecl) {
        let Some((seen, here)) = self.seen else {
            return;
        };
        if f.vis == Vis::Private {
            return;
        }
        for c in &f.where_ {
            let Some(decls) = seen.classes.get(last_segment(&c.class)) else {
                continue;
            };
            if decls
                .iter()
                .any(|&(file, vis)| file != here || vis != Vis::Private)
            {
                continue;
            }
            self.errors.borrow_mut().push((
                msg!(
                    "surface-private-class-bound",
                    name = short(&c.class),
                    function = short(&f.name)
                ),
                c.span,
            ));
        }
    }

    fn name(&self, n: &mut String, span: Span) {
        if let Some((owner, here)) = self.sealed
            && !self.is_local(n)
            && let Some(tote) = owner.get(n.as_str())
            && here != Some(tote.as_str())
        {
            self.errors.borrow_mut().push((
                msg!("surface-sealed-extern", name = short(n), tote = tote),
                span,
            ));
        }
        if !self.is_local(n) {
            if let Some((seen, here)) = self.seen
                && let Some(&(file, vis, ref ty)) = seen.ctors.get(n.as_str())
                && *ty != *n
            {
                self.see_inside(file, vis, here, n, ty, span);
            }
            self.global(n, span);
        }
    }

    fn rename_decl(&self, n: &mut String) {
        if let Some(Meaning::To(to)) = self.names.get(n.as_str()) {
            *n = to.clone();
        } else if let Some(to) = self.declares.and_then(|d| d.get(n.as_str())) {
            // Ambiguous where it is written, the name is still the file's own
            // where it is declared.
            *n = to.clone();
        }
    }

    fn top(&self, s: &mut Stmt) {
        match s {
            Stmt::Fn(f) => (f.name).edit_spelling(|spelling| self.rename_decl(spelling)),
            Stmt::Extern { fns, .. } => fns
                .iter_mut()
                .for_each(|f| (f.name).edit_spelling(|spelling| self.rename_decl(spelling))),
            Stmt::Struct(d) | Stmt::Enum(d) => {
                let same: Vec<bool> = d.constructors.iter().map(|c| c.name == d.name).collect();
                (d.name).edit_spelling(|spelling| self.rename_decl(spelling));
                for (c, same) in d.constructors.iter_mut().zip(same) {
                    if c.name.is_resolved() {
                        continue;
                    }
                    if same {
                        c.name = d.name.clone();
                        continue;
                    }
                    // A name other types of the file share is this type's.
                    match self.names.get(c.name.as_str()) {
                        Some(Meaning::Ambiguous(_)) => {
                            if let Some(to) = self.ctor_of(&d.name, &c.name) {
                                c.name = crate::identity::Name::Spelled(to.clone());
                            }
                        }
                        _ => (c.name).edit_spelling(|spelling| self.rename_decl(spelling)),
                    }
                }
            }
            Stmt::Effect(e) => {
                e.name.edit_spelling(|name| {
                    let mut key = format!("{EFFECT}{name}");
                    self.rename_decl(&mut key);
                    *name = bare(&key).to_string();
                });
            }
            Stmt::Inductive(d) => {
                (d.name).edit_spelling(|spelling| self.rename_decl(spelling));
                for c in d.constructors.iter_mut() {
                    if c.name.is_resolved() {
                        continue;
                    }
                    // A name other types of the file share is this type's.
                    match self.names.get(c.name.as_str()) {
                        Some(Meaning::Ambiguous(_)) => {
                            if let Some(to) = self.ctor_of(&d.name, &c.name) {
                                c.name = crate::identity::Name::Spelled(to.clone());
                            }
                        }
                        _ => (c.name).edit_spelling(|spelling| self.rename_decl(spelling)),
                    }
                }
                // The list after the sort names what is made for the type, so
                // it is renamed with the type.
                d.generates
                    .items
                    .iter_mut()
                    .for_each(|(_, n)| self.rename_decl(n));
            }
            Stmt::Theorem(d) | Stmt::Def(d) => {
                (d.name).edit_spelling(|spelling| self.rename_decl(spelling))
            }
            Stmt::Class(c) => (c.name).edit_spelling(|spelling| self.rename_decl(spelling)),
            Stmt::Let { name, .. } | Stmt::Var { name, .. } => {
                name.edit_spelling(|spelling| self.rename_decl(spelling))
            }
            Stmt::Mutual { items, .. } => items.iter_mut().for_each(|i| self.top(i)),
            Stmt::Attributed { stmt, .. } => self.top(stmt),
            // The function of `macro fn` is the one declared beside it, under
            // whatever name that declaration takes (`nat`, named apart from
            // the builtin type); the macro keeps the name it is called by.
            Stmt::Macro { function, .. } => self.rename_decl(function),
            _ => {}
        }
        self.stmt(s);
    }

    fn stmt(&self, s: &mut Stmt) {
        match s {
            Stmt::Let {
                name, ty, value, ..
            }
            | Stmt::Var {
                name, ty, value, ..
            } => {
                if let Some(t) = ty {
                    self.term(t);
                }
                let of = ty.as_ref().and_then(|t| self.type_named(t));
                self.term_of(value, of.as_deref());
                match ty {
                    Some(t) => self.bind_typed(name, t),
                    None => self.bind([&*name]),
                }
            }
            Stmt::Fn(f) => {
                self.see_where(f);
                self.scoped(|| self.function(f))
            }
            Stmt::Extern { fns, .. } => {
                for f in fns {
                    self.scoped(|| self.function(f));
                }
            }
            Stmt::Theorem(d) | Stmt::Def(d) => self.scoped(|| {
                for (n, t) in &mut d.params {
                    self.term(t);
                    self.bind_typed(n, t);
                }
                self.term(&mut d.ty);
                if let Some(b) = &mut d.body {
                    self.term(b);
                }
            }),
            Stmt::Struct(d) | Stmt::Enum(d) => self.scoped(|| {
                self.bind(&d.generics);
                for c in &mut d.constructors {
                    for (_, t) in &mut c.fields {
                        self.term(t);
                    }
                }
            }),
            Stmt::Effect(e) => self.scoped(|| {
                self.bind(&e.generics);
                for t in e.params.iter_mut().flatten() {
                    self.term(t);
                }
                if let Some(r) = &mut e.result {
                    self.term(r);
                }
                if let Some(set) = &mut e.set {
                    set.iter_mut().for_each(|n| self.effect(n, e.span));
                }
            }),
            Stmt::Inductive(d) => self.scoped(|| {
                for (n, t) in &mut d.params {
                    self.term(t);
                    self.bind([&*n]);
                }
                self.term(&mut d.sort);
                for c in &mut d.constructors {
                    self.scoped(|| {
                        for (n, t) in &mut c.params {
                            self.term(t);
                            self.bind([&*n]);
                        }
                        self.term(&mut c.result);
                    });
                }
            }),
            Stmt::Class(c) => self.scoped(|| {
                for (name, ty) in &mut c.parameters {
                    self.term(ty);
                    self.bind([&*name]);
                }
                for m in &mut c.methods {
                    self.scoped(|| self.function(m));
                }
                self.record_laws(&c.laws);
            }),
            Stmt::Instance(inst) => self.scoped(|| {
                self.see_instance(short(&inst.class), inst.span);
                (inst.class).edit_spelling(|spelling| self.global(spelling, inst.span));
                for (index, name) in inst.generics.iter().enumerate() {
                    if let Some(ty) = inst.generic_types.get_mut(index) {
                        self.term(ty);
                    }
                    self.bind([name]);
                }
                self.term(&mut inst.head);
                for arg in &mut inst.arguments {
                    self.term(arg);
                }
                for c in &mut inst.where_ {
                    (c.class).edit_spelling(|spelling| self.global(spelling, c.span));
                    self.term(&mut c.ty);
                    for arg in &mut c.arguments {
                        self.term(arg);
                    }
                }
                for m in &mut inst.methods {
                    self.scoped(|| self.function(m));
                }
                self.record_laws(&inst.laws);
            }),
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                items.iter_mut().for_each(|i| self.stmt(i))
            }
            Stmt::Attributed {
                name,
                arg,
                stmt,
                span,
                ..
            } => {
                self.record_call(name, *span);
                self.term(arg);
                self.stmt(stmt);
            }
            Stmt::Assign { value, place, .. } => {
                if self.seen.is_some()
                    && let Some(place) = place
                {
                    // The place is read for its fields only: its names are the binding's.
                    let mut at = &*place;
                    while let TermKind::Field { base, name } = &*at.kind {
                        self.see_field(base, name, at.span);
                        at = base;
                    }
                }
                self.term(value)
            }
            Stmt::While { condition, body } => {
                self.term(condition);
                self.term(body);
            }
            Stmt::Return(Some(e)) => {
                let of = self.returns.borrow().clone();
                self.term_of(e, of.as_deref());
            }
            Stmt::Expr(e) => self.term(e),
            Stmt::Called { call, .. } => self.term(call),
            // The function of a macro is named as any reference is: a
            // function `nat` beside the type `nat` is `m::nat` after this
            // pass, and so is the function its macro runs.
            Stmt::Macro { function, span, .. } => self.global(function, *span),
            Stmt::Return(None) | Stmt::Import { .. } | Stmt::Syntax { .. } | Stmt::Other(..) => {}
        }
    }

    fn function(&self, f: &mut super::program::FnDecl) {
        for (i, name) in f.generics.iter().enumerate() {
            if let Some(ty) = f.generic_types.get_mut(i) {
                self.term(ty);
                self.bind_typed(name, ty);
            } else {
                self.bind([name]);
            }
        }
        for c in &mut f.where_ {
            (c.class).edit_spelling(|spelling| self.global(spelling, c.span));
            self.term(&mut c.ty);
            for arg in &mut c.arguments {
                self.term(arg);
            }
        }
        // Each parameter is bound from the next one's type on: a later
        // parameter's type, and the result, may name it (`h: Eq(T, x, x)`).
        for (i, n) in f.params.iter().enumerate() {
            match f.param_types.get_mut(i).and_then(|t| t.as_mut()) {
                Some(t) => {
                    self.term(t);
                    self.bind_typed(n, t);
                }
                None => self.bind([n]),
            }
        }
        for t in f.param_types.iter_mut().skip(f.params.len()).flatten() {
            self.term(t);
        }
        if let Some(r) = &mut f.result {
            self.term(r);
        }
        if let Some(effects) = &mut f.effects {
            effects
                .iter_mut()
                .for_each(|e| e.edit_spelling(|spelling| self.effect(spelling, f.span)));
        }
        if let Some(d) = &mut f.decreasing_by {
            self.term(d);
        }
        let returns = f.result.as_ref().and_then(|r| self.type_named(r));
        let outer = self.returns.replace(returns.clone());
        self.term_of(&mut f.body, returns.as_deref());
        self.returns.replace(outer);
    }

    /// A pattern, `of` the type of the matched value when it is written: a
    /// constructor written by its short name is then that type's constructor
    /// of that name, whatever else declares the name, as the kernel accepts
    /// no other there.
    fn pattern(&self, p: &mut Pattern, span: Span, bound: &mut Vec<String>, of: Option<&Shape>) {
        let shape = of;
        let of = shape.and_then(Shape::head);
        // A constructor of a pending module type retains its owner's path
        // until expansion declares that type.
        if let Some(ty) = of
            && ty.contains(SEPARATOR)
            && !self.ctors.contains_key(ty)
            && let Pattern::Ctor { name: n, args } = &mut *p
            && !n.contains(SEPARATOR)
            && !n.starts_with('$')
            && self
                .names
                .get(n.as_str())
                .is_none_or(|m| !matches!(m, Meaning::NotImported(..)))
            && self.pending_module_type(ty)
        {
            n.edit_spelling(|spelling| *spelling = format!("{ty}{SEPARATOR}{spelling}"));
            args.iter_mut()
                .for_each(|a| self.pattern(a, span, bound, None));
            return;
        }
        if let Some(ty) = of
            && let Some(n) = (match &mut *p {
                Pattern::Ctor { name, .. } | Pattern::Record { name, .. } => name.spelling_mut(),
                _ => None,
            })
            && !n.contains(SEPARATOR)
        {
            if let Some(c) = self.ctor_of(ty, n) {
                *n = c.clone();
                self.record(c, span);
                // The type of each field, the matched type's arguments put for
                // the family's parameters.
                let fields: Vec<Option<Shape>> = match (self.fields.get(c), shape) {
                    (Some(fs), Some(Shape::Named(_, targs))) => fs
                        .iter()
                        .map(|f| f.as_ref().and_then(|f| f.instantiate(targs)))
                        .collect(),
                    _ => Vec::new(),
                };
                match p {
                    Pattern::Ctor { args, .. } => {
                        let args_len = args.len();
                        for (k, a) in args.iter_mut().enumerate() {
                            let field = (fields.len() == args_len)
                                .then(|| fields.get(k).and_then(Option::as_ref))
                                .flatten();
                            // A name alone in a field is read as without a type (it binds
                            // unless a constructor has it); a variable it binds has the
                            // field's type.
                            let before = bound.len();
                            match a {
                                Pattern::Bind(_) => self.pattern(a, span, bound, None),
                                _ => self.pattern(a, span, bound, field),
                            }
                            if let (Some(shape), Pattern::Bind(n)) = (field, &*a)
                                && bound[before..]
                                    .iter()
                                    .any(|b| n.spelling() == Some(b.as_str()))
                            {
                                self.typed.borrow_mut().push((n.to_string(), shape.clone()));
                            }
                        }
                    }
                    Pattern::Record { fields, .. } => fields
                        .iter_mut()
                        .for_each(|(_, a)| self.pattern(a, span, bound, None)),
                    _ => {}
                }
                return;
            }
            // A name declared more than once, none of them a constructor of
            // the matched type: say which type is matched.
            if self.ctors.contains_key(ty)
                && let Some(Meaning::Ambiguous(all)) = self.names.get(n.as_str())
            {
                self.errors.borrow_mut().push((
                    msg!(
                        "surface-not-a-constructor-of",
                        name = &*n,
                        ty = short(ty),
                        names = names_and(all)
                    ),
                    span,
                ));
                return;
            }
        }
        match p {
            // A bare name is a constructor when one has it; a name only a
            // function or a theorem has is bound here, whatever declares it.
            Pattern::Bind(n) => {
                if let Some(ty) = of
                    && self.ctors.contains_key(ty)
                    && self.ctor_of(ty, n).is_none()
                    && let Some(Meaning::Ambiguous(all)) = self.names.get(n.as_str())
                    && all.iter().all(|candidate| {
                        self.ctors
                            .values()
                            .any(|constructors| constructors.values().any(|name| name == candidate))
                    })
                {
                    self.errors.borrow_mut().push((
                        msg!(
                            "surface-not-a-constructor-of",
                            name = n.to_string(),
                            ty = short(ty),
                            names = names_and(all)
                        ),
                        span,
                    ));
                    return;
                }

                let visible_constructor = of.and_then(|ty| self.ctor_of(ty, n)).or_else(|| {
                    match self.names.get(n.as_str()) {
                        Some(Meaning::To(full)) => Some(full),
                        _ => None,
                    }
                });
                if let Some(constructor) = visible_constructor {
                    self.see_ctor(constructor, span);
                    if self
                        .ctors
                        .values()
                        .any(|constructors| constructors.values().any(|name| name == constructor))
                    {
                        self.record(constructor, span);
                    }
                }
                if n.contains(SEPARATOR) {
                    n.edit_spelling(|spelling| self.global(spelling, span));
                } else {
                    // A bare pattern's occurrences share its pending binding.
                    // The type checker decides between its constructor candidates
                    // and the local reference reserved for this occurrence.
                    bound.push(n.to_string());
                }
            }
            Pattern::Ctor { name, args } => {
                // `@a p`: a label, which names no declaration.
                let label = name.starts_with('@');
                if !label {
                    self.see_ctor(name, span);
                }
                // A name only constructors of several types share (`Mk`),
                // where the matched type is not written: the kernel reads it
                // as the matched type's constructor of that name.
                let is_ctor =
                    |f: &String| self.ctors.values().any(|cs| cs.values().any(|v| v == f));
                let shared = matches!(
                    self.names.get(name.as_str()),
                    Some(Meaning::Ambiguous(all)) if all.iter().all(is_ctor)
                );
                if !shared && !label {
                    (name).edit_spelling(|spelling| self.global(spelling, span));
                }
                args.iter_mut()
                    .for_each(|a| self.pattern(a, span, bound, None));
            }
            Pattern::Record { name, fields } => {
                // `C<n: m>(…)`: the record of the implicit arguments named has
                // an internal name, not a declaration's.
                if name.spelling() != Some(crate::IMPLICITS) {
                    self.see_ctor(name, span);
                    (name).edit_spelling(|spelling| self.global(spelling, span));
                }
                fields
                    .iter_mut()
                    .for_each(|(_, a)| self.pattern(a, span, bound, None));
            }
            Pattern::Tuple(items) => items
                .iter_mut()
                .for_each(|a| self.pattern(a, span, bound, None)),
            _ => {}
        }
    }

    fn term(&self, t: &mut SurfaceTerm) {
        self.term_of(t, None)
    }

    /// The full name `a.b.c` that the fields `a.b.c` write, when `a` is not
    /// bound here and the full name is a declaration or a type's constructor.
    fn full_name(&self, t: &SurfaceTerm) -> Option<String> {
        fn dotted<'t>(t: &'t SurfaceTerm, out: &mut Vec<&'t str>) -> bool {
            match &*t.kind {
                TermKind::Var(crate::identity::Name::Spelled(n)) => {
                    out.extend(n.split(SEPARATOR));
                    true
                }
                TermKind::Field { base, name } => {
                    let ok = dotted(base, out);
                    out.push(name);
                    ok
                }
                _ => false,
            }
        }
        if !is_path(t) {
            return None;
        }
        let mut parts = Vec::new();
        if !dotted(t, &mut parts) || self.is_local(parts[0]) {
            return None;
        }
        let full = parts.join(SEPARATOR);
        if self.by_full.contains_key(&full) {
            return Some(full);
        }
        // `module.Ctor`: the constructor of a type of that module, written
        // with the module as it is written alone (`Cut` of `other.more`).
        if let Some(c) = self.module_ctor(&full) {
            return Some(c);
        }
        // `Type::Ctor`: the type has that constructor. A class's method
        // `Ord::compare` is not one.
        let (ty, ctor) = full.rsplit_once(SEPARATOR)?;
        let mut to = ty.to_string();
        if let Some(Meaning::To(m)) = self.names.get(&to) {
            to = m.clone();
        } else if let Some(f) = self.by_full.get(&to) {
            to = f.clone();
        }
        let has = |t: &str| self.ctors.get(t).is_some_and(|cs| cs.contains_key(ctor));
        (has(&to) || has(ty)).then_some(full)
    }

    /// The full name of the constructor `full` names as `module.Ctor`, when
    /// one type of that module has a constructor of that name.
    fn module_ctor(&self, full: &str) -> Option<String> {
        let (module, ctor) = full.rsplit_once(SEPARATOR)?;
        if !with_known_modules(|known| known.contains(module)) {
            return None;
        }
        let mut found = self.by_full.iter().filter(|(k, _)| {
            k.strip_prefix(module)
                .and_then(|r| r.strip_prefix(SEPARATOR))
                .and_then(|r| r.strip_suffix(ctor))
                .and_then(|ty| ty.strip_suffix(SEPARATOR))
                .is_some_and(|ty| !ty.is_empty() && !ty.contains(SEPARATOR))
        });
        match (found.next(), found.next()) {
            (Some((k, _)), None) => Some(k.clone()),
            _ => None,
        }
    }

    /// Whether `t` is `M::f` naming the function `f` of the module `M`, which
    /// the flattening of the modules reads after this pass: `M` is left as
    /// written, though a type `M` is renamed.
    fn module_fn(&self, t: &SurfaceTerm) -> bool {
        fn dotted(t: &SurfaceTerm, out: &mut Vec<String>) -> bool {
            match &*t.kind {
                TermKind::Var(crate::identity::Name::Spelled(n)) => {
                    out.extend(n.split(SEPARATOR).map(str::to_string));
                    true
                }
                TermKind::Field { base, name } => {
                    let ok = dotted(base, out);
                    out.push(name.clone());
                    ok
                }
                _ => false,
            }
        }
        let mut parts = Vec::new();
        is_path(t) && dotted(t, &mut parts) && !self.is_local(&parts[0]) && {
            let full = parts.join(SEPARATOR);
            // The modules are flattened before this pass: `M::f` that a file
            // declares is a name like any other, read as it means here.
            !self.names.contains_key(&full)
                && (self.module_fns.contains(&full)
                    || self
                        .by_full
                        .contains_key(&format!("{PRELUDE_MODULE}{SEPARATOR}{full}")))
        }
    }

    /// A term, `of` the type wanted of its value when that is written: a
    /// constructor written there by its short name is then read as that
    /// type's (`ctor_wanted`).
    fn term_of(&self, t: &mut SurfaceTerm, of: Option<&str>) {
        self.term_here(t, of);
    }

    fn term_here(&self, t: &mut SurfaceTerm, of: Option<&str>) {
        if matches!(&*t.kind, TermKind::Var(n) if n.is_resolved()) {
            return;
        }
        let span = t.span;
        if let TermKind::Var(crate::identity::Name::Spelled(written)) = &*t.kind
            && let Some(reference) = crate::bindings::library_by_full_name(written).cloned()
        {
            let mut checked = written.clone();
            self.name(&mut checked, span);
            t.kind = Arc::new(TermKind::Var(crate::identity::Name::Global(reference)));
            return;
        }
        // `.` takes a field only: a declaration's name after it is written with `::`.
        // (A function of a module written `M::f` is reported where the modules are read.)
        if matches!(&*t.kind, TermKind::Field { .. })
            && !self.module_fn(t)
            && self.full_name(t).is_some()
        {
            self.errors.borrow_mut().push((
                msg!("surface-dot-names-a-declaration", name = dotted_text(t)),
                span,
            ));
        }
        if self.module_fn(t) {
            self.record(&dotted_text(t), span);
            return;
        }
        // A full name written with `::`: `std::Text::text`, `Shape::Circle`.
        if let Some(full) = self.full_name(t) {
            t.kind = Arc::new(TermKind::Var(crate::identity::Name::Spelled(full)));
        }
        match Arc::make_mut(&mut t.kind) {
            TermKind::Var(n) => match of.and_then(|ty| {
                self.ctor_wanted(ty, n)
                    .map(super::Name::from)
                    .or_else(|| self.sort_wanted(ty, n))
            }) {
                Some(c) => {
                    self.record(&c, span);
                    *n = c
                }
                None => n.edit_spelling(|spelling| self.name(spelling, span)),
            },
            TermKind::App {
                function,
                arguments,
            } if matches!(&*function.kind, TermKind::Var(_)) => {
                self.term_of(function, of);
                // Each argument is read with the type its parameter is written with.
                let wanted = match &*function.kind {
                    TermKind::Var(f) => self.args.get(f.as_str()).cloned(),
                    _ => None,
                };
                for (k, a) in arguments.iter_mut().enumerate() {
                    let ty = wanted.as_ref().and_then(|w| w.get(k).cloned().flatten());
                    self.term_of(a, ty.as_deref());
                }
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } if of.is_some() => {
                self.term(condition);
                self.term_of(then, of);
                if let Some(o) = otherwise {
                    self.term_of(o, of);
                }
            }
            TermKind::Block(stmts) if of.is_some() => self.scoped(|| {
                let last = stmts.len().saturating_sub(1);
                for (i, s) in stmts.iter_mut().enumerate() {
                    match s {
                        Stmt::Expr(e) if i == last => self.term_of(e, of),
                        _ => self.stmt(s),
                    }
                }
            }),
            TermKind::Record { name, fields, .. } if name.spelling() == Some(crate::IMPLICITS) => {
                fields.iter_mut().for_each(|(_, v)| self.term(v));
            }
            TermKind::Record { name, fields, base } => {
                (name).edit_spelling(|spelling| self.global(spelling, span));
                self.see_ctor(name, span);
                if let Some((seen, here)) = self.seen
                    && let Some((file, vis, family)) = seen.ctors.get(&format!("{name}::Mk"))
                    && family == name.as_str()
                {
                    self.see_inside(*file, *vis, here, name, family, span);
                }
                fields.iter_mut().for_each(|(_, v)| self.term(v));
                if let Some(b) = base {
                    self.term(b);
                }
            }
            TermKind::Perform { effect, args } => {
                (effect).edit_spelling(|spelling| self.effect(spelling, span));
                args.iter_mut().for_each(|a| self.term(a));
            }
            TermKind::Pi {
                params,
                result,
                effects,
            } => self.scoped(|| {
                for (n, p) in params {
                    self.term(p);
                    if let Some(n) = n {
                        self.bind([&*n]);
                    }
                }
                if let Some(effects) = effects {
                    effects
                        .iter_mut()
                        .for_each(|e| e.edit_spelling(|spelling| self.effect(spelling, span)));
                }
                self.term(result);
            }),
            TermKind::Exists {
                binder,
                domain,
                body,
            } => {
                self.term(domain);
                self.scoped(|| {
                    self.bind([&*binder]);
                    self.term(body);
                });
            }
            TermKind::Lam {
                params,
                body,
                types,
            } => self.scoped(|| {
                // The written types are read outside the parameters.
                types.iter_mut().flatten().for_each(|ty| self.term(ty));
                self.bind(params.iter());
                self.term(body);
            }),
            // A quote's statements bind as a block's do: its own `let tmp`
            // is a local of the quote, not a global `tmp` of another file.
            TermKind::Block(stmts) => self.scoped(|| stmts.iter_mut().for_each(|s| self.stmt(s))),
            TermKind::Quote { body: stmts, .. } => {
                self.quoting.set(self.quoting.get() + 1);
                self.scoped(|| stmts.iter_mut().for_each(|s| self.stmt(s)));
                self.quoting.set(self.quoting.get() - 1);
            }
            TermKind::Handle { body, handlers } => {
                self.term(body);
                for h in handlers {
                    self.scoped(|| match h {
                        Handler::Return { pattern, body } => {
                            let mut bound = Vec::new();
                            self.pattern(pattern, body.span, &mut bound, None);
                            self.bind(&bound);
                            self.term(body);
                        }
                        Handler::Operation {
                            effect,
                            instance,
                            patterns,
                            cont,
                            guard,
                            body,
                        } => {
                            self.see_arm(effect, body.span);
                            (effect).edit_spelling(|spelling| self.effect(spelling, body.span));
                            self.bind(&instance.forall);
                            instance.args.iter_mut().for_each(|a| self.term(a));
                            let mut bound = Vec::new();
                            for p in patterns {
                                self.pattern(p, body.span, &mut bound, None);
                            }
                            bound.extend(cont.iter().map(ToString::to_string));
                            self.bind(&bound);
                            if let Some(g) = guard {
                                self.term(g);
                            }
                            self.term(body);
                        }
                    });
                }
            }
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } => {
                self.term(scrutinee);
                let wanted = of;
                let of = self.type_of(scrutinee);
                let mut wanted = wanted.map(str::to_string);
                if let Some(r) = result {
                    self.scoped(|| {
                        self.bind(binder.iter());
                        self.term(r);
                        wanted = self.type_named(r);
                    });
                }
                for a in arms {
                    self.scoped(|| {
                        let mut bound = Vec::new();
                        self.typed.borrow_mut().clear();
                        self.pattern(&mut a.pattern, a.body.span, &mut bound, of.as_ref());
                        // An arm that is a name alone, where the matched
                        // value's type is not known here (the type, when it
                        // is, says what the name is); a name in a field
                        // binds, whatever another file's constructors are
                        // called.
                        if of.is_none()
                            && let Pattern::Bind(n) = &a.pattern
                            && bound.iter().any(|b| b == n.as_str())
                        {
                            self.binds_a_ctor_name(n, a.body.span);
                        }
                        bound.extend(binder.iter().map(ToString::to_string));
                        self.bind(&bound);
                        self.bind_pattern_types();
                        if let Some(g) = &mut a.guard {
                            self.term(g);
                        }
                        if let Some(g) = &mut a.goal {
                            self.term(g);
                        }
                        self.term_of(&mut a.body, wanted.as_deref());
                    });
                }
            }
            TermKind::Step(s) => {
                self.record_call(&s.tactic, s.call);
                self.term(&mut s.arg);
                if let Some(b) = &mut s.before {
                    self.term(b);
                }
                for a in &mut s.arms {
                    self.scoped(|| {
                        for (n, ty) in &mut a.binders {
                            self.term(ty);
                            self.bind([&*n]);
                        }
                        self.term(&mut a.goal);
                        self.term(&mut a.body);
                    });
                }
            }
            TermKind::Field { base, name } => {
                self.see_field(base, name, span);
                // `M::f` over a name not bound here names a function of the
                // module `M` (`Bytes::values`), which the modules resolve: the
                // name is no type's to rename (`std::Bytes::Bytes`).
                if !matches!(&*base.kind, TermKind::Var(b) if !self.is_local(b)) {
                    self.term(base);
                }
            }
            TermKind::MacroCall { name, arg } => {
                self.record_call(name, span);
                self.term(arg);
            }
            _ => super::walk::children(t, &mut |c| self.term(c)),
        }
    }
}

fn is_path(t: &SurfaceTerm) -> bool {
    match &*t.kind {
        TermKind::Var(n) => n.spelling().is_some_and(|s| s.contains(SEPARATOR)),
        TermKind::Field { .. } => true,
        _ => false,
    }
}

/// Fields over a name, written with `::` as the name of a declaration is (`M::f` of `M::f`).
fn dotted_text(t: &SurfaceTerm) -> String {
    match &*t.kind {
        TermKind::Var(n) => n.to_string(),
        TermKind::Field { base, name } => format!("{}{SEPARATOR}{name}", dotted_text(base)),
        _ => String::new(),
    }
}

fn names_and(all: &[String]) -> Message {
    let mut names = all
        .iter()
        .map(|a| Message::text(format!("`{}`", written(a))));
    let first = names.next().unwrap_or_else(|| Message::text(""));
    names.fold(first, |before, name| {
        msg!("surface-names-and", before = before, name = name)
    })
}

/// The members of the product type of `items`, in the order written: a member `Unit` is a
/// member as any other, so `A × Unit` is not `A`. A member that is itself a product stays one member, so
/// `(A × B) × C` is not `A × B × C`: it is what `T × C` is at `T := A × B`. A `Pair(A, B)` written by its name is the inductive
/// type `Pair`, one member: `Pair(A, B) × C` has the two members `Pair(A, B)` and `C`.
pub fn product_type_members(items: &[SurfaceTerm]) -> Vec<SurfaceTerm> {
    fn go(t: &SurfaceTerm, out: &mut Vec<SurfaceTerm>) {
        match &*t.kind {
            _ => out.push(t.clone()),
        }
    }
    let mut out = Vec::new();
    items.iter().for_each(|i| go(i, &mut out));
    out
}

/// `#(…)` with its members put as its type's. Every member, `#()` too, stays one member in the
/// order written, so a `#(…)` is already as its type puts it: `None`, nothing changes.
pub fn flatten_pair_value(_t: &SurfaceTerm) -> Option<SurfaceTerm> {
    None
}

/// The pattern `#(…)` with its members put as its type's, as [`flatten_pair_value`] puts a
/// value: every member stays, so `None`.
pub fn flatten_pair_pattern(_p: &Pattern) -> Option<Pattern> {
    None
}

/// `p` with every `#(…)` in it put as [`flatten_pair_pattern`] puts one.
pub fn flatten_pair_patterns(p: &Pattern) -> Pattern {
    let p = flatten_pair_pattern(p).unwrap_or_else(|| p.clone());
    match p {
        Pattern::Ctor { name, args } => Pattern::Ctor {
            name,
            args: args.iter().map(flatten_pair_patterns).collect(),
        },
        Pattern::Record { name, fields } => Pattern::Record {
            name,
            fields: fields
                .iter()
                .map(|(f, q)| (f.clone(), flatten_pair_patterns(q)))
                .collect(),
        },
        Pattern::Tuple(items) => Pattern::Tuple(items.iter().map(flatten_pair_patterns).collect()),
        other => other,
    }
}

/// `p` put as [`flatten_pair_pattern`] puts a `#(…)`.
fn sort_pair_pattern(p: &mut Pattern) {
    if let Some(flat) = flatten_pair_pattern(p) {
        *p = flat;
    }
}

/// `t` put as [`flatten_pair_value`] puts a `#(…)`.
fn sort_pair_value(t: &mut SurfaceTerm) {
    if let Some(flat) = flatten_pair_value(t) {
        *t = flat;
    }
}

/// `#(a, b, c)` as the record of the prelude's `Pair` that the checker elaborates:
/// `Pair { fst: a, snd: Pair { fst: b, snd: c } }`, `pair` naming the `Pair`. The
/// members are left as they are; anything but a tuple is `t` itself.
pub fn tuple_as_pairs<N: ?Sized>(t: &SurfaceTerm, pair: &N) -> SurfaceTerm
where
    for<'a> crate::identity::Name: From<&'a N>,
{
    if let Some(flat) = flatten_pair_value(t) {
        return tuple_as_pairs(&flat, pair);
    }
    let TermKind::Tuple(items) = &*t.kind else {
        return t.clone();
    };
    let mut items = items.clone();
    let Some(last) = items.pop() else {
        return SurfaceTerm::unit(t.span);
    };
    let span = t.span;
    items.into_iter().rev().fold(last, |snd, fst| {
        let cell = Span::new(fst.span.start, span.end);
        SurfaceTerm::new(
            TermKind::Record {
                name: crate::identity::Name::from(pair),
                fields: vec![("fst".into(), fst), ("snd".into(), snd)],
                base: None,
            },
            cell,
        )
    })
}

/// `#(a, b, c)` as the product the checker elaborates: `prod_mk(a, prod_mk(b, c))`, whose
/// type is the product `Prod(A, Prod(B, C))` and never a `Pair` written by its name. The
/// members are put as [`flatten_pair_value`] puts them; anything but a tuple is `t` itself.
pub fn tuple_as_products(t: &SurfaceTerm) -> SurfaceTerm {
    if let Some(flat) = flatten_pair_value(t) {
        return tuple_as_products(&flat);
    }
    let TermKind::Tuple(items) = &*t.kind else {
        return t.clone();
    };
    let mut items = items.clone();
    let Some(last) = items.pop() else {
        return SurfaceTerm::unit(t.span);
    };
    let span = t.span;
    items.into_iter().rev().fold(last, |snd, fst| {
        let cell = Span::new(fst.span.start, span.end);
        SurfaceTerm::app("prod_mk", vec![fst, snd], cell)
    })
}

/// The pattern `#(p, q, r)` as the record of the prelude's `Pair` that the checker
/// elaborates: `Pair { fst: p, snd: Pair { fst: q, snd: r } }`, `pair` naming the
/// `Pair`, in every member too. Any other pattern is `p` with its own members put so.
pub fn tuple_pattern_as_pairs<N: ?Sized>(p: &Pattern, pair: &N) -> Pattern
where
    for<'a> crate::identity::Name: From<&'a N>,
{
    if let Some(flat) = flatten_pair_pattern(p) {
        return tuple_pattern_as_pairs(&flat, pair);
    }
    match p {
        Pattern::Tuple(items) => {
            let mut items: Vec<Pattern> = items
                .iter()
                .map(|q| tuple_pattern_as_pairs(q, pair))
                .collect();
            let Some(last) = items.pop() else {
                return Pattern::Ctor {
                    name: format!("{PRELUDE_MODULE}{SEPARATOR}Star").into(),
                    args: Vec::new(),
                };
            };
            items
                .into_iter()
                .rev()
                .fold(last, |snd, fst| Pattern::Record {
                    name: crate::identity::Name::from(pair),
                    fields: vec![("fst".into(), fst), ("snd".into(), snd)],
                })
        }
        Pattern::Ctor { name, args } => Pattern::Ctor {
            name: name.clone(),
            args: args
                .iter()
                .map(|q| tuple_pattern_as_pairs(q, pair))
                .collect(),
        },
        Pattern::Record { name, fields } => Pattern::Record {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(f, q)| (f.clone(), tuple_pattern_as_pairs(q, pair)))
                .collect(),
        },
        other => other.clone(),
    }
}

/// Every `#(…)` of `s`, value and pattern, put as [`tuple_as_products`] and
/// [`tuple_pattern_as_pairs`] put it: what the checker
/// elaborates, where Nib and extraction keep the product.
pub fn lower_tuples(s: &mut Stmt, pair: &str) {
    let term = &mut |t: &mut SurfaceTerm| {
        super::walk::term(t, &mut |t| {
            if matches!(&*t.kind, TermKind::Tuple(_)) {
                *t = tuple_as_products(t);
            }
            let lower = |p: &mut Pattern| *p = tuple_pattern_as_pairs(p, pair);
            match &*t.kind {
                TermKind::Match { .. } | TermKind::Handle { .. } => {}
                _ => return,
            }
            match Arc::make_mut(&mut t.kind) {
                TermKind::Match { arms, .. } => arms.iter_mut().for_each(|a| lower(&mut a.pattern)),
                TermKind::Handle { handlers, .. } => {
                    for h in handlers {
                        match h {
                            Handler::Return { pattern: p, .. } => lower(p),
                            Handler::Operation { patterns, .. } => {
                                patterns.iter_mut().for_each(lower)
                            }
                        }
                    }
                }
                _ => {}
            }
        })
    };
    super::walk::roots(s, &mut *term);
    let laws = |laws: &mut [super::program::LawDecl]| {
        for l in laws {
            for (_, t) in &mut l.theorem.params {
                term(t);
            }
            term(&mut l.theorem.ty);
            if let Some(b) = &mut l.theorem.body {
                term(b);
            }
        }
    };
    lower_nested(s, &mut |s| match s {
        Stmt::Instance(i) => laws(&mut i.laws),
        Stmt::Class(c) => laws(&mut c.laws),
        _ => {}
    });
}

/// Every tuple value and pattern of `stmts` whose members all have labels in
/// the order of its type's members, as [`lower_prelude_sugar`] puts the
/// prelude's: for a macro's library, which is checked as executable code
/// without that pass.
pub fn sort_labelled_tuples(stmts: &mut [Stmt]) {
    fn pattern(p: &mut Pattern) {
        sort_pair_pattern(p);
        match p {
            Pattern::Ctor { args, .. } => args.iter_mut().for_each(pattern),
            Pattern::Record { fields, .. } => fields.iter_mut().for_each(|(_, a)| pattern(a)),
            Pattern::Tuple(items) => items.iter_mut().for_each(pattern),
            _ => {}
        }
    }
    for s in stmts {
        super::walk::roots(s, &mut |t| {
            super::walk::term(t, &mut |t| {
                sort_pair_value(t);
                if !matches!(&*t.kind, TermKind::Match { .. } | TermKind::Handle { .. }) {
                    return;
                }
                match Arc::make_mut(&mut t.kind) {
                    TermKind::Match { arms, .. } => {
                        arms.iter_mut().for_each(|a| pattern(&mut a.pattern))
                    }
                    TermKind::Handle { handlers, .. } => {
                        for h in handlers {
                            match h {
                                Handler::Return { pattern: p, .. } => pattern(p),
                                Handler::Operation { patterns, .. } => {
                                    patterns.iter_mut().for_each(pattern)
                                }
                            }
                        }
                    }
                    _ => {}
                }
            })
        });
    }
}

/// The prelude read as its own files, before any module is known: a name the reader writes with
/// the prelude's module (`std::prelude::Star` of the pattern `#()`) is the prelude's short
/// name, and a product type `A × B` is `Pair(A, B)`, in a law too. An instance whose head is a
/// product, `instance Ord(A × B)`, is the instance for `Pair`, and the kernel, which still reads
/// a program's `A × B` as its own product type, gets the instance a second time with its
/// products kept as written.
pub fn lower_prelude_sugar(stmts: &mut Vec<Stmt>) {
    let mut products: Vec<Stmt> = stmts
        .iter()
        .filter(|s| matches!(s, Stmt::Instance(i) if matches!(&*i.head.kind, TermKind::Product(_))))
        .cloned()
        .collect();
    lower_prelude(stmts, true);
    lower_prelude(&mut products, false);
    stmts.extend(products);
}

/// The prelude's names read as [`lower_prelude_sugar`] reads them, its products kept as
/// written: for Nib and extraction, where a product `A × B` and `#(…)` are not the `Pair`
/// the kernel lowers them to, and a `Pair` written by its name is never a product.
pub fn lower_prelude_names(stmts: &mut [Stmt]) {
    lower_prelude(stmts, false)
}

thread_local! {
    /// Whether [`lower_prelude`] lowers the products to `Pair`.
    static LOWER_PRODUCTS: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
}

fn lowering_products() -> bool {
    LOWER_PRODUCTS.with(|p| p.get())
}

fn lower_prelude(stmts: &mut [Stmt], products: bool) {
    let before = LOWER_PRODUCTS.with(|p| p.replace(products));
    fn name(n: &mut String) {
        if let Some(rest) = n
            .strip_prefix(PRELUDE_MODULE)
            .and_then(|r| r.strip_prefix(SEPARATOR))
        {
            *n = rest.to_string();
        }
    }
    fn pattern(p: &mut Pattern) {
        // `#(p, q)` is the prelude's own `Pair` here, as the checker elaborates it.
        if lowering_products() {
            *p = tuple_pattern_as_pairs(p, "Pair");
        }
        match p {
            Pattern::Tuple(items) => items.iter_mut().for_each(pattern),
            Pattern::Ctor { name: n, args } => {
                (n).edit_spelling(|spelling| name(spelling));
                args.iter_mut().for_each(pattern);
            }
            Pattern::Record { name: n, fields } => {
                (n).edit_spelling(|spelling| name(spelling));
                fields.iter_mut().for_each(|(_, a)| pattern(a));
            }
            _ => {}
        }
    }
    fn pairs(t: &mut SurfaceTerm) {
        if !lowering_products() {
            return;
        }
        if let TermKind::Product(items) = &*t.kind {
            // The members in the order written: nested products give theirs, `Unit` gives none.
            let mut items = product_type_members(items);
            if items.len() < 2 {
                *t = items
                    .pop()
                    .unwrap_or_else(|| SurfaceTerm::var("Unit", t.span));
                return;
            }
            items.iter_mut().for_each(pairs);
            let last = items.pop().expect("two or more");
            let span = t.span;
            *t = items.into_iter().rev().fold(last, |snd, fst| {
                SurfaceTerm::app("Pair", vec![fst, snd], span)
            });
        }
    }
    fn term(t: &mut SurfaceTerm) {
        super::walk::term(t, &mut |t| {
            pairs(t);
            // `#(a, b)` is the prelude's own `Pair` here, by its short name, as the checker elaborates it.
            if lowering_products() && matches!(&*t.kind, TermKind::Tuple(_)) {
                *t = tuple_as_pairs(t, "Pair");
            }
            let needed = match &*t.kind {
                TermKind::Var(n) => n.starts_with(PRELUDE_MODULE),
                TermKind::Match { .. } | TermKind::Handle { .. } => true,
                _ => false,
            };
            if !needed {
                return;
            }
            match Arc::make_mut(&mut t.kind) {
                TermKind::Var(n) => n.edit_spelling(|spelling| name(spelling)),
                TermKind::Match { arms, .. } => {
                    arms.iter_mut().for_each(|a| pattern(&mut a.pattern))
                }
                TermKind::Handle { handlers, .. } => {
                    for h in handlers {
                        match h {
                            Handler::Return { pattern: p, .. } => pattern(p),
                            Handler::Operation { patterns, .. } => {
                                patterns.iter_mut().for_each(pattern)
                            }
                        }
                    }
                }
                _ => {}
            }
        });
    }
    fn laws(laws: &mut [super::program::LawDecl]) {
        for l in laws {
            for (_, t) in &mut l.theorem.params {
                term(t);
            }
            term(&mut l.theorem.ty);
            if let Some(b) = &mut l.theorem.body {
                term(b);
            }
        }
    }
    for s in stmts {
        LOWER_PRODUCTS.with(|p| p.set(products));
        super::walk::roots(s, &mut |t| term(t));
        lower_nested(s, &mut |s| match s {
            Stmt::Instance(i) => {
                pairs(&mut i.head);
                laws(&mut i.laws);
            }
            Stmt::Class(c) => laws(&mut c.laws),
            _ => {}
        });
    }
    LOWER_PRODUCTS.with(|p| p.set(before));
}

/// `f` on `s` and on each statement of a `mutual` or a `module` in it.
fn lower_nested(s: &mut Stmt, f: &mut dyn FnMut(&mut Stmt)) {
    match s {
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            items.iter_mut().for_each(|i| lower_nested(i, f))
        }
        Stmt::Attributed { stmt, .. } => lower_nested(stmt, f),
        _ => f(s),
    }
}

/// The functions of the prelude's modules that run as written
/// (`Text::of_nat`): the kernel's prelude does not declare them.
fn runtime_module_fns() -> &'static HashSet<String> {
    static NAMES: OnceLock<HashSet<String>> = OnceLock::new();
    NAMES.get_or_init(|| {
        let of = |text: &str| -> HashSet<String> {
            super::program::prelude_as_written(text)
                .as_ref()
                .map(|p| {
                    let mut names = super::modules::declared(&p.stmts);
                    names.extend(super::modules::declared_flat(&p.stmts));
                    names.into_iter().collect()
                })
                .unwrap_or_default()
        };
        let kernel = of(crate::nibstd::KERNEL);
        of(crate::nibstd::PRELUDE)
            .into_iter()
            .filter(|n| !kernel.contains(n))
            .collect()
    })
}

/// The module functions of the prelude that the file `j` models, when it is
/// a file of `std` (`Text::of_nat` of `std::Text`).
fn models_in(j: usize, stmts: &[Stmt], modules: &[String]) -> HashSet<String> {
    if !is_std(&modules[j]) {
        return HashSet::new();
    }
    super::modules::declared(stmts)
        .into_iter()
        .filter(|n| runtime_module_fns().contains(n))
        .collect()
}

/// A model of the prelude's builtin that [`split_models`] named apart: the
/// file of `std` that declares it, its name as written (`Text::of_nat`) and
/// its full name (`std::Text::Text::of_nat`).
#[derive(Clone, Debug)]
pub struct Model {
    pub file: usize,
    pub name: String,
    pub full: String,
}

/// Tells a module function of the prelude apart from the model a file of
/// `std` gives it, where a file of the program means the builtin.
///
/// `Text::of_nat` written in a file that reaches `std::Text` is the model
/// the proofs see; written in a file that does not, it is the builtin, which
/// runs as written and is not in proofs. Both are written `Text::of_nat`, so
/// when the program has both, each file's uses that mean the model are
/// written as its full name here, before the modules are read, and
/// [`rename_models`] renames the model itself after. A name a macro's `quote`
/// writes as the builtin (`std::prelude::Text::of_nat`, from what its file
/// sees) is the builtin's again where the file that expands it reaches the
/// model.
///
/// What the program runs is the same either way: the model is extracted to
/// the builtin.
pub fn split_models(
    files: &mut [Vec<Stmt>],
    modules: &[String],
    imports: Option<&[Vec<usize>]>,
) -> Vec<Model> {
    if imports.is_none() {
        return Vec::new();
    }
    let reach = reaches(modules, imports);
    let reaches_file = |i: usize, j: usize| i == j || reach[i].contains(&j);
    let mut models = Vec::new();
    for (j, stmts) in files.iter().enumerate() {
        for n in models_in(j, stmts, modules) {
            models.push(Model {
                file: j,
                full: format!("{}{SEPARATOR}{n}", modules[j]),
                name: n,
            });
        }
    }
    let builtin = |n: &str| format!("{PRELUDE_MODULE}{SEPARATOR}{n}");
    // Only where a file means the builtin: the names stay as written
    // otherwise.
    let mut uses: Vec<HashSet<String>> = vec![HashSet::new(); files.len()];
    for (i, stmts) in files.iter_mut().enumerate() {
        for s in stmts.iter_mut() {
            super::walk::stmt(s, &mut |t| {
                if let TermKind::Var(n) = &*t.kind {
                    uses[i].insert(n.to_string());
                }
            });
        }
    }
    models.retain(|m| {
        (0..files.len()).any(|i| {
            uses[i].contains(&builtin(&m.name))
                || (!is_std(&modules[i]) && !reaches_file(i, m.file) && uses[i].contains(&m.name))
        })
    });
    for (i, stmts) in files.iter_mut().enumerate() {
        let here: HashMap<String, String> = models
            .iter()
            .filter(|m| reaches_file(i, m.file))
            .flat_map(|m| {
                let model = (m.file != i).then(|| (m.name.clone(), m.full.clone()));
                model
                    .into_iter()
                    .chain([(builtin(&m.name), m.name.clone())])
            })
            .collect();
        if here.is_empty() {
            continue;
        }
        for s in stmts.iter_mut() {
            super::walk::stmt(s, &mut |t| {
                if let TermKind::Var(crate::identity::Name::Spelled(n)) = &*t.kind
                    && let Some(to) = here.get(n.as_str())
                {
                    t.kind = Arc::new(TermKind::Var(crate::identity::Name::Spelled(to.clone())));
                }
            });
        }
    }
    models
}

/// After the modules are read: each model of [`split_models`] in `stmts`,
/// the statements of the file that declares it, by its full name, and so
/// are that file's uses of it.
pub fn rename_models(stmts: &mut [Stmt], models: &[Model]) {
    let to: HashMap<&str, &str> = models
        .iter()
        .map(|m| (m.name.as_str(), m.full.as_str()))
        .collect();
    if to.is_empty() {
        return;
    }
    for s in stmts.iter_mut() {
        match s {
            Stmt::Fn(f) => {
                if !f.name.is_resolved()
                    && let Some(full) = to.get(f.name.as_str())
                {
                    f.name = crate::identity::Name::Spelled(full.to_string());
                }
            }
            Stmt::Theorem(t) | Stmt::Def(t) => {
                if !t.name.is_resolved()
                    && let Some(full) = to.get(t.name.as_str())
                {
                    t.name = crate::identity::Name::Spelled(full.to_string());
                }
            }
            _ => {}
        }
        super::walk::stmt(s, &mut |t| {
            if let TermKind::Var(crate::identity::Name::Spelled(n)) = &*t.kind
                && let Some(full) = to.get(n.as_str())
            {
                t.kind = Arc::new(TermKind::Var(crate::identity::Name::Spelled(
                    full.to_string(),
                )));
            }
        });
    }
}

#[cfg(test)]
mod source_spelling_tests {
    use super::*;
    use crate::identity::DeclRef;

    #[test]
    fn a_bound_source_spelling_does_not_depend_on_other_programs() {
        let reference = DeclRef::fresh("file::math::Record");
        reference.set_source_offset("file::".len());
        let bound = Name::Global(reference.clone());
        register_modules(&["file".into()]);
        assert_eq!(short(&bound), "math::Record");
        register_modules(&["file::math".into()]);
        assert_eq!(short(&bound), "math::Record");
        assert_eq!(reference.source_display(), "math::Record");
        assert_eq!(
            reference.constructor(0, "Mk").source_display(),
            "math::Record::Mk"
        );
        assert_eq!(reference.display(), "file::math::Record");
    }

    #[test]
    fn unresolved_modules_are_local_to_the_reading_thread() {
        register_modules(&["file".into()]);
        std::thread::spawn(|| {
            register_modules(&["file::math".into()]);
            assert_eq!(short("file::math::Record"), "Record");
        })
        .join()
        .unwrap();
        assert_eq!(short("file::math::Record"), "math::Record");
        register_modules(&["other".into()]);
        assert_eq!(short("file::math::Record"), "file::math::Record");
    }
}
