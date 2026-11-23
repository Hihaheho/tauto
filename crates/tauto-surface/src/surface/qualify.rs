//! Every declaration is told apart by its full name: the module of the file
//! that declares it and its own name (`app::List`, `std::list::List::filter`,
//! `std::prelude::List`); a constructor's full name has its type before its
//! own name (`std::text::Text::Mk`). Where the program is read, each file's statements
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
//! (`std::text::Text::len` of `text_len`). A name the prelude declares and a
//! file the file does not reach declares too (another file of the tote that
//! no importer of the file brings in, or a file of a tote the tote depends
//! on directly) is ambiguous: taking the prelude's would hide that declaration
//! without a word, and taking the other would depend on what the file does
//! not import. The types the
//! language itself has and the standard library declares (`Text`, `Never`)
//! are read as prelude names. Where another declaration of the name (a
//! constructor `Text`) is declared or imported, the bare name is ambiguous:
//! `std::prelude::Text` is the type, and the other is written in full.
//!
//! A name the file's imports declare, directly or through their own imports,
//! means only what they declare: a file that imports this one cannot change
//! what its names mean. What a file of a tote imports from another tote, the
//! standard library included (`std::text`, say), is reached by the files of
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

use crate::span::Span;
use tauto_message::{Message, msg};

use super::program::{Generates, Handler, NOT_A_DECLARATION, Pattern, Stmt, Vis};
use super::{Name, SurfaceTerm, TermKind, scoped};

pub const PRELUDE_MODULE: &str = "std::prelude";
/// The module of the files of `std/builtin/`: the library tauto comes with
/// that a file sees only by importing it (`import std::builtin::os`).
pub const BUILTIN_MODULE: &str = "std::builtin";

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

/// The names of [`GENERATED`] that only a type with a decidable equality has.
const EQUALITY_GENERATED: &[&str] = &["::beq", "::beq_sound", "::beq_refl", "::deq", "::eq"];

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

/// The root of the standard library's modules (`std::list`). The one tote
/// that takes it as its name is the library's source, which the loader reads
/// only by itself (no other tote or file reaches it), so a module under it is
/// the library's, and this is the one place that reads a module's root.
pub const STD_ROOT: &str = "std";

/// A module path split into its root and the rest (`std::list` into `std`
/// and `List`).
pub fn module_root(module: &str) -> (&str, Option<&str>) {
    match module.split_once(SEPARATOR) {
        Some((root, rest)) => (root, Some(rest)),
        None => (module, None),
    }
}

/// The path of the library's module `module` within the library (`List` of
/// `std::list`); none for a module of a tote and for the prelude's.
pub fn std_module_path(module: &str) -> Option<&str> {
    match module_root(module) {
        (STD_ROOT, Some(path)) if module_root(path).0 != "prelude" => Some(path),
        _ => None,
    }
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
    in_module(PRELUDE_MODULE) || in_module(BUILTIN_MODULE) || modules.iter().any(|m| in_module(m))
}

fn bare(key: &str) -> &str {
    key.strip_prefix(EFFECT).unwrap_or(key)
}

/// A full name as a source file writes it, with `.` between its parts: how
/// a message shows a name, so what it suggests can be written as it is.
pub fn written(name: &str) -> String {
    super::print::raw(name)
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
/// constructor `u64` of `std::uint`) is renamed to its full name, so a file
/// that does not import it still means the type, whatever else the program
/// reads and in whatever order. `Text` and `Never` are not among them: the
/// standard library declares those types itself.
pub const BUILTIN_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "uhost", "nat", "Bool", "Float",
    "Float32", "Decimal",
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

/// The module a file of the prelude is imported by: `std::prelude::std` for a
/// core file, which every file sees without the import, and `std::builtin::os`
/// for one a file sees only by importing it.
pub(crate) fn prelude_file_module(file: &str) -> String {
    let core = crate::nibstd::CORE_PRELUDE_FILES
        .iter()
        .any(|p| prelude_stem(p) == file);
    let root = if core { PRELUDE_MODULE } else { BUILTIN_MODULE };
    format!("{root}{SEPARATOR}{file}")
}

/// The names a prelude text declares, and the modules it opens (by their
/// full names): the top-level declarations (effects marked with `!`), the
/// functions of modules (`Text::join`), and the modules themselves.
fn prelude_text_names(text: &'static str, public_only: bool) -> (HashSet<String>, HashSet<String>) {
    fn prefixes(name: &str, out: &mut HashSet<String>) {
        for (at, _) in name.match_indices(SEPARATOR) {
            out.insert(name[..at].to_string());
        }
    }
    fn modules_of(s: &Stmt, at: &mut Vec<String>, out: &mut HashSet<String>) {
        match s {
            Stmt::Module { name, items, .. } => {
                at.push(name.clone());
                out.insert(at.join(SEPARATOR));
                items.iter().for_each(|i| modules_of(i, at, out));
                at.pop();
            }
            Stmt::Fn(f) => prefixes(&f.name, out),
            Stmt::Theorem(t) | Stmt::Def(t) => prefixes(&t.name, out),
            Stmt::Extern { fns, .. } => fns.iter().for_each(|f| prefixes(&f.name, out)),
            Stmt::Struct(d) | Stmt::Enum(d) => prefixes(&d.name, out),
            Stmt::Inductive(d) => prefixes(&d.name, out),
            Stmt::Mutual { items, .. } => items.iter().for_each(|i| modules_of(i, at, out)),
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
        let mut mods: Vec<(String, String)> = Vec::new();
        for (path, text) in crate::nibstd::PRELUDE_FILES {
            let stem = prelude_stem(path);
            if !crate::nibstd::is_core_prelude_file(path) {
                continue;
            }
            let (d, m) = prelude_text_names(text, true);
            for n in d {
                if kernel.contains(&n) {
                    continue;
                }
                let files = core.entry(n).or_default();
                if !files.iter().any(|f| f == stem) {
                    files.push(stem.to_string());
                }
            }
            mods.extend(m.into_iter().map(|m| (m, stem.to_string())));
        }
        // A module is the name of the file that opens it only when no file declares the name:
        // `Collections` adds `List::consume` to `List`, and `List` is still the type `Std`
        // declares.
        for (m, stem) in mods {
            if kernel.contains(&m) || core.get(&m).is_some_and(|fs| !fs.contains(&stem)) {
                continue;
            }
            let files = core.entry(m).or_default();
            if !files.iter().any(|f| *f == stem) {
                files.push(stem);
            }
        }
        core
    })
}

/// The item an import list names a name of the prelude by: a constructor's type
/// (`Option` of `Some`), a module's name for its function (`List` of `List::map`), an effect
/// without its mark, any other name itself.
/// The prelude files that declare each public name, by their stems: a name
/// of a file the program imports (`import std::prelude::std { not }`) is that
/// file's, whether or not the file is core.
fn prelude_declarers() -> &'static HashMap<String, Vec<String>> {
    static DECLARERS: OnceLock<HashMap<String, Vec<String>>> = OnceLock::new();
    DECLARERS.get_or_init(|| {
        let mut out: HashMap<String, Vec<String>> = HashMap::new();
        for (path, text) in crate::nibstd::PRELUDE_FILES {
            let (decls, mods) = prelude_text_names(text, true);
            for n in decls.into_iter().chain(mods) {
                out.entry(n)
                    .or_default()
                    .push(prelude_stem(path).to_string());
            }
        }
        out
    })
}

fn prelude_item(n: &str) -> String {
    let b = bare(n);
    if n.starts_with(EFFECT) {
        return b.to_string();
    }
    if let Some(ty) = prelude_ctor_types().get(b) {
        return ty.clone();
    }
    b.split(SEPARATOR).next().unwrap_or(b).to_string()
}

/// The type of each constructor of the prelude, by the constructor's name,
/// when the type has another name: [`prelude_item`] is asked for every name
/// of the library in every file.
fn prelude_ctor_types() -> &'static HashMap<String, String> {
    static TYPES: OnceLock<HashMap<String, String>> = OnceLock::new();
    TYPES.get_or_init(|| {
        let mut out: HashMap<String, String> = HashMap::new();
        for (ty, cs) in prelude_ctors() {
            for c in cs.keys() {
                if c != ty {
                    // A name two types have as a constructor is read as the
                    // first type's, in the order of their names.
                    out.entry(c.clone())
                        .and_modify(|t| {
                            if ty < t {
                                *t = ty.clone();
                            }
                        })
                        .or_insert_with(|| ty.clone());
                }
            }
        }
        out
    })
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
        Stmt::Reexport {
            aliases: Some(aliases),
            ..
        } => {
            for alias in aliases {
                if alias.effect {
                    out(&format!("{EFFECT}{}", alias.name));
                } else {
                    out(&alias.name);
                }
            }
        }
        Stmt::Inductive(d) => {
            out(&d.name);
            d.constructors.iter().for_each(|c| out(&c.name));
            // A proposition has no equality to decide: the kernel makes none of
            // `T::beq`, …, `T::eq` for it, so those names stay free for another file.
            let proposition =
                matches!(&*d.sort.kind, TermKind::Var(k) if crate::bindings::is_library(k, "Prop"));
            for suffix in GENERATED {
                if proposition && EQUALITY_GENERATED.contains(suffix) {
                    continue;
                }
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

thread_local! {
    /// The files of the program that stand alone ([`StandaloneFiles`]), by index.
    static STANDALONE: std::cell::RefCell<Vec<bool>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// While kept, the files given `true` stand alone: each is one of a tote's other files (a
/// proof, an example, a script) and reads what it imports, as when it is checked alone. A
/// prelude name another file of the tote declares is not made ambiguous for it by that file.
pub struct StandaloneFiles(Vec<bool>);

impl StandaloneFiles {
    pub fn of(alone: Vec<bool>) -> Self {
        StandaloneFiles(STANDALONE.with(|s| s.replace(alone)))
    }
}

impl Drop for StandaloneFiles {
    fn drop(&mut self) {
        let before = std::mem::take(&mut self.0);
        STANDALONE.with(|s| *s.borrow_mut() = before);
    }
}

/// Whether a macro call of the statement says it makes a type.
fn makes_type(s: &Stmt) -> bool {
    let generates = match s {
        Stmt::Attributed {
            generates, stmt, ..
        } => {
            if makes_type(stmt) {
                return true;
            }
            generates
        }
        Stmt::Called { generates, .. } => generates,
        _ => return false,
    };
    generates
        .items
        .iter()
        .any(|(kind, _)| matches!(kind.as_str(), "inductive" | "struct" | "enum"))
}

/// What a top-level statement declares, and the name a top-level `let` or
/// `var` binds. The program reads those names in one scope across its files,
/// so where another file declares the name too, each is renamed to its full
/// name like any declaration, and neither file reads the other's.
fn declared_or_bound(s: &Stmt, out: &mut dyn FnMut(&str)) {
    match s {
        Stmt::Let { name, .. } | Stmt::Var { name, .. } => out(name),
        // What a macro call says it makes is the file's before the macros run: another file's
        // declaration of the name is named apart from it from the first reading on, as it is
        // from one the file writes itself.
        Stmt::Attributed {
            generates, stmt, ..
        } => {
            generated_names(generates, out);
            declared_or_bound(stmt, out);
        }
        Stmt::Called { generates, .. } => generated_names(generates, out),
        _ => declared(s, out),
    }
}

/// The functions and theorems written with their prefix (`fn S::made`) that a macro call says
/// it makes, and those under an attribute: each is the declaration of its full name, as one the
/// file writes itself is ([`super::modules::declared_flat`]). A reference to `S::made` then means
/// that declaration, whatever another file's `S` makes of the prefix.
fn made_with_prefix(s: &Stmt, out: &mut Vec<String>) {
    match s {
        Stmt::Attributed {
            generates, stmt, ..
        } => {
            prefixed_items(generates, out);
            out.extend(super::modules::declared_flat(std::slice::from_ref(stmt)));
            made_with_prefix(stmt, out);
        }
        Stmt::Called { generates, .. } => prefixed_items(generates, out),
        Stmt::Mutual { items, .. } => items.iter().for_each(|i| made_with_prefix(i, out)),
        _ => {}
    }
}

fn prefixed_items(generates: &Generates, out: &mut Vec<String>) {
    out.extend(
        generates
            .items
            .iter()
            .filter(|(kind, n)| {
                matches!(kind.as_str(), "fn" | "def" | "theorem") && n.contains(SEPARATOR)
            })
            .map(|(_, n)| n.clone()),
    );
}

/// The names a macro call says it makes. An `instance` has no name of its own: its item is
/// the class it is of, which the call does not declare, so a file whose macro makes an
/// instance of an imported class (`instance Key`) still reads `Key` as the import.
fn generated_names(generates: &Generates, out: &mut dyn FnMut(&str)) {
    generates
        .items
        .iter()
        .filter(|(kind, _)| kind != "instance")
        .for_each(|(_, n)| out(n));
}

/// How the file `here` writes the import of the file `target`, by their indices,
/// from the paths the program is read from and the dependencies of their totes.
pub type Spell<'a> = &'a dyn Fn(usize, usize) -> String;

/// How the file `here` imports the file `target`: by `spell` when the program
/// is read from files, else by their modules ([`import_spelling`]).
/// [`spelling`] for each of the files `targets`, once each.
fn spellings(
    spell: Option<Spell>,
    modules: &[String],
    here: usize,
    targets: &[usize],
) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for &t in targets {
        let s = spelling(spell, modules, here, t);
        if !out.contains(&s) {
            out.push(s);
        }
    }
    out
}

fn spelling(spell: Option<Spell>, modules: &[String], here: usize, target: usize) -> String {
    match spell {
        Some(spell) => spell(here, target),
        None => import_spelling(&modules[here], &modules[target]),
    }
}

/// How the file `here` imports the file `target`, both by module: a file of the
/// standard library as `std::list`; a file of the same tote by its path from
/// `here`'s directory, quoted (`"setoid.taut"`, `"../src/setoid.taut"`); a file
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
/// `::`, which cannot be in a name written `_`. A part that begins with a
/// digit (`15b.taut`) has `_` before it: a full name is written back into
/// the source text the later passes read again (a row's `15b::wait(R)`), and
/// a name that begins with a digit is read there as a number.
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
            let digit = p.chars().next().is_some_and(char::is_numeric);
            digit
                .then_some('_')
                .into_iter()
                .chain(p.chars().map(|c| {
                    if c.is_alphanumeric() || c == '_' {
                        c
                    } else {
                        '_'
                    }
                }))
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
    Vec<(Message, Span)>,
    Scopes,
) {
    let mut warnings = Vec::new();
    let mut scopes = Vec::new();
    let (errors, seeing, missing) = qualify(
        files,
        modules,
        imports,
        below,
        true,
        spell,
        Some((lists, bare, quoted)),
        &mut Vec::new(),
        &mut warnings,
        &mut scopes,
    );
    (errors, seeing, missing, warnings, scopes)
}

/// By file, the declarations that import at the head of their bodies ([`FileScopes`]).
pub type Scopes = Vec<FileScopes>;

/// The declarations of a file that import at the head of their bodies, each by its name,
/// with what the names of its body mean ([`files_seeing`]): a name a macro written there
/// makes with `Syn::global` means what the body sees. The file's own seeing, given beside
/// them, holds what those bodies see too, for the passes that bind the whole file; `file`
/// is what the file sees without them, when it has such a declaration.
#[derive(Debug, Clone, Default)]
pub struct FileScopes {
    pub file: Option<HashMap<String, String>>,
    pub declarations: Vec<(String, HashMap<String, String>)>,
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

    /// A use introduced by lowering (for example `for`), which keeps a listed
    /// name used without requiring the source to have written it.
    pub fn keeps_listed(path: String, span: Span) -> Self {
        Self {
            written: path.clone(),
            path,
            span,
            keeps_only: true,
        }
    }
}

/// Whether `t` calls `Syn::global`: the file is a macro's, which names declarations by text.
fn calls_syn_global(t: &SurfaceTerm) -> bool {
    matches!(&*t.kind, TermKind::App { function, .. }
        if matches!(&*function.kind, TermKind::Var(f)
            if f.spelling() == Some("Syn::global")
                || crate::bindings::is_library_selected(f, "Syn::global")))
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
    /// The import as written after `import`: `std::text`, `"value.taut"`.
    pub spelling: String,
    /// The names written in its list, if it has one.
    pub names: Option<Vec<(String, Span)>>,
    /// The whole `import` statement.
    pub span: Span,
    /// Written at the head of a declaration's body: it brings its names to that body only.
    pub body: bool,
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
        &mut Vec::new(),
    );
    (errors, seeing, missing, fixes, warnings)
}

/// The types of `stmts` with a constructor named `leaf` when two or more of them have one,
/// each by the name its file gives it (`Mode`, not `m::Mode`); `None` otherwise.
fn ctor_types_of(stmts: &[Stmt], module: &str, leaf: &str) -> Option<Vec<String>> {
    if leaf.contains(SEPARATOR) {
        return None;
    }
    let mut types: Vec<String> = Vec::new();
    for s in stmts {
        ctors_of(s, &mut |ty, c| {
            let c = c
                .strip_prefix(ty)
                .and_then(|rest| rest.strip_prefix(SEPARATOR))
                .unwrap_or(c);
            if c != leaf || c == ty {
                return;
            }
            let ty = ty
                .strip_prefix(module)
                .and_then(|rest| rest.strip_prefix(SEPARATOR))
                .unwrap_or(ty);
            if !types.iter().any(|t| t == ty) {
                types.push(ty.to_string());
            }
        });
    }
    (types.len() > 1).then_some(types)
}

/// Whether `module` is a file of the prelude (`std::builtin::os`) that declares `item`: the
/// prelude's names are read as the prelude's, not as that file's, so a list keeps them as written.
fn prelude_declares(module: &str, item: &str) -> bool {
    let Some(file) = [PRELUDE_MODULE, BUILTIN_MODULE]
        .iter()
        .find_map(|root| module.strip_prefix(root)?.strip_prefix(SEPARATOR))
    else {
        return false;
    };
    // The core files are imported by a file of a tote without the prelude, so their names are
    // listed as the other files' are (`Text` of `std::prelude::Text`, for `Text::byte`).
    let maps = || [hidden_prelude(), core_prelude()].into_iter();
    let declares =
        |n: &str| maps().any(|m| m.get(n).is_some_and(|fs| fs.iter().any(|f| f == file)));
    // A module whose functions the file adds to a module of the core (`U64` of
    // `U64::of_text`): the file declares the module's functions, which a list names
    // by the module.
    let adds_to_module = || {
        let prefix = format!("{item}{SEPARATOR}");
        maps().any(|m| {
            m.iter()
                .any(|(n, fs)| n.starts_with(&prefix) && fs.iter().any(|f| f == file))
        })
    };
    declares(item)
        || adds_to_module()
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
    // The files the file reaches in a fixed order, so that a name two of them declare is held
    // to the same import in every run.
    let mut reached: Vec<usize> = reach[i].iter().copied().collect();
    reached.sort_unstable();
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
                    Stmt::Macro { name, public, .. } => *public && name == called,
                    Stmt::Syntax { name, .. } => name == called,
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
            if !own && let Some(j) = reached.iter().copied().find(|&j| declares(j)) {
                // A macro of a module comes with the module, as its functions do:
                // `Log::info!` is listed as `Log`.
                let item = called.split(SEPARATOR).next().unwrap_or(called);
                by_file
                    .entry(j)
                    .or_default()
                    .push((item.to_string(), called.to_string(), *span));
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
                    // file (`std::builtin::os`) is held to that import.
                    let files_of = hidden_prelude()
                        .get(n.as_str())
                        // A core file's name is held to its import as well, where the file
                        // imports it (`U64::of_text` of `std::prelude::Collections`).
                        // A file with the prelude sees the prelude's own names without it.
                        .or_else(|| {
                            core_prelude()
                                .get(n.as_str())
                                .filter(|_| bare_file || !prelude_names().contains(n.as_str()))
                        });
                    let from = files_of
                        // The files in the order the prelude declares them, not the order of a
                        // set, so the same source is held to the same import every time.
                        .and_then(|fs| {
                            fs.iter().find_map(|f| {
                                reach[i]
                                    .iter()
                                    .copied()
                                    .find(|&j| modules[j] == prelude_file_module(f))
                            })
                        })
                        // A type of the language a file it reaches declares (`Text` of
                        // `std::text`).
                        .or_else(|| {
                            reached.iter().copied().find(|&j| {
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
            rel.split(SEPARATOR).next().unwrap_or(&rel).to_string()
        } else if let Some(ty) = ctor_type[j].get(&rel) {
            ty.clone()
        } else if let Some(types) = ctor_types_of(&files[j], &modules[j], &rel) {
            // A constructor whose name two types of the file share: a list names it by
            // its type. A pass that reads the constructor by its bare name does not say
            // which type, so it is held to the type the use writes (`Mode` of
            // `Mode::Scheduled`), else to one of them the import's list writes, else to
            // the first: never to the bare name, which the list cannot write.
            let written_type = usage
                .written
                .rsplit_once(SEPARATOR)
                .map(|(head, _)| head.rsplit(SEPARATOR).next().unwrap_or(head));
            let listed = |ty: &str| {
                lists.iter().any(|l| {
                    l.target == Some(j)
                        && l.names
                            .as_ref()
                            .is_some_and(|ns| ns.iter().any(|(n, _)| n == ty))
                })
            };
            types
                .iter()
                .find(|t| Some(t.as_str()) == written_type)
                .or_else(|| types.iter().find(|t| listed(t)))
                .unwrap_or(&types[0])
                .clone()
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
                    && !private[j].contains(k)
                    && bare(k)
                        .strip_prefix(item)
                        .is_some_and(|r| r.starts_with(SEPARATOR))
            })
    };
    // A macro or a syntax, whose calls the macros read, and a type of the language the file
    // declares (`Text` of `std::text`), which a file sees whatever it imports: kept as listed.
    let macro_named = |j: usize, item: &str| {
        language.contains(&format!("{}{SEPARATOR}{item}", modules[j]))
            || files[j].iter().any(|s| match s {
                Stmt::Macro { name, public, .. } => *public && name == item,
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
                if !keeps_only.contains(span)
                    && !names.iter().any(|(l, _)| l == item)
                {
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
                } else if !exported(j, l) && !prelude_declares(&modules[j], l) {
                    found.push((
                        msg!(
                            "surface-import-listed-unknown",
                            name = l.as_str(),
                            spelling = import.spelling.as_str()
                        ),
                        *span,
                    ));
                } else if !used_here.iter().any(|(item, _, _)| item == l)
                    // A module the file adds functions to (`module Bytes` after listing
                    // `Bytes`) uses the listed name.
                    && !owners.iter().any(|(k, o)| {
                        o.contains(&i) && {
                            let k = bare(k);
                            let k = k
                                .strip_prefix(modules[i].as_str())
                                .and_then(|r| r.strip_prefix(SEPARATOR))
                                .unwrap_or(k);
                            k.strip_prefix(l.as_str())
                                .is_some_and(|r| r.starts_with(SEPARATOR))
                        }
                    })
                    // A `for` expansion reads these; they are registered as
                    // keeps_only uses and may not yet attribute to `used_here`.
                    && !super::loops::FOR_EXPANSION_NAMES.contains(&l.as_str())
                {
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
        if let Some(names) = &import.names {
            for (l, _) in names {
                if super::loops::FOR_EXPANSION_NAMES.contains(&l.as_str()) {
                    wanted.push(l.clone());
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

/// What each import with a list of `lists` brings of the file it imports, by the items
/// of the lists; a file imported without a list at least once brings everything (no
/// entry).
fn brought<'a>(lists: impl Iterator<Item = &'a ImportList>) -> HashMap<usize, HashSet<String>> {
    let mut out: HashMap<usize, HashSet<String>> = HashMap::new();
    let mut whole: HashSet<usize> = HashSet::new();
    for import in lists {
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
}

/// The name a declaration that may import at the head of its body has.
fn files_decl_name(s: &Stmt) -> Option<String> {
    match s {
        Stmt::Fn(f) => f.name.spelling().map(str::to_string),
        Stmt::Theorem(d) | Stmt::Def(d) => d.name.spelling().map(str::to_string),
        Stmt::Attributed { stmt, .. } => files_decl_name(stmt),
        _ => None,
    }
}

/// What the names of one file mean ([`qualify`]).
struct Env {
    names: HashMap<String, Meaning>,
    unseen: HashSet<String>,
    plain: HashMap<String, String>,
    declares: HashMap<String, Full>,
    prelude_files: HashMap<String, String>,
}

/// A declaration that imports at the head of its body: what the names of its body mean,
/// the files they see, and its imports.
struct Scoped {
    /// The declaration, by its place among the file's statements.
    statement: usize,
    env: Env,
    reach: HashSet<usize>,
    brings: HashMap<usize, HashSet<String>>,
    lists: Vec<ImportList>,
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
    scoped_out: &mut Scopes,
) -> (
    Vec<(Message, Span)>,
    Vec<HashMap<String, String>>,
    Vec<MissingImport>,
) {
    // `for` expands to `iterator_ready` / `fold_finite` before this pass reads
    // which names each file uses. Expansion-only names are kept as listed uses.
    let (for_errors, for_sites) = super::loops::lower_fors(files);
    if let Some((_, _, quoted)) = lists {
        let mut quoted = quoted.borrow_mut();
        for (file, span) in for_sites {
            if quoted.len() <= file {
                quoted.resize(file + 1, Vec::new());
            }
            for (module, name) in [
                ("std::iterator", "for_ready"),
                ("std::iterator", "iterator_ready"),
                ("std::iterator", "IteratorReady"),
                ("std::finite_iteration", "fold_finite"),
                ("std::finite_iteration", "IterationControl"),
            ] {
                quoted[file].push(SourceUse::keeps_listed(
                    format!("{module}{SEPARATOR}{name}"),
                    span,
                ));
            }
        }
    }
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
    let mut flattened = for_errors;
    flattened.extend(super::modules::flatten_files(
        files,
        prelude_fns().iter().map(|n| n.as_str()),
        &ctors,
        modules,
        imports,
        warnings,
    ));
    for file in files.iter() {
        let mut direct = HashSet::new();
        for statement in file.iter().filter(|s| !matches!(s, Stmt::Reexport { .. })) {
            declared(statement, &mut |name| {
                direct.insert(name.to_string());
            });
        }
        for statement in file {
            if let Stmt::Reexport { span, .. } = statement {
                declared(statement, &mut |name| {
                    if !direct.insert(name.to_string()) {
                        flattened.push((
                            msg!("surface-module-export-duplicate", name = bare(name)),
                            *span,
                        ));
                    }
                });
            }
        }
    }
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
    // other is: a tote's copy of `std/text.taut` is that tote's own `Text`,
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
    // The names bound in the files that `j` is hidden from, worked out once for each `j` that
    // has a constructor with fields: asking `hidden` of every file for every name is quadratic
    // in the files, and a program with the standard library has hundreds.
    let hidden_binds: Vec<std::cell::OnceCell<HashSet<&str>>> =
        (0..files.len()).map(|_| std::cell::OnceCell::new()).collect();
    let bound_apart = |n: &str, j: usize| {
        file_ctors[j].contains(n)
            && hidden_binds[j]
                .get_or_init(|| {
                    (0..binds.len())
                        .filter(|&i| hidden(i, j))
                        .flat_map(|i| binds[i].iter().map(String::as_str))
                        .collect()
                })
                .contains(n)
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
                    // A type declared with its full name (one whose name a constructor of
                    // another file also has) is held by the name the file gives it.
                    let ty = ty
                        .strip_prefix(modules[i].as_str())
                        .and_then(|rest| rest.strip_prefix(SEPARATOR))
                        .unwrap_or(ty);
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
        |i: usize, ty: &str, n: &str| Full(format!("{}{SEPARATOR}{ty}{SEPARATOR}{n}", modules[i]));
    let full = |i: usize, n: &str| match ctor_type[i].get(bare(n)) {
        Some(ty) => scoped(i, ty, bare(n)),
        None => Full(format!("{}{SEPARATOR}{}", modules[i], bare(n))),
    };
    let fulls = |i: usize, n: &str| -> Vec<Full> {
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
    // Before the macros run, the files whose macro calls make a type: the constructors it will
    // have are not written yet, so a name such a file uses that only a file it does not see
    // declares may be one of them, and is read when the macros have run.
    let makes_types: Vec<bool> = files
        .iter()
        .map(|stmts| keep_prelude && stmts.iter().any(makes_type))
        .collect();
    let not_imported = |i: usize, n: &str, owners_of: &[usize]| {
        !makes_types[i] && uses[i].contains(bare(n)) && unreached(i, n, owners_of)
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
    let alias_names: HashSet<_> = files
        .iter()
        .flatten()
        .filter_map(|s| match s {
            Stmt::Reexport {
                aliases: Some(_), ..
            } => Some(s),
            _ => None,
        })
        .flat_map(|s| {
            let mut names = Vec::new();
            declared(s, &mut |n| names.push(n.to_string()));
            names
        })
        .collect();
    let renamed = |n: &str, owners_of: &[usize]| {
        alias_names.contains(n) || clash(n, owners_of)
            // A constructor of a type named apart is named apart with it: another file may make a
            // type of that name, with constructors of the same names, when its macros run.
            || owners_of.iter().any(|&j| {
                ctor_type[j]
                    .get(n)
                    .and_then(|t| Some((t, owners.get(t.as_str())?)))
                    .is_some_and(|(t, o)| clash(t, o))
            })
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
        flattened.extend(super::loops::lower_loops(files));
        flattened.extend(record_bases(files));
        scoped_out.extend((0..files.len()).map(|_| FileScopes::default()));
        return (flattened, vec![HashMap::new(); files.len()], Vec::new());
    }
    // `flattened` already holds `lower_fors` errors from the start of this pass.
    // Renaming depends on declarations and import reachability, which stay
    // fixed while each file's reference environment is built.
    let renamed: HashSet<&str> = owners
        .iter()
        .filter(|(name, from)| renamed(name, from))
        .map(|(name, _)| name.as_str())
        .collect();
    let mut by_full: HashMap<Full, String> = HashMap::new();
    for (n, o) in &owners {
        for &i in o {
            let mark = if n.starts_with(EFFECT) { EFFECT } else { "" };
            for f in fulls(i, n) {
                let to = if renamed.contains(n.as_str()) {
                    f.as_str().to_string()
                } else {
                    bare(n).to_string()
                };
                by_full.insert(Full(format!("{mark}{}", f.as_str())), to);
            }
        }
    }
    for n in &prelude {
        let mark = if n.starts_with(EFFECT) { EFFECT } else { "" };
        by_full.insert(
            Full(format!("{mark}{}", Full::prelude(bare(n)).as_str())),
            bare(n).to_string(),
        );
    }
    // A name of a file of the prelude, written in full by the module a file
    // imports it by (`std::builtin::par::Host`, `std::builtin::os::print`):
    // the prelude's declaration, as its short name is.
    for map in [hidden_prelude(), core_prelude()] {
        for (n, declaring) in map {
            let mark = if n.starts_with(EFFECT) { EFFECT } else { "" };
            for file in declaring {
                by_full.insert(
                    Full(format!(
                        "{mark}{}{SEPARATOR}{}",
                        prelude_file_module(file),
                        bare(n)
                    )),
                    bare(n).to_string(),
                );
            }
        }
    }
    for (_, n) in &written {
        // Written in full by the file itself.
        by_full.insert(Full(n.clone()), bare(n).to_string());
    }
    let language_full: HashSet<String> = language.iter().cloned().collect();
    for n in language {
        let to = short(&n).to_string();
        by_full.insert(Full(n), to);
    }
    let after = |i: usize, n: &str| match owners.get(n) {
        Some(_) if renamed.contains(n) => full(i, n).into_string(),
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
            stmts.iter().for_each(|s| made_with_prefix(s, &mut names));
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
                    Some(types) if types.iter().any(|t| t == ty) => scoped(i, ty, c).into_string(),
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
    // The imports at the head of a declaration's body bring their names to that body only.
    let file_lists = |i: usize| lists.and_then(|l| l.get(i)).into_iter().flatten();
    let brings: Vec<HashMap<usize, HashSet<String>>> = (0..files.len())
        .map(|i| brought(file_lists(i).filter(|l| !l.body)))
        .collect();
    // Whether the file `i` imports `j` with lists none of which brings the name `n` of `j`:
    // a constructor's or a generated name's type, a module's function's module, an effect.
    let unlisted_with = |brings_i: &HashMap<usize, HashSet<String>>, j: usize, n: &str| {
        let Some(items) = brings_i.get(&j) else {
            return false;
        };
        let b = bare(n);
        let item = if n.starts_with(EFFECT) {
            b.split(SEPARATOR).next().unwrap_or(b).to_string()
        } else if let Some(ty) = ctor_type[j].get(b) {
            ty.clone()
        } else {
            b.split(SEPARATOR).next().unwrap_or(b).to_string()
        };
        !items.contains(&item)
    };
    let unlisted = |i: usize, j: usize, n: &str| unlisted_with(&brings[i], j, n);
    // A name an import list does not bring is not seen, so it cannot collide.
    let errors = std::cell::RefCell::new(redeclared(
        files,
        modules,
        &owners,
        &reach,
        &private,
        &ctor_names,
        &unlisted,
    ));
    // The functions of each module a file declares, by the module's name:
    // flattened, a module has no declaration of its own (`Ct` of `Ct::u64_add`).
    let mut module_members: HashMap<&str, Vec<(&str, &Vec<usize>)>> = HashMap::new();
    for (k, all) in &owners {
        if let Some((head, _)) = k.split_once(SEPARATOR) {
            module_members.entry(head).or_default().push((k, all));
        }
    }
    let mut all_names: Vec<HashMap<String, Meaning>> = Vec::new();
    let mut all_unseen: Vec<HashSet<String>> = Vec::new();
    let mut all_plain: Vec<HashMap<String, String>> = Vec::new();
    // The names each file declares that this pass renames, with the full
    // name each declaration takes: where a name is ambiguous to read (a
    // non-core prelude name the file imports and declares too), the
    // declaration is still the file's own.
    let mut all_declares: Vec<HashMap<String, Full>> = Vec::new();
    let mut all_prelude_files: Vec<HashMap<String, String>> = Vec::new();
    // By file, each declaration that imports at the head of its body, with what its
    // names mean there.
    let mut all_scoped: Vec<Vec<Scoped>> = Vec::new();
    // What the names of the file `i` mean where it sees the files `reach_i`, imports
    // `imports_i` directly and brings of each what `brings_i` lists: its own
    // imports, or those and the imports at the head of a declaration's body.
    let env = |i: usize,
               reach_i: &HashSet<usize>,
               imports_i: Option<&[usize]>,
               brings_i: &HashMap<usize, HashSet<String>>| {
        let unreached_in = |n: &str, owners_of: &[usize]| {
            imports.is_some()
                && !owners_of.contains(&i)
                && owners_of.iter().all(|&j| !reach_i.contains(&j))
                && !prelude.contains(n)
        };
        let not_imported_in = |n: &str, owners_of: &[usize]| {
            !makes_types[i] && uses[i].contains(bare(n)) && unreached_in(n, owners_of)
        };
        let hidden_in = |j: usize| {
            imports.is_some()
                && i != j
                && !reach_i.contains(&j)
                && reach.iter().any(|r| r.contains(&i) && r.contains(&j))
        };
        let unlisted_in = |j: usize, n: &str| unlisted_with(brings_i, j, n);
        let mut names: HashMap<String, Meaning> = HashMap::new();
        let mut declares: HashMap<String, Full> = HashMap::new();
        // The names the file sees both from the prelude file it imports
        // and from a declaration of its own or of its imports, with that
        // prelude file.
        let mut prelude_files: HashMap<String, String> = HashMap::new();
        let mut unseen: HashSet<String> = HashSet::new();
        let mut plain: HashMap<String, String> = HashMap::new();
        for (n, all) in &owners {
            if not_imported_in(n, all) || (n.starts_with(EFFECT) && unreached_in(n, all)) {
                names.insert(
                    n.clone(),
                    Meaning::NotImported(
                        modules[all[0]].clone(),
                        spellings(spell, modules, i, all),
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
                        .filter(|&j| (j == i || reach_i.contains(&j)) && !private_to(i, j, n));
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
            // A prelude name that only the private declarations of other files have is the
            // prelude's: a file does not see another file's own names, so they take nothing
            // from the prelude (`docs/design/visibility.md`).
            if seen.is_empty() && imports.is_some() && prelude.contains(n) {
                continue;
            }
            // An import with a list brings only what it lists: a file it does not bring the
            // name from does not take it. Where no file brings it, the name is kept to the files
            // that declare it, and the list's check says which list to write it in.
            let brought: Vec<usize> = seen
                .iter()
                .copied()
                .filter(|&j| !unlisted_in(j, n))
                .collect();
            let seen = if brought.is_empty() { seen } else { brought };
            let o = if seen.is_empty() { all } else { &seen };
            // A file that declares the language's type itself (the
            // standard library's `inductive Text`, wherever it is read from).
            let declares_type = |j: usize| {
                files[j]
                    .iter()
                    .any(|st| language_type(st) == Some(n.as_str()))
            };
            let meaning = if o.contains(&i)
                && LANGUAGE_TYPES.contains(&n.as_str())
                && !is_std(&modules[i])
                && !declares_type(i)
            {
                // The file's own declaration of the language type's name (a
                // constructor `Text`): the bare name is ambiguous here too.
                let mut all = fulls(i, n);
                all.push(Full::prelude(n));
                Meaning::Ambiguous(all)
            } else if o.contains(&i) {
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
                        .filter(|j| imports_i.unwrap_or(&[]).contains(j))
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
                // An imported declaration of the name, a constructor `Text`
                // say, is not read as the type either: the bare name is
                // ambiguous, and the full name says which is meant (AI-Native:
                // no silent precedence between the two).
                if LANGUAGE_TYPES.contains(&n.as_str())
                    && !imported
                        .iter()
                        .all(|&j| is_std(&modules[j]) || declares_type(j))
                {
                    let mut all: Vec<Full> = imported.iter().flat_map(|&j| fulls(j, n)).collect();
                    all.push(Full::prelude(n));
                    names.insert(n.clone(), Meaning::Ambiguous(all));
                    continue;
                }
                // A prelude name whose prelude file this file imports, listing it or
                // listing nothing (`import std::builtin::par`), is the prelude's: the
                // import says which declaration is meant. A file it does not import
                // directly (imports are not transitive, `docs/design/visibility.md`)
                // or a file of the tote or of a dependency it does not import says
                // nothing of what the name means here. The standard library's model of
                // a builtin is still the one the file reaches.
                let imports_prelude_file = imports.is_some()
                    && imported.is_empty()
                    && prelude.contains(n)
                    && prelude_declarers().get(n.as_str()).is_some_and(|files| {
                        files.iter().any(|f| {
                            let module = prelude_file_module(f);
                            reach_i.iter().any(|&j| {
                                modules[j] == module
                                    && imports_i.unwrap_or(&[]).contains(&j)
                                    && brings_i
                                        .get(&j)
                                        .is_none_or(|items| items.contains(&prelude_item(n)))
                            })
                        })
                    });
                // A prelude name a file this one reaches through its imports
                // declares is that file's: the imports say which declaration
                // is meant, as they do for any other name, and a name the
                // prelude takes on later does not change what it means.
                let reached_prelude: Vec<usize> = match imports {
                    Some(_) if imported.is_empty() && prelude.contains(n) => o
                        .iter()
                        .copied()
                        .filter(|&j| {
                            reach_i.contains(&j) && (!imports_prelude_file || is_std(&modules[j]))
                        })
                        .collect(),
                    _ => Vec::new(),
                };
                if imports_prelude_file && reached_prelude.is_empty() {
                    continue;
                }
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
                        let alone =
                            STANDALONE.with(|s| s.borrow().get(i).copied().unwrap_or(false));
                        o.iter()
                            .copied()
                            .filter(|&j| {
                                (!alone
                                    && same_tote(&modules[i], &modules[j])
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
                // (`std::text::Text::len` of `text_len`), and a file that reaches
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
                    Some(_) => o.iter().copied().filter(|j| reach_i.contains(j)).collect(),
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
                    if o.iter().all(|&j| bound_apart(n, j) && hidden_in(j))
                        && binds[i].contains(n.as_str())
                    {
                        unseen.insert(n.clone());
                        continue;
                    }
                    // A constructor of a type this file's macros make: read when they have run.
                    if makes_types[i] {
                        continue;
                    }
                    // No import reaches a declaration of the name: it is not
                    // visible here, whichever file of the program declares it.
                    if imports.is_some() {
                        names.insert(
                            n.clone(),
                            Meaning::NotImported(
                                modules[o[0]].clone(),
                                spellings(spell, modules, i, &o),
                            ),
                        );
                        continue;
                    }
                    o.clone()
                };
                let mut others: Vec<Full> = from.iter().flat_map(|&j| fulls(j, n)).collect();
                if through {
                    others.push(Full::prelude(bare(n)));
                }
                match others.as_slice() {
                    [one] => Meaning::To(one.clone()),
                    _ => Meaning::Ambiguous(others),
                }
            };
            names.insert(n.clone(), meaning);
        }
        // A constructor written with its type (`U8::Mk`) whose type a file
        // this one does not reach declares: the type's name alone is not
        // enough, since a module of that name may be reached (`std::secret`
        // adds `U8::wrap`), and the constructor is what the file did not
        // import.
        if imports.is_some() {
            let declares = |k: usize, ty: &str, c: &str| {
                shared[k]
                    .get(c)
                    .is_some_and(|types| types.iter().any(|t| t == ty))
                    || ctor_type[k].get(c).is_some_and(|t| t == ty)
            };
            for j in (0..files.len()).filter(|&j| j != i && !reach_i.contains(&j)) {
                let pairs = shared[j]
                    .iter()
                    .flat_map(|(c, tys)| tys.iter().map(move |t| (t.as_str(), c.as_str())))
                    .chain(ctor_type[j].iter().map(|(c, t)| (t.as_str(), c.as_str())));
                for (ty, c) in pairs {
                    let key = format!("{ty}{SEPARATOR}{c}");
                    if names.contains_key(&key)
                        || !uses[i].contains(&key)
                        || prelude.contains(&key)
                        || std::iter::once(i)
                            .chain(reach_i.iter().copied())
                            .any(|k| declares(k, ty, c))
                    {
                        continue;
                    }
                    names.insert(
                        key,
                        Meaning::NotImportedCtor(
                            modules[j].clone(),
                            spelling(spell, modules, i, j),
                        ),
                    );
                }
            }
        }
        for (name, effect_owners) in owners.iter().filter(|(name, _)| name.starts_with(EFFECT)) {
            for &owner in effect_owners {
                if imports.is_some() && owner != i && !reach_i.contains(&owner) {
                    for full in fulls(owner, name) {
                        names.insert(
                            format!("{EFFECT}{}", full.as_str()),
                            Meaning::NotImported(
                                modules[owner].clone(),
                                vec![spelling(spell, modules, i, owner)],
                            ),
                        );
                    }
                }
            }
        }
        // A prelude file that is not core is seen through its import only
        // (`import std::builtin::os`): a name only it declares, written
        // without the import, is not visible; with the import, a file's own
        // or imported declaration of the same name is ambiguous with it.
        if imports.is_some() {
            // A preceding binding pass may have given a constructor its owner's
            // qualified name. Its source alias remains visible with that owner.
            let mut visible_constructors = HashSet::new();
            for j in std::iter::once(i).chain(reach_i.iter().copied()) {
                for statement in &files[j] {
                    ctors_of(statement, &mut |family, constructor| {
                        if j == i || (!private_to(i, j, family) && !unlisted_in(j, short(family))) {
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
            // A file that sees the prelude still sees the core names of a prelude file it
            // imports as that file's: they meet the other files it imports on equal terms.
            let core = core_prelude().iter();
            for (n, files) in hidden_prelude().iter().chain(core) {
                // An import with a list brings only what it lists.
                let granted = files.iter().any(|f| {
                    let module = prelude_file_module(f);
                    reach_i.iter().any(|&j| {
                        modules[j] == module
                            && brings_i
                                .get(&j)
                                .is_none_or(|items| items.contains(&prelude_item(n)))
                    })
                });
                // A core name a file this one reaches declares (the standard library's model
                // of a builtin) means that declaration, as it does where the prelude is seen;
                // unless the file imports the prelude file that declares it too: two files
                // it imports declare the name, and neither wins (Safe by Default).
                // The file's own declaration (`std::uint`'s model `U64::and` of the builtin)
                // is the one it means, imported prelude file or not.
                let declares_here = owners.get(n).is_some_and(|o| o.contains(&i));
                if !hidden_prelude().contains_key(n)
                    && names.contains_key(n)
                    && (!granted || declares_here)
                {
                    continue;
                }
                if !bare_at(i) && !hidden_prelude().contains_key(n) && !granted {
                    continue;
                }
                let prelude_full = Full::prelude(bare(n));
                match (names.get_mut(n), granted) {
                    // The file imports the prelude file that declares it: a macro of
                    // this file that writes it means that declaration wherever it is
                    // expanded, the importer of the macro's file not importing it.
                    (None, true) => {
                        plain.insert(n.clone(), n.clone());
                    }
                    (None, false) if own.contains(n.as_str()) => {}
                    // A declaration of that name the file's imports bring (`U64` of
                    // `import "uint.taut" { U64 }`) is the one the name means.
                    (None, false)
                        if owners.get(n).is_some_and(|all| {
                            all.iter().any(|&j| {
                                reach_i.contains(&j) && !private_to(i, j, n) && !unlisted_in(j, n)
                            })
                        }) => {}
                    // A module the file's imports declare by that name (`Ct` of
                    // `std::secret`): its functions are the ones the name means.
                    (None, false)
                        if module_members.get(n.as_str()).is_some_and(|members| {
                            members.iter().any(|(member, all)| {
                                all.iter().any(|&j| {
                                    reach_i.contains(&j)
                                        && !private_to(i, j, member)
                                        && !unlisted_in(j, member)
                                })
                            })
                        }) => {}
                    // A constructor the file sees by that name (`I64` of a type `Width`)
                    // is read as that constructor, as it is where the prelude file is
                    // imported.
                    (None, false) if visible_constructors.contains(n.as_str()) => {}
                    // The file imports the prelude file, whose list does not write the name:
                    // the list is what the error says (`check_import_lists`), not that the
                    // file does not import it.
                    (None, false)
                        if files.iter().any(|f| {
                            let module = prelude_file_module(f);
                            reach_i.iter().any(|&j| modules[j] == module)
                        }) => {}
                    (None, false) => {
                        names.insert(
                            n.clone(),
                            Meaning::NotImported(
                                prelude_file_module(&files[0]),
                                vec![prelude_file_module(&files[0])],
                            ),
                        );
                    }
                    (Some(Meaning::To(to)), true) => {
                        let both = vec![to.clone(), prelude_full];
                        names.insert(n.clone(), Meaning::Ambiguous(both));
                        prelude_files.insert(n.clone(), prelude_file_module(&files[0]));
                    }
                    (Some(Meaning::Ambiguous(all)), true) => {
                        // Once, however many ways the file sees the prelude's.
                        if !all.contains(&prelude_full) {
                            all.push(prelude_full);
                        }
                        prelude_files.insert(n.clone(), prelude_file_module(&files[0]));
                    }
                    _ => {}
                }
            }
        }
        Env {
            names,
            unseen,
            plain,
            declares,
            prelude_files,
        }
    };
    for i in 0..files.len() {
        let e = env(
            i,
            &reach[i],
            imports.map(|im| im[i].as_slice()),
            &brings[i],
        );
        all_names.push(e.names);
        all_unseen.push(e.unseen);
        all_plain.push(e.plain);
        all_declares.push(e.declares);
        all_prelude_files.push(e.prelude_files);
        // Each declaration that imports at the head of its body sees what those
        // imports bring as well, in that body only.
        let mut here = Vec::new();
        for (k, statement) in files[i].iter().enumerate() {
            let heads: Vec<&ImportList> = scoped::head_imports(statement)
                .iter()
                .filter_map(|import| {
                    let at = scoped::import_span(import);
                    file_lists(i).find(|l| l.body && l.span == at)
                })
                .collect();
            if heads.is_empty() {
                continue;
            }
            let mut reach_k = reach[i].clone();
            let mut imports_k: Vec<usize> = imports.map(|im| im[i].clone()).unwrap_or_default();
            for l in &heads {
                if let Some(j) = l.target.filter(|&j| j != i) {
                    reach_k.insert(j);
                    if !imports_k.contains(&j) {
                        imports_k.push(j);
                    }
                }
            }
            let brings_k = brought(file_lists(i).filter(|l| !l.body).chain(heads.iter().copied()));
            let mut e = env(i, &reach_k, imports.map(|_| imports_k.as_slice()), &brings_k);
            // A name the file declares and a body's import brings too is ambiguous in the
            // body, as a name two imports of the file bring is: neither is taken.
            for (n, all) in &owners {
                if !all.contains(&i) {
                    continue;
                }
                let brought_too: Vec<usize> = all
                    .iter()
                    .copied()
                    .filter(|&j| {
                        j != i
                            && reach_k.contains(&j)
                            && !reach[i].contains(&j)
                            && !private_to(i, j, n)
                            && !unlisted_with(&brings_k, j, n)
                    })
                    .collect();
                if brought_too.is_empty() {
                    continue;
                }
                let mut both = fulls(i, n);
                both.extend(brought_too.iter().flat_map(|&j| fulls(j, n)));
                e.names.insert(n.clone(), Meaning::Ambiguous(both));
            }
            here.push(Scoped {
                statement: k,
                env: e,
                reach: reach_k,
                brings: brings_k,
                lists: heads.into_iter().cloned().collect(),
            });
        }
        all_scoped.push(here);
    }
    // The global names each file writes, as read, when its import lists are checked.
    let used: Vec<std::cell::RefCell<Vec<SourceUse>>> =
        (0..files.len()).map(|_| Default::default()).collect();
    // What the short and full names of the file `i` mean, by the full names they are
    // renamed to, where its names mean `names` and it sees the files `reach_i`.
    let seeing_of = |i: usize,
                     names: &HashMap<String, Meaning>,
                     plain: HashMap<String, String>,
                     reach_i: &HashSet<usize>,
                     brings_i: &HashMap<usize, HashSet<String>>|
     -> HashMap<String, String> {
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
            implicit
                .chain(names.iter().flat_map(|(n, m)| {
                    match m {
                        Meaning::To(to) => vec![
                            (n.clone(), to.as_str().to_string()),
                            (to.as_str().to_string(), to.as_str().to_string()),
                        ],
                        // A shared short spelling hides neither declaration's
                        // full path from the file's reference environment.
                        Meaning::Ambiguous(all) => all
                            .iter()
                            .map(|full| (full.as_str().to_string(), full.as_str().to_string()))
                            .collect(),
                        Meaning::NotImported(..) | Meaning::NotImportedCtor(..) => Vec::new(),
                    }
                }))
                // A module function of the prelude that no file this one
                // reaches models (`Text::of_nat` without `std::text`) is the
                // builtin: a macro of the file that writes it means that,
                // wherever it is expanded ([`split_models`]).
                .chain(
                    runtime_module_fns()
                        .iter()
                        .filter(|_| keep_prelude && imports.is_some())
                        .filter(|n| {
                            !matches!(
                                names.get(*n),
                                Some(
                                    Meaning::NotImported(..)
                                        | Meaning::NotImportedCtor(..)
                                        | Meaning::Ambiguous(_)
                                )
                            )
                        })
                        .filter(|n| {
                            !std::iter::once(&i)
                                .chain(reach_i)
                                .any(|&j| modelled[j].contains(*n))
                        })
                        .map(|n| (n.clone(), format!("{PRELUDE_MODULE}{SEPARATOR}{n}"))),
                )
                .chain(written.iter().filter_map(|(owner, name)| {
                    let local = bare(name)
                        .strip_prefix(&format!("{}{SEPARATOR}", modules[*owner]))
                        .unwrap_or(bare(name));
                    (*owner == i
                        || (reach_i.contains(owner)
                            && !private_to(i, *owner, name)
                            && !unlisted_with(brings_i, *owner, local)))
                    .then(|| (name.clone(), name.clone()))
                }))
                .chain(plain)
                .collect()
    };
    // The uses of the body of each declaration that imports at the head of its body,
    // by file, as `all_scoped` holds the declarations.
    let mut scoped_used: Vec<Vec<Vec<SourceUse>>> = Vec::new();
    for (i, stmts) in files.iter_mut().enumerate() {
        let plain = std::mem::take(&mut all_plain[i]);
        macro_rules! renamer {
            ($env:expr, $errors:expr, $missing:expr, $used:expr) => {
                Renamer {
                    names: &$env.names,
                    by_full: &by_full,
                    by_target: Default::default(),
                    module_fns: &module_fns,
                    module_paths: None,
                    ctors: &ctors,
                    nullary: &nullary,
                    args: &args,
                    fields: &fields,
                    unseen: &$env.unseen,
                    locals: Default::default(),
                    typed: Default::default(),
                    returns: Default::default(),
                    errors: $errors,
                    sealed: None,
                    seen: None,
                    unsure: None,
                    missing: Some(($missing, i)),
                    declares: Some(&$env.declares),
                    prelude_files: Some(&$env.prelude_files),
                    keep_prelude,
                    used: lists.map(|_| $used),
                    global_texts: Default::default(),
            quoting: Default::default(),
                    owner: Default::default(),
                }
            };
        }
        let file_env = Env {
            names: std::mem::take(&mut all_names[i]),
            unseen: std::mem::take(&mut all_unseen[i]),
            plain: HashMap::new(),
            declares: std::mem::take(&mut all_declares[i]),
            prelude_files: std::mem::take(&mut all_prelude_files[i]),
        };
        let r = renamer!(file_env, &errors, &missing, &used[i]);
        if lists.is_some() {
            let mut calls = false;
            for s in stmts.iter_mut() {
                super::walk::stmt(s, &mut |t| calls |= calls_syn_global(t));
            }
            r.global_texts.set(calls);
        }
        let mut body_uses = Vec::new();
        for (k, s) in stmts.iter_mut().enumerate() {
            let Some(sc) = all_scoped[i].iter().find(|sc| sc.statement == k) else {
                r.top(s);
                continue;
            };
            // The signature is read as the file reads it; the body sees the body's
            // imports too.
            let mut signature = s.clone();
            if let Some(b) = scoped::body_mut(&mut signature) {
                *b = SurfaceTerm::new(TermKind::Block(Vec::new()), b.span);
            }
            r.top(&mut signature);
            let within = scoped::body_span(s).unwrap_or_default();
            let inside = |at: &Span| within.start <= at.start && at.end <= within.end;
            let body_errors = std::cell::RefCell::new(Vec::new());
            let body_missing = std::cell::RefCell::new(Vec::new());
            let body_used = std::cell::RefCell::new(Vec::new());
            let body = renamer!(sc.env, &body_errors, &body_missing, &body_used);
            body.global_texts.set(r.global_texts.get());
            body.top(s);
            errors.borrow_mut().extend(
                body_errors
                    .into_inner()
                    .into_iter()
                    .filter(|(_, at)| inside(at)),
            );
            missing.borrow_mut().extend(
                body_missing
                    .into_inner()
                    .into_iter()
                    .filter(|m: &MissingImport| inside(&m.at)),
            );
            let uses: Vec<SourceUse> = body_used
                .into_inner()
                .into_iter()
                .filter(|u| inside(&u.span))
                .collect();
            used[i].borrow_mut().extend(uses.iter().cloned());
            body_uses.push(uses);
            let body = scoped::body(s).cloned();
            *s = signature;
            if let (Some(b), Some(body)) = (scoped::body_mut(s), body) {
                *b = body;
            }
        }
        scoped_used.push(body_uses);
        let mut visible = seeing_of(i, &file_env.names, plain, &reach[i], &brings[i]);
        // What a declaration's body sees through its own imports is seen by the passes
        // that bind the file's names: this pass has held every other use to the file's.
        let mut here = FileScopes::default();
        if !all_scoped[i].is_empty() {
            here.file = Some(visible.clone());
        }
        for sc in &mut all_scoped[i] {
            let plain = std::mem::take(&mut sc.env.plain);
            let inner = seeing_of(i, &sc.env.names, plain, &sc.reach, &sc.brings);
            for (n, to) in &inner {
                visible.entry(n.clone()).or_insert_with(|| to.clone());
            }
            if let Some(name) = files_decl_name(&stmts[sc.statement]) {
                here.declarations.push((name, inner));
            }
        }
        scoped_out.push(here);
        seeing.push(visible);
    }
    // Capture source uses before expansion. A generated reference belongs to the
    // macro definition's imports; it does not add an import use at the call site.
    if let Some(quoted) = quoted {
        let mut quoted = quoted.borrow_mut();
        quoted.resize(files.len(), Vec::new());
        for (q, u) in quoted.iter_mut().zip(&used) {
            if keep_prelude {
                // What lowering introduced (`for`) is kept: the source never wrote it.
                let lowered: Vec<SourceUse> = q.iter().filter(|u| u.keeps_only).cloned().collect();
                *q = u.take();
                q.extend(lowered);
            } else {
                u.borrow_mut().extend(q.iter().cloned());
            }
        }
    }
    let mut errors = errors.into_inner();
    if let Some(lists) = lists.filter(|_| !keep_prelude) {
        for (i, file_lists) in lists.iter().enumerate().take(files.len()) {
            let at_top: Vec<ImportList> = file_lists.iter().filter(|l| !l.body).cloned().collect();
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
                &at_top,
                &used[i].borrow(),
                &mut errors,
                warnings,
                fixes,
            );
            // The imports at the head of a declaration's body, held to what that body uses.
            for (sc, uses) in all_scoped[i].iter().zip(&scoped_used[i]) {
                let mut seen = reach.clone();
                seen[i] = sc.reach.clone();
                check_import_lists(
                    bare_at(i),
                    i,
                    files,
                    modules,
                    &owners,
                    &seen,
                    &private,
                    &ctor_type,
                        &language_full,
                    &sc.lists,
                    uses,
                    &mut errors,
                    warnings,
                    fixes,
                );
            }
        }
    }
    flattened.extend(errors);
    flattened.extend(super::loops::lower_loops(files));
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
    // The prelude's structs (`SynFn` of `std::builtin::macro`) are not among
    // `files`: a literal names them as it names a struct of its own, bare or
    // by the prelude file's module. A struct of `files` comes after them, so a
    // name both declare is the program's.
    static PRELUDE: OnceLock<HashMap<String, Vec<String>>> = OnceLock::new();
    let mut fields = PRELUDE
        .get_or_init(|| {
            let mut out = HashMap::new();
            let texts = std::iter::once(("", crate::nibstd::KERNEL)).chain(
                crate::nibstd::PRELUDE_FILES
                    .iter()
                    .map(|(path, text)| (prelude_stem(path), *text)),
            );
            for (stem, text) in texts {
                if let Ok(program) = super::program::prelude_unresolved(text) {
                    let module = if stem.is_empty() {
                        String::new()
                    } else {
                        prelude_file_module(stem)
                    };
                    structs(&program.stmts, &module, &mut out);
                }
            }
            out
        })
        .clone();
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
                                stack: None,
                                name: RECORD_BASE.into(),
                                ty: None,
                                value: *b,
                                borrow: false,
                                borrow_mut: false,
                unused: None
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

/// A file may not declare a name its imports bring: the file's declaration would quietly take the
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
    unlisted: &dyn Fn(usize, usize, &str) -> bool,
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
                    o.iter().copied().find(|&j| {
                        j != i
                            && reach[i].contains(&j)
                            && !private[j].contains(n)
                            && !unlisted(i, j, n)
                    })
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
        // A struct or an enum, with the variants that clash, is the file's
        // own: without its span the error fell on the first file read.
        Stmt::Struct(d) | Stmt::Enum(d) => d.span,
        Stmt::Fn(f) => f.span,
        Stmt::Reexport { span, .. } => *span,
        Stmt::Class(c) => c.span,
        Stmt::Mutual { span, .. } | Stmt::Extern { span, .. } => *span,
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
            "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "uhost", "nat", "I8", "I16", "I32", "I64",
            "U8", "U16", "U32", "U64", "UHost", "Nat", "UInt", "SInt",
        ];
        let text = width_families_as_words(&super::print::print_term(t.as_ref()?));
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
    // `UInt(8)` as the one word `UInt`: a family at a width is a number.
    fn width_families_as_words(text: &str) -> String {
        let mut out = text.to_string();
        for family in ["UInt(", "SInt("] {
            let mut done = String::new();
            let mut rest = out.as_str();
            while let Some(at) = rest.find(family) {
                let after = &rest[at + family.len()..];
                let digits = after.chars().take_while(|c| c.is_ascii_digit()).count();
                done.push_str(&rest[..at + family.len() - 1]);
                if digits > 0 && after[digits..].starts_with(')') {
                    rest = &after[digits + 1..];
                } else {
                    done.push('(');
                    rest = after;
                }
            }
            done.push_str(rest);
            out = done;
        }
        out
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
    // The types a file declares: `Slots::get` in a file that declares a `Slots`
    // is a function of that type, not a model of the builtin of the same name.
    fn declared<'a>(s: &'a Stmt, out: &mut HashSet<&'a str>) {
        match s {
            Stmt::Struct(d) | Stmt::Enum(d) => {
                out.insert(d.name.as_str());
            }
            // `inductive struct`: one constructor, named as the type.
            Stmt::Inductive(i) if i.constructors.len() == 1 && i.constructors[0].name == i.name => {
                out.insert(i.name.as_str());
            }
            Stmt::Attributed { stmt, .. } => declared(stmt, out),
            _ => {}
        }
    }
    let mut errors = Vec::new();
    for (stmts, module) in files.iter().zip(modules) {
        if !is_std(module) {
            continue;
        }
        let mut own = HashSet::new();
        stmts.iter().for_each(|s| declared(s, &mut own));
        // Written in full, as the file's other names are.
        let own: HashSet<&str> = own
            .into_iter()
            .map(|n| n.strip_prefix(module.as_str()).and_then(|n| n.strip_prefix(SEPARATOR)).unwrap_or(n))
            .collect();
        let mut found = Vec::new();
        stmts.iter().for_each(|s| fns(s, "", &mut found));
        for (name, f) in found {
            // The name in the file: a full name has the file's module before it.
            let name = name
                .strip_prefix(module.as_str())
                .and_then(|n| n.strip_prefix(SEPARATOR))
                .unwrap_or(&name)
                .to_string();
            // The model of a `uhost` operation takes the proof (and the bound)
            // that the builtin leaves out, so it differs from the builtin by
            // design (`std/uhost.taut`).
            if name.starts_with("UHost::") {
                continue;
            }
            if name.split_once(SEPARATOR).is_some_and(|(ty, _)| own.contains(ty)) {
                continue;
            }
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
            by_target: Default::default(),
            module_fns: &module_fns,
            module_paths: None,
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
            unsure: None,
            missing: None,
            declares: None,
            prelude_files: None,
            keep_prelude: false,
            used: None,
            global_texts: Default::default(),
            quoting: Default::default(),
            owner: Default::default(),
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
    effects: HashMap<String, (usize, Vis, Option<(super::TermId, Vis)>)>,
    /// Each class by its last name segment, with every file that declares
    /// one of that name.
    classes: HashMap<String, Vec<(usize, Vis)>>,
    /// Each field name, with every type that has it: a field of a struct or
    /// an enum, or a parameter of an inductive type's constructor.
    fields: HashMap<String, Vec<(usize, Vis, String)>>,
    modules: Vec<String>,
    /// Field reads are left to the check after the macros: before them, a
    /// type a macro declares (`syntax!`) is not seen, so a field name alone
    /// may name only the sealed type of another file.
    fields_later: bool,
    /// The types and classes, which may own a path `T::C`.
    types: HashSet<String>,
}

const PRELUDE_FILE: usize = usize::MAX;

/// The full name this pass gives a declaration (`app::src::main::Open`,
/// `std::prelude::Array`). A short name is never one: the two are kept
/// apart by their types, so that a declaration is never matched by the
/// last segment of its name.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Full(String);

impl Full {
    fn prelude(n: &str) -> Self {
        Full(format!("{PRELUDE_MODULE}{SEPARATOR}{n}"))
    }

    fn as_str(&self) -> &str {
        &self.0
    }

    fn into_string(self) -> String {
        self.0
    }
}

/// A table keyed by full names is read with the name a file writes, which is full there.
impl std::borrow::Borrow<str> for Full {
    fn borrow(&self) -> &str {
        &self.0
    }
}

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
            // An extern function is seen as a function is: in its file
            // unless it is written `pub`.
            Stmt::Extern { fns, .. } => {
                for f in fns {
                    insert(&mut self.names, &f.name, f.vis);
                }
            }
            Stmt::Theorem(d) | Stmt::Def(d) => insert(&mut self.names, &d.name, d.vis),
            Stmt::Class(c) => {
                self.types.insert(c.name.to_string());
                insert(&mut self.names, &c.name, c.vis);
                self.classes
                    .entry(last_segment(&c.name).to_string())
                    .or_default()
                    .push((file, c.vis));
            }
            Stmt::Struct(d) | Stmt::Enum(d) => {
                self.types.insert(d.name.to_string());
                insert(&mut self.names, &d.name, d.vis);
                for c in &d.constructors {
                    self.ctors.entry(c.name.to_string()).or_insert((
                        file,
                        d.vis,
                        d.name.to_string(),
                    ));
                    for (f, _) in &c.fields {
                        let Some(f) = f else { continue };
                        // `w.T::f` names the field of the struct `T` itself.
                        // A struct with a `coerce` field is read through it
                        // where `w.f` is written, so its own fields are seen
                        // only by that name.
                        let mut keys = vec![format!("{}::{f}", last_segment(&d.name))];
                        if d.coerce.is_none() {
                            keys.push(f.to_string());
                        }
                        for key in keys {
                            self.fields.entry(key).or_default().push((
                                file,
                                d.vis,
                                d.name.to_string(),
                            ));
                        }
                    }
                }
            }
            Stmt::Inductive(d) => {
                self.types.insert(d.name.to_string());
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
                    .or_insert((file, e.vis, e.module_scope));
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
            fields_later: false,
            types: HashSet::new(),
        };
        for text in [crate::nibstd::PRELUDE, crate::nibstd::KERNEL] {
            if let Ok(program) = super::program::prelude_as_written(text) {
                for s in &program.stmts {
                    seen.add(s, PRELUDE_FILE);
                }
            }
        }
        // Its `pub` names are seen everywhere; the others are its own.
        seen.names.retain(|_, (_, vis)| *vis == Vis::Private);
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
    visibility(files, modules, false, false).0
}

/// [`sealed_visibility`] on what the files write, before the macros run. A
/// field read is not judged here: the types a macro declares are not seen
/// yet, and [`sealed_visibility_typed`] reads every field again after the
/// macros, with them.
pub fn written_visibility(files: &[Vec<Stmt>], modules: &[String]) -> Vec<(Message, Span)> {
    visibility(files, modules, false, true).0
}

/// A field read `x.f` where another file declares a type with the field `f`
/// without `pub(open)` and a type seen here has a field `f` too: the name does
/// not tell which, the type of `x` does. `sealed` holds each type it would be
/// sealed for, by its full name, with the error to give for it: two files may
/// each declare a private type of the same short name, and only the one the
/// read's value has is sealed.
#[derive(Debug, Clone)]
pub struct SealedRead {
    pub span: Span,
    pub sealed: Vec<(String, Message)>,
}

/// [`sealed_visibility`], and the reads its names alone do not settle, for the
/// caller to settle by the types the checker gives (`TypeReport::field_owners`).
pub fn sealed_visibility_typed(
    files: &[Vec<Stmt>],
    modules: &[String],
) -> (Vec<(Message, Span)>, Vec<SealedRead>) {
    visibility(files, modules, false, false)
}

/// Checks source aliases before expansion replaces their uses with member effects.
pub fn effect_set_visibility(files: &[Vec<Stmt>], modules: &[String]) -> Vec<(Message, Span)> {
    visibility(files, modules, true, false).0
}

fn visibility(
    files: &[Vec<Stmt>],
    modules: &[String],
    aliases_only: bool,
    fields_later: bool,
) -> (Vec<(Message, Span)>, Vec<SealedRead>) {
    let unsure = std::cell::RefCell::new(Vec::new());
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
        fields_later,
        types: HashSet::new(),
    };
    for (i, stmts) in files.iter().enumerate() {
        for s in stmts {
            if !aliases_only || matches!(s, Stmt::Effect(e) if e.set.is_some()) {
                seen.add(s, i);
            }
        }
    }
    for s in files.iter().flatten() {
        if let Stmt::Reexport {
            aliases: Some(aliases),
            ..
        } = s
        {
            for alias in aliases.iter().filter(|alias| alias.effect) {
                if let Some(&(file, visibility, scope)) = seen.effects.get(&alias.target) {
                    let visibility = scope.map_or(visibility, |(_, member)| member);
                    seen.effects
                        .insert(alias.name.clone(), (file, visibility, scope));
                }
            }
        }
    }
    // A name the prelude declares stays the prelude's, wherever else it is declared.
    let prelude_names = prelude_names();
    let own: HashSet<String> = seen.names.keys().cloned().collect();
    seen.names
        .retain(|n, _| !prelude_names.contains(n.as_str()));
    // What the prelude keeps to its files, unless a file declares the name.
    if !aliases_only {
        for (n, at) in &prelude.names {
            if !own.contains(n) {
                seen.names.insert(n.clone(), *at);
            }
        }
    }
    let (names, by_full, ctors) = (HashMap::new(), HashMap::new(), HashMap::new());
    let nullary = HashSet::new();
    // The functions of the modules (`Reading::title`): the owner of such a path names the
    // module, so a private type of another file with the module's name is not what it reads.
    let module_fns = HashSet::new();
    let module_paths: HashSet<String> = files
        .iter()
        .flat_map(|stmts| {
            let mut names = super::modules::declared(stmts);
            names.extend(super::modules::declared_flat(stmts));
            names.retain(|n| n.contains(SEPARATOR));
            names
        })
        .collect();
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
            by_target: Default::default(),
            module_fns: &module_fns,
            module_paths: Some(&module_paths),
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
            unsure: Some(&unsure),
            missing: None,
            declares: None,
            prelude_files: None,
            keep_prelude: false,
            used: None,
            global_texts: Default::default(),
            quoting: Default::default(),
            owner: Default::default(),
        };
        // The walk renames nothing with empty tables; it runs on a copy so
        // that it only reads.
        for s in stmts.clone().iter_mut() {
            r.top(s);
        }
    }
    (errors.into_inner(), unsure.into_inner())
}

/// Each place a program writes the prelude's `Pair` by its name: its type, its
/// constructor, its record or a declaration made for it (`Pair::rec`). A product is
/// written `A × B` and `#(a, b)`, and taken apart by `#(…)`, by its members' types or by
/// `.fst` and `.snd`; the `Pair` it is read to is the checker's, never the program's.
/// Runs on the output of `files_before_macros`, so a program's own `Pair` is not the
/// prelude's.
pub fn written_pairs(files: &[Vec<Stmt>]) -> Vec<(Message, Span)> {
    // Runs on the output of `files_before_macros`, whose names are spelled in full: the
    // prelude's `Pair` is `std::prelude::Pair`, a program's own is under the program's
    // module. A product the reader writes names `Pair` by the library's own reference, not
    // by a spelling, so it is never taken for a `Pair` written by its name.
    // A file that declares nothing of its own named `Pair` writes the prelude's by the
    // plain spelling.
    let own_pair = files.iter().flatten().any(|s| {
        crate::bindings::declared_names(std::slice::from_ref(s))
            .iter()
            .any(|n| matches!(n, Name::Spelled(t) if t == "Pair" || t.starts_with("Pair::")))
    });
    let is_pair = move |n: &Name| -> bool {
        let Name::Spelled(text) = n else {
            return false;
        };
        let rest = match text
            .strip_prefix(PRELUDE_MODULE)
            .and_then(|r| r.strip_prefix(SEPARATOR))
        {
            Some(rest) => rest,
            None if !own_pair => text.as_str(),
            None => return false,
        };
        rest == "Pair" || PAIR_DECLARATIONS.iter().any(|d| rest == format!("Pair{d}"))
    };
    fn pattern(p: &Pattern, is_pair: &impl Fn(&Name) -> bool) -> bool {
        match p {
            Pattern::Ctor { name, args } => {
                is_pair(name) || args.iter().any(|a| pattern(a, is_pair))
            }
            Pattern::Record { name, fields } => {
                is_pair(name) || fields.iter().any(|(_, q)| pattern(q, is_pair))
            }
            Pattern::Bind { .. }
            | Pattern::Typed { .. }
            | Pattern::Wild
            | Pattern::Int(_)
            | Pattern::Bool(_)
            | Pattern::Text(_)
            | Pattern::Other(_) => false,
        }
    }
    let mut out = Vec::new();
    for s in files.iter().flatten() {
        let mut s = s.clone();
        super::walk::stmt(&mut s, &mut |t| {
            let written = match &*t.kind {
                TermKind::Var(n) => is_pair(n),
                TermKind::Record { name, .. } => is_pair(name),
                TermKind::Match { arms, .. } => arms.iter().any(|a| pattern(&a.pattern, &is_pair)),
                TermKind::Handle { handlers, .. } => handlers.iter().any(|h| match h {
                    Handler::Return { pattern: p, .. } => pattern(p, &is_pair),
                    Handler::Operation { patterns, .. } => {
                        patterns.iter().any(|p| pattern(p, &is_pair))
                    }
                }),
                _ => false,
            };
            if written {
                out.push((msg!("surface-pair-written"), t.span));
            }
        });
    }
    out
}

/// What is declared for `Pair` beside it, each after its name.
const PAIR_DECLARATIONS: &[&str] = &[
    "::Mk",
    "::fst",
    "::snd",
    "::rec",
    "::ind",
    "::noconf",
    "::nc",
    "::nc_diag",
];

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
        fields_later: false,
        types: HashSet::new(),
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
            Pattern::Bind { name: n, .. } | Pattern::Typed { name: n, .. } => {
                out.insert(n.to_string());
            }
            Pattern::Ctor { args, .. } => args.iter().for_each(|a| of(a, out)),
            Pattern::Record { fields, .. } => fields.iter().for_each(|(_, a)| of(a, out)),
            Pattern::Wild
            | Pattern::Int(_)
            | Pattern::Bool(_)
            | Pattern::Text(_)
            | Pattern::Other(_) => {}
        }
    }
    fn fors(s: &Stmt, out: &mut HashSet<String>) {
        match s {
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                items.iter().for_each(|i| fors(i, out));
            }
            Stmt::Attributed { stmt, .. } => fors(stmt, out),
            _ => {
                super::walk::values_stmt(s, &mut |n| {
                    if let super::walk::Node::Stmt(Stmt::For { pattern, .. }) = n {
                        of(pattern, out);
                    }
                });
            }
        }
    }
    let mut out = HashSet::new();
    for s in stmts {
        fors(s, &mut out);
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
            // A row's entries are names too (`! {std::builtin::par::Host}`).
            super::references::statement(&mut s, &mut |n| {
                if n.spelling().is_some_and(|n| {
                    [PRELUDE_MODULE, BUILTIN_MODULE].iter().any(|m| {
                        n.strip_prefix(m).is_some_and(|r| r.starts_with(SEPARATOR))
                    })
                }) {
                    found = true;
                }
            });
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

/// A name the file does not see that files declare: `import spelling`, for any of
/// the spellings, in the file `file` makes it seen. `at` is where the name is written.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MissingImport {
    pub file: usize,
    pub at: Span,
    /// How the file imports each file that declares the name, in the order of the files.
    pub spellings: Vec<String>,
}

enum Meaning {
    To(Full),
    Ambiguous(Vec<Full>),
    /// Declared by this file of the standard library only, which the file
    /// does not import, with how the file imports it (`std::os`,
    /// `"setoid.taut"`, `algebra::proof::Setoid`).
    /// The files that declare it, each by how the file imports it: any one import makes it
    /// seen. The module is the first file's.
    NotImported(String, Vec<String>),
    /// A constructor written with its type (`U8::Mk`) whose type a file the
    /// file does not import declares: the file, and how to import it.
    NotImportedCtor(String, String),
}

struct Renamer<'a> {
    /// What the source spellings in this file mean.
    names: &'a HashMap<String, Meaning>,
    by_full: &'a HashMap<Full, String>,
    /// The full names outside the prelude that `by_full` gives each name,
    /// made when a name is first recorded.
    by_target: std::cell::OnceCell<HashMap<String, Vec<Full>>>,
    /// The functions of the modules of the program, by their full names
    /// (`Bytes::values`): a module's name is not a type's, even where a type
    /// has that name and is renamed.
    module_fns: &'a HashSet<String>,
    /// For the visibility pass only: the module functions, whose path's owner names the
    /// module and not a private declaration of that name (`Reading::title`).
    module_paths: Option<&'a HashSet<String>>,
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
    /// Where the fields read whose names alone do not tell whether they are
    /// seen are kept ([`sealed_visibility_typed`]).
    unsure: Option<&'a std::cell::RefCell<Vec<SealedRead>>>,
    /// Where the names one import would make seen are written, and the file being read.
    missing: Option<(&'a std::cell::RefCell<Vec<MissingImport>>, usize)>,
    returns: std::cell::RefCell<Option<String>>,
    /// The full names the file's own declarations take, by their short
    /// names; `None` where this walk renames no declaration.
    declares: Option<&'a HashMap<String, Full>>,
    /// The prelude file (`std::builtin::par`) the file imports that makes a
    /// name ambiguous with the file's own or imported declaration of it.
    prelude_files: Option<&'a HashMap<String, String>>,
    /// Whether a full name of the prelude is kept as written
    /// (`files_before_macros`).
    keep_prelude: bool,
    /// Where the global names this file writes itself are kept, as read,
    /// when its import lists are checked ([`check_import_lists`]).
    used: Option<&'a std::cell::RefCell<Vec<SourceUse>>>,
    /// Whether the file calls `Syn::global`, whatever it is given: a macro's helper takes the
    /// name as a text (`fn call(name: Text, ..)` of `call("segments", ..)`), so every text the
    /// file writes that is a name it sees is held to read it as `Syn::global` would.
    global_texts: std::cell::Cell<bool>,
    /// How many quotes the name being read is in.
    quoting: std::cell::Cell<u32>,
    /// Reading the owner `T` of a path `T::C`: only a type can be one.
    owner: std::cell::Cell<bool>,
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
            let by_target = self.by_target.get_or_init(|| {
                let mut by_target: HashMap<String, Vec<Full>> = HashMap::new();
                for (full, target) in self.by_full {
                    // The prelude's names written in full by a builtin module
                    // (`std::builtin::os::print`) are the prelude's, as are
                    // those written under `std::prelude`.
                    if !full.as_str().starts_with(PRELUDE_MODULE)
                        && !bare(full.as_str()).starts_with(BUILTIN_MODULE)
                    {
                        by_target
                            .entry(target.clone())
                            .or_default()
                            .push(full.clone());
                    }
                }
                by_target
            });
            let path = match by_target.get(n).map(Vec::as_slice) {
                Some([full]) => full.as_str(),
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
    /// The laws of an instance read as its methods are: the names they use
    /// written in full (`Array::len` as `std::array::len`), since the kernel
    /// checks them away from the file's imports. A name left unread here is
    /// the kernel's to report, as for [`Self::record_laws`].
    fn qualify_laws(&self, laws: &mut [super::program::LawDecl]) {
        let errors = self.errors.borrow().len();
        let missing = self.missing.map(|(m, _)| m.borrow().len());
        for l in laws {
            let d = &mut l.theorem;
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

    /// Keeps, as a name the file uses, the literal `Syn::global` is given: a macro's output
    /// names a declaration visible in the macro's definition by it, so what brings it there
    /// is used (removing the import would leave the expansion with no such declaration).
    /// Reading it reports nothing: a name nothing binds is the expander's to report.
    fn record_global_literal(&self, written: &str, span: Span) {
        if self.used.is_none() || self.is_local(written) {
            return;
        }
        let errors = self.errors.borrow().len();
        let missing = self.missing.map(|(m, _)| m.borrow().len());
        let mut name = written.to_string();
        self.global(&mut name, span);
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
            Some(Meaning::NotImported(..) | Meaning::NotImportedCtor(..)) | None => n,
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
        if self.ctors.contains_key(means.as_str()) {
            return None;
        }
        let is_ctor = self
            .ctors
            .values()
            .any(|cs| cs.values().any(|v| v == means.as_str()));
        if !is_ctor {
            return None;
        }
        let full = format!("{PRELUDE_MODULE}{SEPARATOR}{n}");
        self.by_full.get(full.as_str())?;
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

    /// An entry of a row or of a set's members: the effect it names, and
    /// for a written application (`res(Pos)`, `∀ A. res(A)`) its argument
    /// terms, under the row's parameters.
    fn row_entry(&self, entry: &mut Name, span: Span) {
        match entry {
            Name::Written(written) => {
                let edited = std::cell::RefCell::new(None);
                self.scoped(|| {
                    self.bind(written.parameters());
                    *edited.borrow_mut() = Some(written.edited(
                        |head| self.effect(head, span),
                        |argument| self.term(argument),
                    ));
                });
                if let Some(edited) = edited.into_inner() {
                    *entry = Name::Written(Arc::new(edited));
                }
            }
            _ => entry.edit_spelling(|spelling| self.effect(spelling, span)),
        }
    }

    fn effect(&self, n: &mut String, span: Span) {
        if self.is_local(n) {
            return;
        }
        self.see(&format!("{EFFECT}{n}"), span);
        let mut key = format!("{EFFECT}{n}");
        if n.contains(SEPARATOR) {
            self.meaning(&mut key, span);
            self.record(&key, span);
            if let Some(to) = self.by_full.get(key.as_str()) {
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
        // `std::prelude::Text`, written where the bare name is ambiguous, is
        // the language's type, which keeps its bare name for the kernel.
        if let Some(t) = n
            .strip_prefix(PRELUDE_MODULE)
            .and_then(|r| r.strip_prefix(SEPARATOR))
            .filter(|t| LANGUAGE_TYPES.contains(t))
        {
            *n = t.to_string();
            return;
        }
        if n.contains(SEPARATOR) {
            if let Some(to) = self.by_full.get(n.as_str()) {
                *n = to.clone();
                return;
            }
            // A constructor of a type the file does not import: it is not
            // the one this name means, whatever the program declares.
            if matches!(
                self.names.get(n.as_str()),
                Some(Meaning::NotImportedCtor(..))
            ) {
                self.meaning(n, span);
                return;
            }
            if let Some((ty, ctor)) = n.rsplit_once(SEPARATOR) {
                // `T::C`, a constructor of the type `T`, written as the
                // constructor's name after this pass when that is not `C`
                // of the type named `T`.
                let mut to = ty.to_string();
                let outer = self.owner.replace(true);
                let before = self.errors.borrow().len();
                self.global(&mut to, span);
                self.owner.set(outer);
                // The owner of a module's function names the module, not a
                // declaration: a type or constructor of that name that is
                // ambiguous with it is not what the path says.
                if self.module_fns.contains(n.as_str())
                    || self.module_paths.is_some_and(|m| m.contains(n.as_str()))
                {
                    self.errors.borrow_mut().truncate(before);
                }
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
    fn ctors_of_one_file(&self, all: &[Full]) -> bool {
        let module = |f: &str| {
            let mut parts = f.rsplitn(3, SEPARATOR);
            let (_, _, m) = (parts.next()?, parts.next()?, parts.next()?);
            Some(m.to_string())
        };
        let is_ctor = |f: &Full| {
            self.ctors
                .values()
                .any(|cs| cs.values().any(|v| v == f.as_str()))
        };
        let Some(first) = all.first().and_then(|f| module(f.as_str())) else {
            return false;
        };
        all.len() > 1
            && all
                .iter()
                .all(|f| is_ctor(f) && module(f.as_str()).as_deref() == Some(first.as_str()))
    }

    fn meaning(&self, n: &mut String, span: Span) {
        let names = self.names;
        match names.get(n.as_str()) {
            Some(Meaning::To(to)) => *n = to.as_str().to_string(),
            Some(Meaning::Ambiguous(all)) => {
                let message = if LANGUAGE_TYPES.contains(&bare(n)) {
                    // The language's type and an imported declaration of its
                    // name: importing does not say which, the full name does.
                    msg!(
                        "surface-ambiguous-language-type",
                        name = bare(n),
                        names = names_and(all)
                    )
                } else if self.ctors_of_one_file(all) {
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
                } else if all.iter().any(|a| a.as_str().starts_with(PRELUDE_MODULE)) {
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
            // A name in a quote that no declaration visible at the definition
            // has is a free name of the quote, bound where the quote is
            // expanded (hygiene); a declaration of the program using the
            // macro that spells the same is not what it names.
            Some(Meaning::NotImported(..)) if self.quoting.get() > 0 => {}
            Some(Meaning::NotImported(module, spellings)) => {
                self.errors.borrow_mut().push((
                    msg!(
                        "surface-not-imported",
                        name = bare(n),
                        module = written(module),
                        spelling = spellings[0].as_str()
                    ),
                    span,
                ));
                if let Some((missing, file)) = self.missing {
                    missing.borrow_mut().push(MissingImport {
                        file,
                        at: span,
                        spellings: spellings.clone(),
                    });
                }
            }
            Some(Meaning::NotImportedCtor(module, spelling)) => {
                let message = if spelling.starts_with("std::") {
                    // Said as the kernel says of a name no file declares,
                    // with where the standard library has it.
                    msg!(
                        "surface-ctor-in-std",
                        name = written(n),
                        spelling = spelling.as_str()
                    )
                } else {
                    msg!(
                        "surface-ctor-not-imported",
                        name = written(n),
                        module = written(module),
                        spelling = spelling.as_str()
                    )
                };
                self.errors.borrow_mut().push((message, span));
            }
            None => {}
        }
    }

    fn see(&self, n: &str, span: Span) {
        let Some((seen, here)) = self.seen else {
            return;
        };
        // A free name of a quote is bound where the quote is expanded, not to a
        // declaration of another file that happens to be spelled the same.
        if self.quoting.get() > 0 {
            return;
        }
        // The owner of `T::C` is a type: a function of the same name, as a
        // macro's, is not what the path names.
        if self.owner.get() && !seen.types.contains(n) {
            return;
        }
        if let Some(&(file, Vis::Private)) = seen.names.get(n)
            && file != here
        {
            // The standard library's own declarations are not the
            // program's to open.
            let message = if file == PRELUDE_FILE {
                msg!("surface-private-std", name = short(n))
            } else {
                msg!("surface-private", name = short(n), file = seen.file(file))
            };
            self.errors.borrow_mut().push((message, span));
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
        if seen.fields_later {
            return;
        }
        // A base that is not a local (`C::member` of a class, or a value
        // declared at the top) may name a member rather than read a field:
        // the types tell which, so every sealed owner is left to them.
        let global = matches!(&*base.kind, TermKind::Var(b) if !self.is_local(b));
        // `w.m::T::f` is seen as `w.T::f` is.
        let key = match f.rsplitn(3, "::").collect::<Vec<_>>().as_slice() {
            [field, ty, _] => format!("{ty}::{field}"),
            _ => f.to_string(),
        };
        let Some(owners) = seen.fields.get(&key) else {
            return;
        };
        let seen_here = |&(file, vis, _): &(usize, Vis, String)| file == here || vis == Vis::Open;
        let message = |(file, _, ty): &(usize, Vis, String)| {
            msg!(
                "surface-sealed-field",
                field = f,
                ty = short(ty),
                file = seen.file(*file)
            )
        };
        if global || owners.iter().any(seen_here) {
            // `x.value` of an open type and of one sealed in another file:
            // the type of `x` tells which.
            if let Some(unsure) = self.unsure {
                let sealed: Vec<_> = owners
                    .iter()
                    .filter(|o| !seen_here(o))
                    .map(|o| (o.2.clone(), message(o)))
                    .collect();
                if !sealed.is_empty() {
                    unsure.borrow_mut().push(SealedRead { span, sealed });
                }
            }
            return;
        }
        self.errors.borrow_mut().push((message(&owners[0]), span));
    }

    fn see_perform(&self, op: &str, span: Span, permission: Option<super::TermId>) {
        let Some((seen, here)) = self.seen else {
            return;
        };
        let Some(&(file, vis, module)) = seen.effects.get(op) else {
            return;
        };
        let message = match module {
            Some((scope, Vis::Private)) if permission != Some(scope) => {
                Some(msg!("surface-module-member-private", name = op))
            }
            Some((scope, Vis::Handle)) if permission != Some(scope) => Some(msg!(
                "surface-sealed-perform",
                name = op
                    .rsplit(SEPARATOR)
                    .next()
                    .unwrap_or(op)
                    .split('#')
                    .next()
                    .unwrap_or(op)
            )),
            None if vis == Vis::Handle && file != here => {
                Some(msg!("surface-sealed-perform", name = short(op)))
            }
            _ => None,
        };
        if let Some(message) = message {
            self.errors.borrow_mut().push((message, span));
        }
    }

    /// `sealed_visibility`: an arm for the operation `op` outside the file
    /// that declares it, which lets other files answer it only with
    /// `pub(open)`.
    fn see_arm(&self, op: &str, span: Span) {
        let Some((seen, here)) = self.seen else {
            return;
        };
        if let Some(&(file, vis, module)) = seen.effects.get(op)
            && file != here
            && !matches!(
                module.map_or(vis, |(_, member)| member),
                Vis::Open | Vis::Handle
            )
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
            *n = to.as_str().to_string();
        } else if let Some(to) = self.declares.and_then(|d| d.get(n.as_str())) {
            // Ambiguous where it is written, the name is still the file's own
            // where it is declared.
            *n = to.as_str().to_string();
        }
    }

    fn top(&self, s: &mut Stmt) {
        match s {
            Stmt::Reexport {
                aliases: Some(aliases),
                ..
            } => {
                for alias in aliases {
                    for name in [&mut alias.name, &mut alias.target] {
                        if alias.effect {
                            let mut key = format!("{EFFECT}{name}");
                            self.rename_decl(&mut key);
                            *name = bare(&key).to_string();
                        } else {
                            self.rename_decl(name);
                        }
                    }
                }
            }
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
                    set.iter_mut().for_each(|n| self.row_entry(n, e.span));
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
                for parent in &mut c.parents {
                    parent
                        .class
                        .edit_spelling(|spelling| self.global(spelling, parent.span));
                    self.term(&mut parent.ty);
                    for argument in &mut parent.arguments {
                        self.term(argument);
                    }
                }
                for m in &mut c.methods {
                    self.scoped(|| self.function(m));
                }
                self.record_laws(&c.laws);
                class_laws_follow_rename(c);
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
                self.qualify_laws(&mut inst.laws);
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
            Stmt::Assign {
                name, value, place, ..
            } => {
                // The target of an assignment is read as any name is: a top-level
                // `var` of the file is renamed with its declaration, so a
                // declaration of another file spelled alike is not meant.
                let span = value.span;
                if !self.is_local(&name.to_string()) {
                    name.edit_spelling(|spelling| self.global_here(spelling, span));
                }
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
            Stmt::For { source, body, .. } => {
                self.term(source);
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
            Stmt::Loop { body } => self.term(body),
            Stmt::Break(Some(e)) => self.term(e),
            Stmt::Return(None)
            | Stmt::Break(None)
            | Stmt::Continue
            | Stmt::Reexport { .. }
            | Stmt::Import { .. }
            | Stmt::Syntax { .. }
            | Stmt::Other(..) => {}
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
                    self.term_of(t, Some("Type"));
                    self.bind_typed(n, t);
                }
                None => self.bind([n]),
            }
        }
        for t in f.param_types.iter_mut().skip(f.params.len()).flatten() {
            self.term(t);
        }
        if let Some(r) = &mut f.result {
            self.term_of(r, Some("Type"));
        }
        if let Some(effects) = &mut f.effects {
            effects.iter_mut().for_each(|e| self.row_entry(e, f.span));
        }
        // The row as written names the same effects as the row: each entry
        // is read as the one declaration it means, not kept as spelled.
        if let Some(entries) = &mut f.written_effects {
            for entry in entries {
                self.row_entry(&mut entry.name, entry.span);
            }
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
        // until expansion declares that type. A name a file it does not
        // import declares (`Proved` of `std::builtin::macro`) is still the
        // matched type's: the pattern is matched against that type, as it is
        // for a type written by hand.
        if let Some(ty) = of
            && ty.contains(SEPARATOR)
            && !self.ctors.contains_key(ty)
            && let Pattern::Ctor { name: n, args } = &mut *p
            && !n.contains(SEPARATOR)
            && !n.starts_with('$')
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
                                Pattern::Bind { .. } => self.pattern(a, span, bound, None),
                                _ => self.pattern(a, span, bound, field),
                            }
                            if let (Some(shape), Pattern::Bind { name: n, .. }) = (field, &*a)
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
            Pattern::Bind { name: n, unused } => {
                if let Some(ty) = of
                    && self.ctors.contains_key(ty)
                    && self.ctor_of(ty, n).is_none()
                    && let Some(Meaning::Ambiguous(all)) = self.names.get(n.as_str())
                    && all.iter().all(|candidate| {
                        self.ctors.values().any(|constructors| {
                            constructors.values().any(|name| name == candidate.as_str())
                        })
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
                        Some(Meaning::To(full)) => Some(&full.0),
                        _ => None,
                    }
                });
                if let Some(constructor) = visible_constructor {
                    let is_ctor = of.and_then(|ty| self.ctor_of(ty, n)).is_some()
                        || self.ctors.values().any(|constructors| {
                            constructors.values().any(|name| name == constructor)
                        });
                    // `^None`: a nullary constructor is not a binding; refuse
                    // the unused assertion once the name is known as a ctor.
                    if is_ctor && let Some(mark) = unused {
                        self.errors.borrow_mut().push((
                            msg!("surface-unused-marker-not-binding"),
                            *mark,
                        ));
                        return;
                    }
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
                let is_ctor = |f: &Full| {
                    self.ctors
                        .values()
                        .any(|cs| cs.values().any(|v| v == f.as_str()))
                };
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
            // `y: T`: the type is read where the `match` stands, and `y` binds.
            Pattern::Typed { name, ty, .. } => {
                self.term(ty);
                bound.push(name.to_string());
            }
            Pattern::Wild
            | Pattern::Int(_)
            | Pattern::Bool(_)
            | Pattern::Text(_)
            | Pattern::Other(_) => {}
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
        if self.by_full.contains_key(full.as_str()) {
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
            to = m.as_str().to_string();
        } else if let Some(f) = self.by_full.get(to.as_str()) {
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
            k.as_str()
                .strip_prefix(module)
                .and_then(|r| r.strip_prefix(SEPARATOR))
                .and_then(|r| r.strip_suffix(ctor))
                .and_then(|ty| ty.strip_suffix(SEPARATOR))
                .is_some_and(|ty| !ty.is_empty() && !ty.contains(SEPARATOR))
        });
        match (found.next(), found.next()) {
            (Some((k, _)), None) => Some(k.as_str().to_string()),
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
                    || self.by_full.contains_key(Full::prelude(&full).as_str()))
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
        if self.global_texts.get()
            && let TermKind::Text(written) = &*t.kind
        {
            self.record_global_literal(written, span);
        }
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
        // A full name written with `::`: `std::text::text`, `Shape::Circle`.
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
                effect.edit_spelling(|spelling| self.effect(spelling, span));
                self.see_perform(effect, span, t.perform_scope);
                args.iter_mut().for_each(|a| self.term(a));
            }
            TermKind::Pi {
                params,
                result,
                effects,
                ..
            } => self.scoped(|| {
                for (n, p) in params {
                    self.term(p);
                    if let Some(n) = n {
                        self.bind([&*n]);
                    }
                }
                if let Some(effects) = effects {
                    effects.iter_mut().for_each(|e| self.row_entry(e, span));
                }
                self.term(result);
            }),
            TermKind::Exists {
                binder,
                domain,
                body,
                ..
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
                ..
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
                ..
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
                ..
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
                            && let Pattern::Bind { name: n, unused: None } = &a.pattern
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
                // name is no type's to rename (`std::bytes::Bytes`).
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

fn names_and(all: &[Full]) -> Message {
    let mut names = all
        .iter()
        .map(|a| Message::text(format!("`{}`", written(a.as_str()))));
    let first = names.next().unwrap_or_else(|| Message::text(""));
    names.fold(first, |before, name| {
        msg!("surface-names-and", before = before, name = name)
    })
}

/// The prelude read as its own files, before any module is known: a name the reader writes with
/// the prelude's module (`std::prelude::Star` of the pattern `#()`) is the prelude's short
/// name, and so is a declaration the reader writes by the library's own reference (`Pair` of a
/// product `A × B`, `Pair::Mk` of `#(a, b)`), in a law and an instance's head too: the
/// kernel checks the prelude's own `Pair` by its short name.
pub fn lower_prelude_sugar(stmts: &mut Vec<Stmt>) {
    LOWER_PAIRS.with(|p| p.set(true));
    lower_prelude(stmts);
    LOWER_PAIRS.with(|p| p.set(false));
}

/// The prelude's names read as [`lower_prelude_sugar`] reads them, its products kept by the
/// library's own reference: Nib reads a product as its own, never as the `Pair` the prelude
/// declares by name.
pub fn lower_prelude_names(stmts: &mut [Stmt]) {
    lower_prelude(stmts)
}

thread_local! {
    /// Whether [`lower_prelude`] names the products by the prelude's short `Pair`.
    static LOWER_PAIRS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The short name of a product's declaration the reader writes by the library's own
/// reference, where the products are lowered to the prelude's `Pair` by name.
fn reader_spelling(n: &crate::identity::Name) -> Option<&'static str> {
    if !LOWER_PAIRS.with(|p| p.get()) {
        return None;
    }
    ["Pair", "Pair::Mk"]
        .into_iter()
        .find(|s| crate::bindings::is_reader_reference(n, s))
}

fn lower_prelude(stmts: &mut [Stmt]) {
    fn name(n: &mut String) {
        if let Some(rest) = n
            .strip_prefix(PRELUDE_MODULE)
            .and_then(|r| r.strip_prefix(SEPARATOR))
        {
            *n = rest.to_string();
        }
    }
    fn short(n: &mut crate::identity::Name) {
        match reader_spelling(n) {
            Some(spelling) => *n = crate::identity::Name::from(spelling),
            None => n.edit_spelling(|spelling| name(spelling)),
        }
    }
    fn pattern(p: &mut Pattern) {
        match p {
            Pattern::Ctor { name: n, args } => {
                short(n);
                args.iter_mut().for_each(pattern);
            }
            Pattern::Record { name: n, fields } => {
                short(n);
                fields.iter_mut().for_each(|(_, a)| pattern(a));
            }
            Pattern::Bind { .. }
            | Pattern::Typed { .. }
            | Pattern::Wild
            | Pattern::Int(_)
            | Pattern::Bool(_)
            | Pattern::Text(_)
            | Pattern::Other(_) => {}
        }
    }
    fn term(t: &mut SurfaceTerm) {
        super::walk::term(t, &mut |t| {
            let needed = match &*t.kind {
                TermKind::Var(n) => n.starts_with(PRELUDE_MODULE) || reader_spelling(n).is_some(),
                TermKind::Match { .. } | TermKind::Handle { .. } => true,
                _ => false,
            };
            if !needed {
                return;
            }
            match Arc::make_mut(&mut t.kind) {
                TermKind::Var(n) => short(n),
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
        super::walk::roots(s, &mut |t| term(t));
        lower_nested(s, &mut |s| match s {
            Stmt::Instance(i) => {
                term(&mut i.head);
                laws(&mut i.laws);
            }
            Stmt::Class(c) => laws(&mut c.laws),
            _ => {}
        });
    }
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
        let of = |text: &'static str| -> HashSet<String> {
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
/// a file of `std` (`Text::of_nat` of `std::text`).
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
/// its full name (`std::text::Text::of_nat`).
#[derive(Clone, Debug)]
pub struct Model {
    pub file: usize,
    pub name: String,
    pub full: String,
}

/// Tells a module function of the prelude apart from the model a file of
/// `std` gives it, where a file of the program means the builtin.
///
/// `Text::of_nat` written in a file that reaches `std::text` is the model
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

#[cfg(test)]
mod module_of_tests {
    use super::module_of;

    #[test]
    fn a_part_that_begins_with_a_digit_is_still_a_name() {
        assert_eq!(module_of(&["15b.taut"]), "_15b");
        assert_eq!(module_of(&["2026", "a-b.taut"]), "_2026::a_b");
        assert_eq!(module_of(&["app", "src", "main.taut"]), "app::src::main");
    }
}

/// A class's laws name its members by the class (`Policy::alloc`). Where the
/// class is renamed to its full name (`std::alloc::Policy`, because another
/// file declares a `Policy` too), so are its members, and the laws follow
/// them: `Policy::alloc` there is this class's member, whatever else is
/// named `Policy`.
fn class_laws_follow_rename(c: &mut super::program::ClassDecl) {
    let full = c.name.as_str().to_string();
    let own = short(&full).to_string();
    if full == own {
        return;
    }
    let prefix = format!("{own}{SEPARATOR}");
    let rename = &mut |t: &mut SurfaceTerm| {
        super::walk::term(t, &mut |t| {
            if let TermKind::Var(Name::Spelled(n)) = &*t.kind
                && let Some(member) = n.strip_prefix(prefix.as_str())
                && !member.contains(SEPARATOR)
            {
                let renamed = format!("{full}{SEPARATOR}{member}");
                *t = t.with_kind(TermKind::Var(Name::Spelled(renamed)), t.span);
            }
        });
    };
    for law in &mut c.laws {
        for (_, ty) in &mut law.theorem.params {
            rename(ty);
        }
        rename(&mut law.theorem.ty);
        if let Some(body) = &mut law.theorem.body {
            rename(body);
        }
    }
}
