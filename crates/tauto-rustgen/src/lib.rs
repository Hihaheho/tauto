//! Rust code from NIR: one generated
//! module for a program, and the Cargo workspace around it.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use proc_macro2::Ident;
use tauto_message::msg;
use tauto_nir::{DataDef, Expr, ExprKind, FnInst, InstId, Name, Package, Repr, Span, Ty};

use crate::tok::{Rs, generics, id, idents, lexes, lifetime};
use quote::quote;

mod abi;
mod array_match;
mod borrowed_budget;
mod cargo;
mod cps;
mod direct;
mod expr;
mod item;
mod names;
mod nonresuming;
mod operation_instances;
mod syntax;
mod tail;
mod tok;
mod ty;

pub use borrowed_budget::{BorrowDiagnostic, BorrowReason, borrowed_budget_diagnostics};
pub use cargo::{
    BuildEvent, JEMALLOC_VERSION, Lock, Options, WASM_TARGETS, Workspace, WriteStats, workspace,
};
pub use item::{
    allow_lints, emit_items, emit_lib, emit_lib_tokens, emit_module, emit_vm_lib_tokens,
};
pub use names::fn_names;
pub use nonresuming::{BudgetDiagnostic, BudgetReason, budget_diagnostics};
pub use tok::render;

/// What the manifest says about the program's `extern`s: the Rust type of
/// each extern type, and the Rust path of each extern function.
#[derive(Debug, Clone, Default)]
pub struct Bindings {
    pub types: std::collections::BTreeMap<Name, Binding>,
    pub externs: std::collections::BTreeMap<Name, Binding>,
    /// Replaceable-extern members whose host bindings were selected for this
    /// build: emit them as externs and skip their Tauto instances.
    pub externalized: HashSet<Name>,
    /// Replaceable data types whose host representation was selected.
    pub externalized_types: HashSet<Name>,
    /// Explicit host promises; these are not inferred from effect rows.
    pub nonresuming_externs: BTreeMap<Name, HostContract>,
    /// Separate Rust facades requiring an explicit whole-embedding host assertion.
    pub nonresuming_entries: BTreeMap<String, EntryContract>,
    /// Also write `uniffi_api`: the facade's functions as UniFFI exports.
    pub uniffi: bool,
}

/// A versioned assertion for a Rust binding, supplied explicitly by its owner.
#[derive(Debug, Clone)]
pub enum HostContract {
    ClosedHostV1 { at: String },
}

impl HostContract {
    pub(crate) fn assumption(&self, name: &str) -> HostAssumption {
        let Self::ClosedHostV1 { at } = self;
        HostAssumption {
            kind: "extern",
            name: name.into(),
            at: at.clone(),
            contract: "closed-host-v1",
        }
    }
}

/// An assertion supplied at the Rust boundary, not a compiler or kernel proof.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct HostAssumption {
    pub kind: &'static str,
    pub name: String,
    pub at: String,
    pub contract: &'static str,
}

/// The source function behind a named whole-embedding trusted facade.
#[derive(Debug, Clone)]
pub struct EntryContract {
    pub function: String,
    pub at: String,
}

/// A Rust type or path, and where it was bound (`Tauto.eure:21`).
#[derive(Debug, Clone)]
pub struct Binding {
    pub rust: String,
    pub at: String,
    /// The `usize` / `isize` marks of an extern: `p1 q2 r`.
    pub marks: String,
}

/// The ident of the bridge crate in Rust: `files-demo-bridge` is
/// `files_demo_bridge`.
/// A declaration's name without its module (`app::native::Device` is
/// `Device`): what `rust.types` and a bridge crate call it.
fn last_segment(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

pub fn bridge_ident(tote: &str) -> String {
    format!("{}_bridge", tote.replace('-', "_"))
}

/// Turns selected replaceable members into host externs/types on the package
/// so wrappers and call sites use them, and drops fallback-only host deps.
/// [`Bindings::resolve`] does this; JavaScript selection calls it on its own.
pub fn materialize_externalized(pkg: &mut Package, bindings: &Bindings) {
    for name in &bindings.externalized_types {
        if let Some(d) = pkg
            .datas
            .iter_mut()
            .find(|d| d.name.as_str() == name.as_str())
        {
            d.host = true;
        }
    }
    for name in &bindings.externalized {
        if pkg.externs.iter().any(|e| e.name.as_str() == name.as_str()) {
            continue;
        }
        let Some(f) = pkg.fns.iter().find(|f| f.source.as_str() == name.as_str()) else {
            continue;
        };
        let waits = pkg
            .replaceable_externs
            .iter()
            .find_map(|b| {
                b.fn_names
                    .iter()
                    .zip(b.fn_waits.iter())
                    .find(|(n, _)| n.as_str() == name.as_str())
                    .map(|(_, w)| *w)
            })
            .unwrap_or(false);
        pkg.externs.push(tauto_nir::ExternDef {
            name: name.clone(),
            generics: f.generics.iter().map(|(n, _)| n.clone()).collect(),
            params: f
                .params
                .iter()
                .map(|p| {
                    (
                        p.local.name.clone(),
                        p.ty.clone(),
                        tauto_nir::pass_of(&p.ty),
                    )
                })
                .collect(),
            ret: f.ret.clone(),
            lends: f.lends.clone(),
            waits,
            span: f.span,
        });
    }
    prune_unreachable_after_externalize(pkg, &bindings.externalized, &bindings.externalized_types);
}

/// What remains reachable after treating selected replaceable members as host
/// leaves (their Tauto bodies are not followed). Includes suspending handler
/// arms, which ordinary [`Expr::walk`] skips.
struct HostReachability {
    fns: HashSet<InstId>,
    externs: HashSet<String>,
    /// Data names still mentioned by remaining code, closed over fields.
    types: HashSet<String>,
    /// Unions still mentioned by remaining code or those data fields.
    unions: HashSet<tauto_nir::UnionId>,
}

fn host_reachability(
    pkg: &Package,
    externalized: &HashSet<Name>,
    externalized_types: &HashSet<Name>,
) -> HostReachability {
    let externalized_spellings: HashSet<&str> = externalized.iter().map(|n| n.as_str()).collect();
    let mut reachable_fns = HashSet::new();
    let mut stack: Vec<InstId> = Vec::new();
    if let Some(top) = pkg.top {
        stack.push(top);
    }
    for e in &pkg.exports {
        stack.push(e.inst);
    }
    while let Some(id) = stack.pop() {
        if !reachable_fns.insert(id) {
            continue;
        }
        let Some(f) = pkg.fns.iter().find(|f| f.id == id) else {
            continue;
        };
        // Host-selected replaceable members do not keep their Tauto bodies.
        if externalized_spellings.contains(f.source.as_str()) {
            continue;
        }
        f.body.walk_with_handlers(&mut |e| {
            if let ExprKind::Call(c) = &e.kind
                && let tauto_nir::Callee::Inst(i) = c.callee
            {
                stack.push(i);
            }
            if let ExprKind::FnValue { inst, .. } = &e.kind {
                stack.push(*inst);
            }
        });
    }
    let mut reachable_externs = HashSet::new();
    for f in &pkg.fns {
        if !reachable_fns.contains(&f.id) {
            continue;
        }
        if externalized_spellings.contains(f.source.as_str()) {
            reachable_externs.insert(f.source.as_str().to_string());
            continue;
        }
        f.body.walk_with_handlers(&mut |e| {
            if let ExprKind::Call(c) = &e.kind {
                match &c.callee {
                    tauto_nir::Callee::Extern(n) => {
                        reachable_externs.insert(n.as_str().to_string());
                    }
                    tauto_nir::Callee::Inst(i) => {
                        if let Some(g) = pkg.fns.iter().find(|g| g.id == *i)
                            && externalized_spellings.contains(g.source.as_str())
                        {
                            reachable_externs.insert(g.source.as_str().to_string());
                        }
                    }
                    _ => {}
                }
            }
        });
    }
    for name in externalized {
        reachable_externs.insert(name.as_str().to_string());
    }

    let mut types = HashSet::new();
    let mut unions = HashSet::new();
    let mut note_ty = |ty: &Ty| {
        ty_type_names(ty, &mut types, &mut unions);
    };
    for f in &pkg.fns {
        if !reachable_fns.contains(&f.id) {
            continue;
        }
        if externalized_spellings.contains(f.source.as_str()) {
            // Selected members keep only their host signature, which
            // materialize copies from the instance; collect from that shape.
            for p in &f.params {
                note_ty(&p.ty);
            }
            note_ty(&f.ret);
            continue;
        }
        for p in &f.params {
            note_ty(&p.ty);
        }
        note_ty(&f.ret);
        f.body.walk_with_handlers(&mut |e| {
            note_ty(&e.ty);
        });
    }
    for x in &pkg.externs {
        if !reachable_externs.contains(x.name.as_str()) {
            continue;
        }
        for (_, ty, _) in &x.params {
            note_ty(ty);
        }
        note_ty(&x.ret);
    }
    for name in externalized_types {
        types.insert(name.as_str().to_string());
    }
    close_type_deps(pkg, externalized_types, &mut types, &mut unions);

    HostReachability {
        fns: reachable_fns,
        externs: reachable_externs,
        types,
        unions,
    }
}

fn ty_type_names(ty: &Ty, types: &mut HashSet<String>, unions: &mut HashSet<tauto_nir::UnionId>) {
    match ty {
        Ty::Data(name, args) => {
            types.insert(name.as_str().to_string());
            for a in args {
                ty_type_names(a, types, unions);
            }
        }
        Ty::Std(_, args) => {
            for a in args {
                ty_type_names(a, types, unions);
            }
        }
        Ty::Vec(a)
        | Ty::Array(a)
        | Ty::Slice(a)
        | Ty::Option(a)
        | Ty::Ref(a)
        | Ty::RefMut(a)
        | Ty::Info(a)
        | Ty::BudgetAnswer(a)
        | Ty::SharedVar(_, a) => ty_type_names(a, types, unions),
        Ty::Result(a, b) | Ty::Pair(a, b) => {
            ty_type_names(a, types, unions);
            ty_type_names(b, types, unions);
        }
        Ty::Fn(f) => {
            for p in &f.params {
                ty_type_names(p, types, unions);
            }
            ty_type_names(&f.ret, types, unions);
        }
        Ty::Union(id) => {
            unions.insert(*id);
        }
        Ty::Int(_)
        | Ty::Bool
        | Ty::Text
        | Ty::Unit
        | Ty::Never
        | Ty::Float
        | Ty::Float32
        | Ty::Buf
        | Ty::Param(_)
        | Ty::Shown => {}
    }
}

/// Adds field / union-member dependencies of types already reached.
/// Host-selected replaceable types are leaves: their Tauto fields are not
/// followed (the host representation does not keep them). Type arguments at
/// use sites are still collected by [`ty_type_names`].
fn close_type_deps(
    pkg: &Package,
    externalized_types: &HashSet<Name>,
    types: &mut HashSet<String>,
    unions: &mut HashSet<tauto_nir::UnionId>,
) {
    let externalized: HashSet<&str> = externalized_types.iter().map(|n| n.as_str()).collect();
    loop {
        let before_types = types.len();
        let before_unions = unions.len();
        for d in &pkg.datas {
            if !types.contains(d.name.as_str()) || externalized.contains(d.name.as_str()) {
                continue;
            }
            for c in &d.ctors {
                for f in &c.fields {
                    ty_type_names(&f.ty, types, unions);
                }
            }
        }
        for u in &pkg.unions {
            if !unions.contains(&u.id) {
                continue;
            }
            for m in &u.members {
                ty_type_names(m, types, unions);
            }
        }
        if types.len() == before_types && unions.len() == before_unions {
            break;
        }
    }
}

/// Drops host externs and marks fallback-only functions and types omitted
/// after host selection, so generators and binding checks agree.
fn prune_unreachable_after_externalize(
    pkg: &mut Package,
    externalized: &HashSet<Name>,
    externalized_types: &HashSet<Name>,
) {
    if externalized.is_empty() && externalized_types.is_empty() {
        return;
    }
    let reach = host_reachability(pkg, externalized, externalized_types);
    pkg.externs
        .retain(|x| reach.externs.contains(x.name.as_str()));
    let externalized_spellings: HashSet<&str> = externalized.iter().map(|n| n.as_str()).collect();
    pkg.host_omitted_fns = pkg
        .fns
        .iter()
        .filter(|f| {
            !reach.fns.contains(&f.id) && !externalized_spellings.contains(f.source.as_str())
        })
        .map(|f| f.id)
        .collect();
    pkg.host_omitted_datas = pkg
        .datas
        .iter()
        .filter(|d| !reach.types.contains(d.name.as_str()))
        .map(|d| d.name.clone())
        .collect();
    pkg.host_omitted_unions = pkg
        .unions
        .iter()
        .filter(|u| !reach.unions.contains(&u.id))
        .map(|u| u.id)
        .collect();
}

/// Whether a NIR function was selected as a host-backed replaceable member.
pub fn is_externalized(pkg: &Package, f: &tauto_nir::FnInst) -> bool {
    pkg.externs
        .iter()
        .any(|e| e.name.as_str() == f.source.as_str())
}

/// Selects replaceable `extern` blocks for the JavaScript backend: a complete
/// JavaScript set, a complete Rust/Wasm set, or Tauto fallback. Mixing
/// JavaScript with Rust/Wasm for one block, or a partial set, is an error.
pub fn apply_javascript_selection(
    pkg: &mut Package,
    manifest: Option<&tauto::manifest::Manifest>,
    target: &str,
) -> Result<(), String> {
    if pkg.replaceable_externs.is_empty() {
        return Ok(());
    }
    let Some(m) = manifest else {
        return Ok(());
    };
    let target_bindings = if target == "node" {
        &m.javascript.node
    } else {
        &m.javascript.browser
    };
    let js_bound = |n: &str| {
        let short = n.strip_prefix("main::");
        target_bindings.contains_key(n)
            || m.javascript.externs.contains_key(n)
            || m.javascript.types.contains_key(n)
            || short.is_some_and(|s| {
                target_bindings.contains_key(s)
                    || m.javascript.externs.contains_key(s)
                    || m.javascript.types.contains_key(s)
            })
    };
    let rust_bound = |n: &str| {
        let short = n.strip_prefix("main::");
        m.rust.externs.contains_key(n)
            || m.rust.types.contains_key(n)
            || short.is_some_and(|s| m.rust.externs.contains_key(s) || m.rust.types.contains_key(s))
    };
    let mut js_members = HashSet::new();
    let mut rust_members = HashSet::new();
    for b in &pkg.replaceable_externs {
        let members: Vec<_> = b.fn_names.iter().chain(b.data_names.iter()).collect();
        if members.is_empty() {
            continue;
        }
        let js_n = members.iter().filter(|n| js_bound(n.as_str())).count();
        let rust_n = members.iter().filter(|n| rust_bound(n.as_str())).count();
        if js_n > 0 && rust_n > 0 {
            let shown = b.id.replace('\0', ", ");
            return Err(msg!("surface-extern-mixed-backends", block = shown).to_string());
        }
        if js_n > 0 {
            if js_n != members.len() {
                let shown = b.id.replace('\0', ", ");
                return Err(msg!("surface-extern-partial-bindings", block = shown).to_string());
            }
            for n in members {
                js_members.insert((*n).clone());
            }
        } else if rust_n > 0 {
            if rust_n != members.len() {
                let shown = b.id.replace('\0', ", ");
                return Err(msg!("surface-extern-partial-bindings", block = shown).to_string());
            }
            for n in members {
                rust_members.insert((*n).clone());
            }
        }
    }
    let bound: HashSet<_> = js_members
        .iter()
        .chain(rust_members.iter())
        .cloned()
        .collect();
    let selection = tauto_nir::select_replaceable_blocks(&pkg.replaceable_externs, &bound)
        .map_err(|e| e.to_string())?;
    let mut host = Bindings::default();
    host.externalized = tauto_nir::external_fn_names(&pkg.replaceable_externs, &selection);
    host.externalized_types = tauto_nir::external_data_names(&pkg.replaceable_externs, &selection);
    materialize_externalized(pkg, &host);
    Ok(())
}

/// The key a dependency's binding of `full` (`dev::src::render::open`) is
/// also written under: the declaring tote and the bare name (`dev::open`).
/// A name of the root module (`main::…`) or a bare name has none.
fn tote_key(full: &str) -> Option<String> {
    let (tote, rest) = full.split_once("::")?;
    if tote == "main" || !rest.contains("::") {
        return None;
    }
    Some(format!("{tote}::{}", last_segment(full)))
}

impl Bindings {
    /// Looks every extern of `pkg` up in the manifest (`Tauto.eure`, then the
    /// bindings files it names, then the bridge crate), and fails with the
    /// first one that has no Rust to run. On success, materializes selected
    /// replaceable members and drops fallback-only host deps on `pkg`.
    pub fn resolve(
        pkg: &mut Package,
        manifest: Option<&tauto::manifest::Manifest>,
        bridge: Option<&str>,
    ) -> Result<Bindings, String> {
        let mut out = Bindings::default();
        let at = |e: &tauto::manifest::Entry| format!("{}:{}", e.file.display(), e.line);
        // The Rust of a binding is put into the generated tokens as it is
        // written, so it has to lex.
        let lex = |e: &tauto::manifest::Entry| {
            lexes(&e.value).map_err(|m| {
                msg!(
                    "rustgen-binding-not-rust",
                    rust = format!("{:?}", e.value),
                    at = at(e),
                    error = m
                )
                .to_string()
            })
        };
        if let Some(m) = manifest {
            // A key names a type by its full name, or by its name bare of
            // the module. A bare name that two declarations share is
            // ambiguous in general (the declarations are told apart by their
            // full names, `app::src::native::T`), and then the key means the
            // one the host answers for: an extern type, or a type an extern
            // function takes or returns. If that leaves more than one, the
            // key has to say which, in the full name.
            let replaceable: HashSet<&str> = pkg
                .replaceable_externs
                .iter()
                .flat_map(|b| b.data_names.iter().map(|n| n.as_str()))
                .collect();
            let mut in_externs = HashSet::new();
            let mut unions = HashSet::new();
            for x in &pkg.externs {
                for (_, ty, _) in &x.params {
                    ty_type_names(ty, &mut in_externs, &mut unions);
                }
                ty_type_names(&x.ret, &mut in_externs, &mut unions);
            }
            for (k, e) in &m.rust.types {
                lex(e)?;
                let same: Vec<&Name> = pkg
                    .datas
                    .iter()
                    .filter(|d| last_segment(&d.name) == k)
                    .map(|d| &d.name)
                    .collect();
                let hostish: Vec<&Name> = same
                    .iter()
                    .copied()
                    .filter(|n| {
                        pkg.datas.iter().any(|d| d.name == **n && d.host)
                            || replaceable.contains(n.as_str())
                            || in_externs.contains(n.as_str())
                    })
                    .collect();
                let name = match pkg.datas.iter().find(|d| d.name.as_str() == k) {
                    Some(d) => d.name.clone(),
                    None => match (same.as_slice(), hostish.as_slice()) {
                        ([], _) => Name::from(k),
                        ([one], _) | (_, [one]) => (*one).clone(),
                        (_, many) => {
                            let many = if many.is_empty() { &same[..] } else { many };
                            return Err(msg!(
                                "rustgen-type-ambiguous",
                                name = k.clone(),
                                at = at(e),
                                candidates = many
                                    .iter()
                                    .map(|n| n.to_string())
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            )
                            .to_string());
                        }
                    },
                };
                out.types.insert(
                    name,
                    Binding {
                        rust: e.value.clone(),
                        at: at(e),
                        marks: String::new(),
                    },
                );
            }
        }
        // Replaceable blocks: all members bound → host; none → Tauto fallback;
        // partial → error. Required `pkg.externs` stay mandatory below.
        {
            let mut bound = HashSet::new();
            if let Some(m) = manifest {
                for b in &pkg.replaceable_externs {
                    for n in b.fn_names.iter().chain(b.data_names.iter()) {
                        let short = n.strip_prefix("main::");
                        let named = |map: &BTreeMap<String, tauto::manifest::Entry>| {
                            map.contains_key(n.as_str())
                                || short.is_some_and(|s| map.contains_key(s))
                                || map.contains_key(last_segment(n))
                        };
                        if named(&m.rust.externs) || named(&m.rust.types) {
                            bound.insert(n.clone());
                        }
                    }
                }
            }
            let selection = tauto_nir::select_replaceable_blocks(&pkg.replaceable_externs, &bound)
                .map_err(|e| e.to_string())?;
            out.externalized = tauto_nir::external_fn_names(&pkg.replaceable_externs, &selection);
            out.externalized_types =
                tauto_nir::external_data_names(&pkg.replaceable_externs, &selection);
            if let Some(m) = manifest {
                for name in &out.externalized {
                    let short = name.strip_prefix("main::");
                    let e = m
                        .rust
                        .externs
                        .get(name.as_str())
                        .or_else(|| short.and_then(|s| m.rust.externs.get(s)))
                        .or_else(|| m.rust.externs.get(&tote_key(name)?))
                        .ok_or_else(|| {
                            msg!("rustgen-extern-no-binding", name = name.to_string()).to_string()
                        })?;
                    lex(e)?;
                    out.externs.insert(
                        name.clone(),
                        Binding {
                            rust: e.value.clone(),
                            at: at(e),
                            marks: m
                                .rust
                                .marks
                                .get(name.as_str())
                                .or_else(|| short.and_then(|s| m.rust.marks.get(s)))
                                .map(|e| e.value.clone())
                                .unwrap_or_default(),
                        },
                    );
                }
                for name in &out.externalized_types {
                    if out.types.contains_key(name) {
                        continue;
                    }
                    let short = name.strip_prefix("main::");
                    let e = m
                        .rust
                        .types
                        .get(name.as_str())
                        .or_else(|| short.and_then(|s| m.rust.types.get(s)))
                        .ok_or_else(|| {
                            msg!("rustgen-type-no-binding", name = name.to_string()).to_string()
                        })?;
                    lex(e)?;
                    out.types.insert(
                        name.clone(),
                        Binding {
                            rust: e.value.clone(),
                            at: at(e),
                            marks: String::new(),
                        },
                    );
                }
            } else if !out.externalized.is_empty() || !out.externalized_types.is_empty() {
                return Err(msg!(
                    "rustgen-extern-no-binding",
                    name = out
                        .externalized
                        .iter()
                        .chain(out.externalized_types.iter())
                        .next()
                        .map(|n| n.to_string())
                        .unwrap_or_default()
                )
                .to_string());
            }
        }
        // After host selection, only what remaining bodies still reach needs
        // host bindings; fallback-only deps are dropped at materialize time.
        let reach = if out.externalized.is_empty() && out.externalized_types.is_empty() {
            None
        } else {
            Some(host_reachability(
                pkg,
                &out.externalized,
                &out.externalized_types,
            ))
        };
        // An extern type is the host's: `rust.types`, then the bridge crate's
        // type of the same name.
        for d in pkg.datas.iter().filter(|d| {
            let hostish = d.host
                || out
                    .externalized_types
                    .iter()
                    .any(|n| n.as_str() == d.name.as_str());
            hostish
                && reach
                    .as_ref()
                    .is_none_or(|r| r.types.contains(d.name.as_str()))
        }) {
            if out.types.contains_key(&d.name) {
                continue;
            }
            let Some(b) = bridge else {
                return Err(msg!("rustgen-type-no-binding", name = d.name.to_string()).to_string());
            };
            out.types.insert(
                d.name.clone(),
                Binding {
                    rust: format!("{b}::{}", last_segment(&d.name)),
                    at: "the bridge crate".into(),
                    marks: String::new(),
                },
            );
        }
        for x in &pkg.externs {
            if reach
                .as_ref()
                .is_some_and(|r| !r.externs.contains(x.name.as_str()))
            {
                continue;
            }
            // A Rust binding answers at once: a call that waits on the host
            // (`! {wait}`) has no Rust binding yet.
            if x.waits {
                return Err(msg!("rustgen-extern-waits", name = x.name.to_string()).to_string());
            }
            // An extern of the root module whose name the prelude also uses
            // is `main::name`; the manifest may still write it as `name`.
            let short = x.name.strip_prefix("main::");
            fn key<'m>(
                map: &'m std::collections::BTreeMap<String, tauto::manifest::Entry>,
                full: &str,
                short: Option<&str>,
            ) -> Option<&'m tauto::manifest::Entry> {
                map.get(full)
                    .or_else(|| short.and_then(|s| map.get(s)))
                    .or_else(|| map.get(&tote_key(full)?))
            }
            let bound = manifest.and_then(|m| key(&m.rust.externs, &x.name, short));
            if let Some(e) = bound {
                lex(e)?;
            }
            match (bound, bridge) {
                (Some(e), _) => {
                    out.externs.insert(
                        x.name.clone(),
                        Binding {
                            rust: e.value.clone(),
                            at: at(e),
                            marks: manifest
                                .and_then(|m| key(&m.rust.marks, &x.name, short))
                                .map(|e| e.value.clone())
                                .unwrap_or_default(),
                        },
                    );
                }
                // The bridge crate's function is the declared name, which a
                // program that shares the bare name elsewhere writes in full
                // (`dev::src::render::open`) without moving the function.
                (None, Some(b)) => {
                    out.externs.insert(
                        x.name.clone(),
                        Binding {
                            rust: format!("{b}::{}", last_segment(&x.name)),
                            at: "the bridge crate".into(),
                            marks: String::new(),
                        },
                    );
                }
                (None, None) => {
                    return Err(
                        msg!("rustgen-extern-no-binding", name = x.name.to_string()).to_string()
                    );
                }
            }
        }
        materialize_externalized(pkg, &out);
        if let Some(m) = manifest {
            out.uniffi = m.rust.uniffi;
            for (name, entry) in &m.rust.nonresuming_externs {
                if entry.value != "closed-host-v1" {
                    return Err(msg!(
                        "rustgen-unknown-host-contract",
                        at = at(entry),
                        contract = format!("{:?}", entry.value)
                    )
                    .to_string());
                }
                let external = pkg.externs.iter().find(|x| {
                    x.name.as_str() == name || x.name.strip_prefix("main::") == Some(name.as_str())
                });
                let Some(external) = external else {
                    return Err(msg!(
                        "rustgen-contract-unknown-extern",
                        at = at(entry),
                        name = name
                    )
                    .to_string());
                };
                out.nonresuming_externs.insert(
                    external.name.clone(),
                    HostContract::ClosedHostV1 { at: at(entry) },
                );
            }
            for (facade, entry) in &m.rust.nonresuming_entries {
                let mut chars = facade.chars();
                let valid = chars
                    .next()
                    .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                    && chars.all(|c| c.is_ascii_alphanumeric() || c == '_');
                if !valid || facade == "_" {
                    return Err(msg!(
                        "rustgen-invalid-facade-name",
                        at = at(entry),
                        name = format!("{facade:?}")
                    )
                    .to_string());
                }
                let public_name = crate::expr::field_ident(facade).to_string();
                if pkg
                    .exports
                    .iter()
                    .any(|e| crate::expr::field_ident(&e.name).to_string() == public_name)
                    || out
                        .nonresuming_entries
                        .keys()
                        .any(|n| crate::expr::field_ident(n).to_string() == public_name)
                {
                    return Err(msg!(
                        "rustgen-facade-collides-export",
                        at = at(entry),
                        name = facade
                    )
                    .to_string());
                }
                if pkg
                    .datas
                    .iter()
                    .any(|data| Gen::data_name(pkg, &data.name).to_string() == public_name)
                {
                    return Err(msg!(
                        "rustgen-facade-collides-data",
                        at = at(entry),
                        name = facade
                    )
                    .to_string());
                }
                let function = entry.value.trim();
                if !pkg.exports.iter().any(|e| e.name == function) {
                    return Err(msg!(
                        "rustgen-entry-unknown-export",
                        at = at(entry),
                        name = function
                    )
                    .to_string());
                }
                out.nonresuming_entries.insert(
                    facade.clone(),
                    EntryContract {
                        function: function.into(),
                        at: at(entry),
                    },
                );
            }
        }
        let generator = Gen::new(pkg, &Sources { file: "", text: "" }, &out);
        for contract in out.nonresuming_entries.values() {
            let export = pkg
                .exports
                .iter()
                .find(|e| e.name == contract.function)
                .expect("validated contract export");
            if let Some(reason) = generator.export_issue(export) {
                return Err(
                    msg!("rustgen-invalid-entry", at = &contract.at, reason = reason).to_string(),
                );
            }
        }
        Ok(out)
    }
}

/// The text of the source files a span points into.
pub struct Sources<'a> {
    /// The name shown in a run-time error's place.
    pub file: &'a str,
    pub text: &'a str,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Pred {
    Clone,
    Eq,
    Show,
    /// `Eq` and `Hash` in Rust, derived where every part has them.
    Hash,
}

pub(crate) struct Gen<'a> {
    pub pkg: &'a Package,
    /// The Rust name of each instance of `pkg` (`names::fn_names`).
    pub fn_names: Vec<String>,
    pub sources: &'a Sources<'a>,
    pub bindings: &'a Bindings,
    pub union_names: Vec<Rs>,
    pub union_params: Vec<Vec<String>>,
    pub data_index: HashMap<&'a Name, usize>,
    /// For each data: can it be cloned, compared, shown.
    pub flags: Vec<[bool; 4]>,
    /// Where run-time errors point: `(file, line, col)` by constant name.
    pub locs: BTreeMap<String, (String, u32, u32)>,
    /// Types are spelled with `'r` for borrows.
    pub named_refs: Cell<bool>,
    /// The name of that lifetime: `'r`, or `'a` in a function of the O tier.
    pub lt_name: Cell<&'static str>,
    /// A callback's environment region, independent of synchronous result borrows.
    pub o_lt_name: Cell<&'static str>,
    /// The function being written gives its synchronous function values the
    /// region `'f` (`FnInst::fn_region`).
    pub fn_region: Cell<bool>,
    /// Owned O callback aliases needed by local lifetime inference.
    pub o_callback_types: RefCell<std::collections::BTreeSet<(usize, bool)>>,
    /// Complete package identifiers, independent of alias emission order.
    pub o_callback_reserved: BTreeSet<String>,
    /// Internal modules carry alias declarations; standalone type spellings do not.
    pub o_callback_aliases: bool,
    /// A type Rust cannot infer is written `()`.
    pub infer_unit: Cell<bool>,
    pub next_label: u32,
    pub next_tmp: u32,
    /// The locals a continuation copies, where a closure of the M tier is
    /// written.
    pub m_scope: Vec<Ident>,
    /// The locals that are the `k` of an arm of the M tier (a `Resume`).
    pub conts: HashSet<u32>,
    /// Tick-only O instances needed by nonresuming synchronous bodies.
    pub sync_budget_fns: std::collections::BTreeSet<tauto_nir::InstId>,
    /// Only populated while emitting an explicit private trusted facade body.
    pub trusted_budget_host: Option<HostAssumption>,
    pub trusted_budget_callbacks: BTreeMap<u32, HostAssumption>,
    pub contract_functions: BTreeMap<String, String>,
    pub borrowed_budget: borrowed_budget::Variants,
    /// While a function's body is written as a loop: the function, whose
    /// calls to itself marked `recur` jump back to the start of the body.
    pub self_tail: Option<tauto_nir::InstId>,
    /// The generics of the function being written: an arm `tauto_nir::arms`
    /// wrote at a payload type naming another function's generic (one
    /// performed inside that function) has no type to be written at here.
    pub scope_generics: Vec<String>,
    /// The locals of a function type in the function being written (its
    /// parameters and `let`s), with the types they are written with.
    pub fn_locals: HashMap<u32, Ty>,
    /// The locals a pattern bound to a shared field, held as the field's
    /// `Rc` or `Shared` rather than as its content. The content is taken
    /// out (`unrc`) only where a value is needed, and a constructor that
    /// puts the local back into a shared field reuses the cell.
    pub lazy: HashSet<u32>,
    /// The functions of the program read as a value somewhere, or
    /// exported: their Rust signature is the one their type says.
    pub fn_values: HashSet<InstId>,
    /// The parameters of the M-tier function being written that it takes as
    /// an owned copy of a borrowed duplicable value (`Gen::m_owned_param`).
    pub owned_refs: HashSet<u32>,
    /// The type of each `var` the M-tier code being written declares: a
    /// `while` that suspends passes the ones its body assigns to each round.
    pub var_tys: HashMap<u32, Ty>,
    /// The continuations of the handlers whose body can `return`: the rest
    /// of the body ends as `Ok(value)` or `Err(returned)`.
    pub ret_conts: HashSet<u32>,
    /// The arms being written belong to a handler whose body can `return`.
    pub arm_returns: Cell<bool>,
    /// The `direct` operations whose handler is in a local here
    /// (`evd_<id>`), as `tauto_nir::evidence` resolved it.
    pub evd: Vec<tauto_nir::OpIndex>,
}

impl<'a> Gen<'a> {
    /// Runs `f` where no handler of the function is known (a closure, a
    /// `budget`, code of a higher tier).
    pub(crate) fn without_evd<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = std::mem::take(&mut self.evd);
        let r = f(self);
        self.evd = saved;
        r
    }

    /// The local that holds the handler of `op`.
    pub(crate) fn evd_name(&self, op: tauto_nir::OpIndex) -> proc_macro2::Ident {
        quote::format_ident!("evd_{}", self.pkg.ops[op].id)
    }

    /// The type of a handler passed as evidence: `&dyn Fn(A) -> R`.
    pub(crate) fn evd_ty(&self, op: tauto_nir::OpIndex) -> proc_macro2::TokenStream {
        let (params, ret) = &self.pkg.evidence.ops[&op];
        let tup = self.payload_ty(params);
        let r = self.ty(ret);
        quote::quote!(&dyn Fn(#tup) -> #r)
    }

    pub fn new(pkg: &'a Package, sources: &'a Sources<'a>, bindings: &'a Bindings) -> Gen<'a> {
        let mut union_params = Vec::new();
        let mut union_names = Vec::new();
        for u in &pkg.unions {
            let mut ps = std::collections::BTreeSet::new();
            for m in &u.members {
                m.params(&mut ps);
            }
            let ps: Vec<String> = ps.into_iter().collect();
            let name = id(&format!("U{}", u.id));
            let args = generics(idents(&ps));
            union_names.push(quote!(#name #args));
            union_params.push(ps);
        }
        let mut o_callback_reserved = BTreeSet::new();
        for data in &pkg.datas {
            o_callback_reserved.insert(Self::data_name(pkg, &data.name).to_string());
            o_callback_reserved.extend(data.generics.iter().cloned());
        }
        for (function, name) in pkg.fns.iter().zip(names::fn_names(pkg)) {
            o_callback_reserved.insert(name);
            o_callback_reserved.extend(function.generics.iter().map(|(name, _)| name.clone()));
        }
        for external in &pkg.externs {
            o_callback_reserved.insert(external.name.to_string());
            o_callback_reserved.extend(external.generics.iter().cloned());
        }
        for operation in &pkg.ops {
            o_callback_reserved.extend(operation.generics.iter().cloned());
        }
        for (index, parameters) in union_params.iter().enumerate() {
            o_callback_reserved.insert(format!("U{index}"));
            o_callback_reserved.extend(parameters.iter().cloned());
        }
        o_callback_reserved.extend(["show", "externs", "api"].map(str::to_string));
        for binding in bindings.types.values().chain(bindings.externs.values()) {
            if let Ok(tokens) = binding.rust.parse::<Rs>() {
                reserve_identifiers(tokens, &mut o_callback_reserved);
            }
        }
        let data_index = pkg
            .datas
            .iter()
            .enumerate()
            .map(|(i, d)| (&d.name, i))
            .collect();
        let mut g = Gen {
            pkg,
            fn_names: names::fn_names(pkg),
            sources,
            bindings,
            union_names,
            union_params,
            data_index,
            flags: vec![[true; 4]; pkg.datas.len()],
            locs: BTreeMap::new(),
            named_refs: Cell::new(false),
            lazy: HashSet::new(),
            lt_name: Cell::new("'r"),
            o_lt_name: Cell::new("'_"),
            fn_region: Cell::new(false),
            o_callback_types: RefCell::new(Default::default()),
            o_callback_reserved,
            o_callback_aliases: true,
            infer_unit: Cell::new(false),
            next_label: 0,
            next_tmp: 0,
            m_scope: Vec::new(),
            conts: HashSet::new(),
            sync_budget_fns: Default::default(),
            trusted_budget_host: None,
            trusted_budget_callbacks: Default::default(),
            contract_functions: Default::default(),
            borrowed_budget: Default::default(),
            self_tail: None,
            scope_generics: Vec::new(),
            fn_locals: HashMap::new(),
            fn_values: HashSet::new(),
            owned_refs: HashSet::new(),
            var_tys: HashMap::new(),
            ret_conts: HashSet::new(),
            arm_returns: Cell::new(false),
            evd: Vec::new(),
        };
        for e in &pkg.exports {
            g.fn_values.insert(e.inst);
        }
        for f in &pkg.fns {
            each_expr(&f.body, &mut |e| {
                if let ExprKind::FnValue { inst, .. } = &e.kind {
                    g.fn_values.insert(*inst);
                }
            });
        }
        g.settle_flags();
        g
    }

    pub fn data(&self, name: &Name) -> Option<&'a DataDef> {
        self.data_index.get(name).map(|i| &self.pkg.datas[*i])
    }

    /// The Rust name of a generated type. A name the generated module
    /// already uses for something else (the names `item::uses` imports, the
    /// crates its paths start from, and the prelude's types and variants
    /// the generated code writes bare) gets a trailing `_`, and so does a
    /// name that is one of those plus trailing `_`s, so two types never
    /// meet at one Rust name.
    pub fn data_name(pkg: &Package, name: &Name) -> Ident {
        Self::data_symbol(pkg.datas.iter().map(|d| &d.name), name)
    }

    fn data_symbol<'n>(names: impl Iterator<Item = &'n Name>, name: &Name) -> Ident {
        let names: Vec<_> = names.collect();
        let base = Self::data_spelling(name);
        let spelling = base.to_string();
        let collides = names
            .iter()
            .any(|other| **other != *name && Self::data_spelling(other).to_string() == spelling);
        if !collides {
            return base;
        }
        let position = names
            .iter()
            .position(|other| **other == *name)
            .expect("a generated type has a declaration identity");
        let occupied: BTreeSet<String> = names
            .iter()
            .map(|other| Self::data_spelling(other).to_string())
            .collect();
        let mut candidate = format!("{}__type_{position}", spelling.trim_start_matches("r#"));
        while occupied.contains(&candidate) {
            candidate.push('_');
        }
        id(&candidate)
    }

    fn data_spelling(name: &str) -> Ident {
        static TAKEN: std::sync::LazyLock<BTreeSet<String>> = std::sync::LazyLock::new(|| {
            let mut taken: BTreeSet<String> = [
                "String", "Vec", "Option", "Result", "Box", "Some", "None", "Ok", "Err", "Bomb",
            ]
            .map(str::to_string)
            .into();
            reserve_identifiers(item::uses(), &mut taken);
            // `use` itself: a keyword is written raw, so it meets nothing.
            taken.retain(|n| !tok::KEYWORDS.contains(&n.as_str()));
            taken
        });
        if TAKEN.contains(name.trim_end_matches('_')) {
            id(&format!("{name}_"))
        } else {
            id(name)
        }
    }

    fn settle_flags(&mut self) {
        loop {
            let mut changed = false;
            for (i, d) in self.pkg.datas.iter().enumerate() {
                let eq = !d.linear && !self.bindings.types.contains_key(&d.name);
                let mut now = [d.clone, eq, true, eq];
                for c in &d.ctors {
                    for f in &c.fields {
                        for (k, p) in [Pred::Clone, Pred::Eq, Pred::Show, Pred::Hash]
                            .into_iter()
                            .enumerate()
                        {
                            if !self.ty_has(&f.ty, p) {
                                now[k] = false;
                            }
                        }
                    }
                }
                if now != self.flags[i] {
                    self.flags[i] = now;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// Whether Rust's impl of `p` exists for the type (type parameters are
    /// assumed to have it: the bound is on the parameter).
    pub fn ty_has(&self, t: &Ty, p: Pred) -> bool {
        let k = p as usize;
        match t {
            Ty::Fn(f) => p == Pred::Clone && f.kind.dup(),
            Ty::Info(_) | Ty::BudgetAnswer(_) => false,
            // `f64` has no `Hash`.
            Ty::Float | Ty::Float32 if p == Pred::Hash => false,
            Ty::Ref(a) | Ty::RefMut(a) => match p {
                Pred::Clone => matches!(t, Ty::Ref(_)),
                _ => self.ty_has(a, p),
            },
            Ty::Vec(a) | Ty::Array(a) | Ty::Slice(a) | Ty::Option(a) => self.ty_has(a, p),
            Ty::Result(a, b) | Ty::Pair(a, b) => self.ty_has(a, p) && self.ty_has(b, p),
            // The runtime's shared slots and handles (`Ref`, `Weak`, `Mutex`,
            // `Atomic`, `Pending`) have no `PartialEq`: a copy is another
            // handle on the same slot, so equality of contents is not theirs.
            Ty::Std(_, _) if matches!(p, Pred::Eq | Pred::Hash) => false,
            // A copy of a `Ref`, `Weak` or `Mutex` is another handle on the
            // same slot: the runtime's `Clone` copies the handle and asks
            // nothing of the content, so the handle is `Clone` even when the
            // content is affine.
            Ty::Std(
                tauto_nir::StdType::Ref | tauto_nir::StdType::Weak | tauto_nir::StdType::Mutex,
                _,
            ) if p == Pred::Clone => true,
            // The runtime's slots table owns its cells and has neither a
            // copy nor a printed form.
            Ty::Std(tauto_nir::StdType::Slots, _) => false,
            Ty::Std(_, args) => args.iter().all(|a| self.ty_has(a, p)),
            Ty::Data(n, args) => {
                self.data_index.get(n).is_none_or(|i| self.flags[*i][k])
                    && args.iter().all(|a| self.ty_has(a, p))
            }
            Ty::Union(id) => self.pkg.unions[*id]
                .members
                .iter()
                .all(|m| self.ty_has(m, p)),
            _ => true,
        }
    }

    /// The source file, line and column of a span, following macro origins.
    pub fn span_place(&self, span: Span) -> (String, u32, u32) {
        if let Some((file, line, col)) = self
            .pkg
            .sources
            .as_ref()
            .and_then(|map| map.locate(span.start))
        {
            // A program given as text is read at a path that is no file of the
            // caller's: the caller's own name for the text is the place.
            let file = if file == std::path::Path::new(tauto::nir::TEXT_ENTRY) {
                self.sources.file.to_owned()
            } else {
                file.display().to_string()
            };
            return (file, line as u32, col as u32);
        }
        // A program read from files places every span through its map: an
        // offset the map cannot place belongs to none of the entry's text, so
        // reading the entry at it would name a wrong place, or split a
        // character.
        if self.pkg.sources.is_some() && span.start < tauto::surface::PRELUDE_BASE {
            return (self.sources.file.to_owned(), 0, 0);
        }
        let (prelude, offset) = if span.start >= tauto::surface::PRELUDE_BASE {
            (true, (span.start - tauto::surface::PRELUDE_BASE) as usize)
        } else {
            (false, span.start as usize)
        };
        let text = if prelude {
            tauto::nibstd::PRELUDE
        } else {
            self.sources.text
        };
        let before = &text[..text.floor_char_boundary(offset)];
        let line = before.matches('\n').count() as u32 + 1;
        let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) as u32 + 1;
        (
            if prelude {
                "<prelude>"
            } else {
                self.sources.file
            }
            .to_owned(),
            line,
            col,
        )
    }

    /// The name of the constant for the place of `span`, declared once.
    pub fn loc(&mut self, span: Span) -> Ident {
        let (file, line, col) = self.span_place(span);
        let name = if self.pkg.sources.is_some() {
            format!("LM{}", span.start)
        } else {
            format!(
                "{}{line}_{col}",
                if file == "<prelude>" { "LP" } else { "L" }
            )
        };
        self.locs.insert(name.clone(), (file, line, col));
        id(&name)
    }

    pub fn label(&mut self) -> Rs {
        self.next_label += 1;
        lifetime(&format!("'h{}", self.next_label))
    }

    pub fn tmp(&mut self, base: &str) -> Ident {
        self.next_tmp += 1;
        id(&format!("{base}_t{}", self.next_tmp))
    }
}

/// Rust paths in bindings can refer to names outside the generated package.
fn reserve_identifiers(tokens: Rs, reserved: &mut BTreeSet<String>) {
    for token in tokens {
        match token {
            proc_macro2::TokenTree::Ident(name) => {
                reserved.insert(name.to_string().trim_start_matches("r#").to_string());
            }
            proc_macro2::TokenTree::Group(group) => reserve_identifiers(group.stream(), reserved),
            _ => {}
        }
    }
}

/// Rust spelling shared by the native generator and the typed wasm ABI.
/// Suspending callbacks require the caller's named `'a` region in scope;
/// their spelling does not require separately emitted callback aliases.
pub fn type_name(pkg: &Package, bindings: &Bindings, ty: &Ty) -> String {
    let mut g = Gen::new(pkg, &Sources { file: "", text: "" }, bindings);
    g.o_callback_aliases = false;
    g.o_lt_name.set("'a");
    g.ty(ty).to_string()
}

pub fn field_name(name: &str) -> String {
    expr::field_ident(name).to_string()
}

/// Rust ABI type with an explicit lifetime for borrowed codec results.
pub fn type_name_with_lifetime(
    pkg: &Package,
    bindings: &Bindings,
    ty: &Ty,
    lifetime: &'static str,
) -> String {
    let mut g = Gen::new(pkg, &Sources { file: "", text: "" }, bindings);
    g.o_callback_aliases = false;
    g.named_refs.set(true);
    g.lt_name.set(lifetime);
    g.o_lt_name.set(lifetime);
    g.ty(ty).to_string()
}

#[cfg(test)]
mod identity_tests {
    use super::*;

    #[test]
    fn type_symbols_distinguish_references_and_escaped_spellings() {
        let names: Vec<Name> = ["Same", "Same", "A::B", "A__B", "Same__type_0"]
            .into_iter()
            .map(|s| Name::from(tauto::identity::DeclRef::fresh(s)))
            .collect();
        let symbols: Vec<_> = names
            .iter()
            .map(|name| Gen::data_symbol(names.iter(), name).to_string())
            .collect();
        assert_eq!(symbols.iter().collect::<BTreeSet<_>>().len(), names.len());
        for (name, symbol) in names.iter().zip(&symbols) {
            assert_eq!(
                &Gen::data_symbol(names.iter(), &name.clone()).to_string(),
                symbol
            );
        }
    }
}

/// `Expr::walk`, the arms of suspending handlers included.
pub(crate) fn each_expr(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    e.walk(&mut |x| {
        f(x);
        if let ExprKind::Handle(h) = &x.kind {
            for a in &h.susp {
                if let Some(g) = &a.guard {
                    each_expr(g, f);
                }
                each_expr(&a.body, f);
            }
        }
    });
}

impl Gen<'_> {
    /// Whether parameter `i` of `f`, a shared borrow of a duplicable value
    /// (`&A ≡ A`), is taken as an owned copy. A function of the M tier
    /// returns its computation before the computation runs, so a borrow it
    /// takes must outlive the caller's frame; an owned copy has no such
    /// bound, and the function reads it through a borrow of its own. A
    /// function read as a value or exported keeps the signature of its type.
    pub(crate) fn m_owned_param(&self, f: &FnInst, i: usize) -> bool {
        let Some(p) = f.params.get(i) else {
            return false;
        };
        f.tier == tauto_nir::Tier::M
            && p.local.repr == Repr::Ref
            && !self.fn_values.contains(&f.id)
            && matches!(&p.ty, Ty::Ref(t) if !matches!(**t, Ty::Fn(_)) && self.ty_has(t, crate::Pred::Clone))
    }
}

/// Whether `n` is the prelude's `Placed`, which runs as a value in a region
/// (`tauto_rt::region::Placed`). The checker knows nothing of the name.
pub(crate) fn is_placed(n: &tauto_nir::Name) -> bool {
    tauto::bindings::is_library(n, "Placed") || is_rc_placed(n)
}

/// Whether `n` is the prelude's `RcPlaced`, which runs as a value in a
/// counted region or on the heap (`tauto_rt::region::RcPlaced`).
pub(crate) fn is_rc_placed(n: &tauto_nir::Name) -> bool {
    tauto::bindings::is_library(n, "RcPlaced")
}

/// Whether `n` is std's `BumpPolicy`, whose regions the runtime cuts by bump.
pub(crate) fn is_bump_policy(n: &tauto_nir::Name) -> bool {
    n.as_str().rsplit("::").next() == Some("BumpPolicy")
}
