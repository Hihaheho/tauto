//! Rust code from NIR: one generated
//! module for a program, and the Cargo workspace around it.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use proc_macro2::Ident;
use tauto_message::msg;
use tauto_nir::{DataDef, Name, Package, Span, Ty};

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
mod nonresuming;
mod operation_instances;
mod syntax;
mod tail;
mod tok;
mod ty;

pub use borrowed_budget::{BorrowDiagnostic, BorrowReason, borrowed_budget_diagnostics};
pub use cargo::{BuildEvent, Options, WASM_TARGETS, Workspace, WriteStats, workspace};
pub use item::{
    allow_lints, emit_items, emit_lib, emit_lib_tokens, emit_module, emit_vm_lib_tokens,
};
pub use nonresuming::{BudgetDiagnostic, BudgetReason, budget_diagnostics};
pub use tok::render;

/// What the manifest says about the program's `extern`s: the Rust type of
/// each extern type, and the Rust path of each extern function.
#[derive(Debug, Clone, Default)]
pub struct Bindings {
    pub types: std::collections::BTreeMap<Name, Binding>,
    pub externs: std::collections::BTreeMap<Name, Binding>,
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
pub fn bridge_ident(tote: &str) -> String {
    format!("{}_bridge", tote.replace('-', "_"))
}

impl Bindings {
    /// Looks every extern of `pkg` up in the manifest (`Tauto.eure`, then the
    /// bindings files it names, then the bridge crate), and fails with the
    /// first one that has no Rust to run.
    pub fn resolve(
        pkg: &Package,
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
            for (k, e) in &m.rust.types {
                lex(e)?;
                out.types.insert(
                    pkg.datas
                        .iter()
                        .find(|d| d.name.as_str() == k)
                        .map(|d| d.name.clone())
                        .unwrap_or_else(|| Name::from(k)),
                    Binding {
                        rust: e.value.clone(),
                        at: at(e),
                        marks: String::new(),
                    },
                );
            }
        }
        // An extern type is the host's: `rust.types`, then the bridge crate's
        // type of the same name.
        for d in pkg.datas.iter().filter(|d| d.host) {
            if out.types.contains_key(&d.name) {
                continue;
            }
            let Some(b) = bridge else {
                return Err(msg!("rustgen-type-no-binding", name = d.name.to_string()).to_string());
            };
            out.types.insert(
                d.name.clone(),
                Binding {
                    rust: format!("{b}::{}", d.name),
                    at: "the bridge crate".into(),
                    marks: String::new(),
                },
            );
        }
        for x in &pkg.externs {
            // An extern of the root module whose name the prelude also uses
            // is `main::name`; the manifest may still write it as `name`.
            let short = x.name.strip_prefix("main::");
            fn key<'m>(
                map: &'m std::collections::BTreeMap<String, tauto::manifest::Entry>,
                full: &str,
                short: Option<&str>,
            ) -> Option<&'m tauto::manifest::Entry> {
                map.get(full).or_else(|| short.and_then(|s| map.get(s)))
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
                (None, Some(b)) => {
                    out.externs.insert(
                        x.name.clone(),
                        Binding {
                            rust: format!("{b}::{}", x.name),
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
    /// `Eq` and `Hash` in Rust: a key of `HashMap` (`DecEq` and `Hash`).
    Hash,
}

pub(crate) struct Gen<'a> {
    pub pkg: &'a Package,
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
    /// The locals of a function type in the function being written (its
    /// parameters and `let`s), with the types they are written with.
    pub fn_locals: HashMap<u32, Ty>,
    /// The locals a pattern bound to a shared field, held as the field's
    /// `Rc` or `Shared` rather than as its content. The content is taken
    /// out (`unrc`) only where a value is needed, and a constructor that
    /// puts the local back into a shared field reuses the cell.
    pub lazy: HashSet<u32>,
}

impl<'a> Gen<'a> {
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
        for function in &pkg.fns {
            o_callback_reserved.insert(function.rust_name.clone());
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
            fn_locals: HashMap::new(),
        };
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
            // `f64` has no `Eq`, and the runtime's `HashMap` neither
            // `PartialEq` nor `Hash` (a `HashMap` is not `PartialEq` in
            // Tauto either).
            Ty::Float | Ty::Float32 if p == Pred::Hash => false,
            Ty::HashMap(..) if matches!(p, Pred::Eq | Pred::Hash) => false,
            Ty::Ref(a) | Ty::RefMut(a) => match p {
                Pred::Clone => matches!(t, Ty::Ref(_)),
                _ => self.ty_has(a, p),
            },
            Ty::Vec(a) | Ty::Array(a) | Ty::Slice(a) | Ty::Option(a) => self.ty_has(a, p),
            Ty::HashMap(a, b) | Ty::Result(a, b) | Ty::Pair(a, b) => {
                self.ty_has(a, p) && self.ty_has(b, p)
            }
            // The runtime's shared slots and handles (`Ref`, `Weak`, `Mutex`,
            // `Atomic`, `Pending`) have no `PartialEq`: a copy is another
            // handle on the same slot, so equality of contents is not theirs.
            Ty::Std(_, _) if matches!(p, Pred::Eq | Pred::Hash) => false,
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
            return (file.display().to_string(), line as u32, col as u32);
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
        let before = &text[..offset.min(text.len())];
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
