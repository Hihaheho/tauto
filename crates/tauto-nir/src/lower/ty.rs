use std::collections::HashSet;

use tauto::surface::SurfaceTerm;
use tauto::types::{Data, Kind, Ty as TTy};

use super::*;

/// A field of more words than this goes behind an `Rc` (`box_large_fields`).
const LARGE_FIELD_WORDS: usize = 8;

/// The checked type's structural order, without occurrence or inference IDs.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum TypeKey {
    Int(Width),
    Bool,
    Text,
    Unit,
    Never,
    Decimal,
    Float,
    Float32,
    Fn(Vec<TypeKey>, Box<TypeKey>, Kind),
    Union(Vec<TypeKey>),
    Product(Vec<TypeKey>),
    Tagged(BTreeSet<String>, Box<TypeKey>),
    Named(String, Vec<TypeKey>),
    Param(Option<String>, Kind),
    Info(Box<TypeKey>),
    Borrow(Box<TypeKey>, bool),
    Infer,
    Poly(Vec<(Option<String>, Kind)>, Box<TypeKey>),
    App(Box<TypeKey>, Box<TypeKey>),
}

impl<'a> Lowerer<'a> {
    /// The Rust shape of a tauto type. A function type is of tier `S` here;
    /// `conv_in` sets the tier a declaration writes.
    pub fn conv(&mut self, t: &TTy) -> Ty {
        match t {
            TTy::Int(w) => Ty::Int(*w),
            TTy::Bool => Ty::Bool,
            TTy::Text => Ty::Text,
            TTy::Unit => Ty::Unit,
            TTy::Never => Ty::Never,
            TTy::Float => Ty::Float,
            TTy::Float32 => Ty::Float32,
            // `Decimal` is not written; `build` reports it.
            TTy::Decimal => {
                let m = "error: Decimal is not supported by the rust backend".to_string();
                if !self.build_errors.contains(&m) {
                    self.build_errors.push(m);
                }
                Ty::Infer
            }
            // The dictionary of a method with generics of its own: the rust
            // backend does not write these.
            TTy::Poly(..) | TTy::App(..) => {
                let m = "error: a class method with generics or a type constructor variable is not supported by the rust backend"
                    .to_string();
                if !self.build_errors.contains(&m) {
                    self.build_errors.push(m);
                }
                Ty::Infer
            }
            TTy::Fn(ps, r, k) => {
                let params = ps.iter().map(|p| self.conv(p)).collect();
                let ret = self.conv(r);
                Ty::Fn(Box::new(FnTy {
                    params,
                    ret,
                    kind: *k,
                    tier: Tier::S,
                }))
            }
            TTy::Union(ts) => {
                // A checked union's identity ordering is not an output order.
                // Sort before conversion, which can allocate nested unions.
                let mut ordered: Vec<&TTy> = ts.iter().collect();
                ordered.sort_by_cached_key(|t| self.stable_type_key(t));
                let mut members: Vec<Ty> = Vec::new();
                for m in ordered {
                    let m = self.conv(m);
                    if !members.contains(&m) {
                        members.push(m);
                    }
                }
                if members.len() == 1 {
                    return members.pop().unwrap();
                }
                self.union_id(members)
            }
            TTy::Product(ts) => {
                Ty::Product(ts.iter().map(|t| (t.to_string(), self.conv(t))).collect())
            }
            TTy::Tagged(_, t) => self.conv(t),
            TTy::Named(n, args) => {
                // A row parameter has no runtime representation.
                let rows = self.row_parameters(n);
                let mut a: Vec<Ty> = args
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !rows.contains(i))
                    .map(|(_, x)| self.conv(x))
                    .collect();
                match (n.as_str(), a.len()) {
                    ("Buf", 0) => Ty::Buf,
                    ("Vec", 1) => Ty::Vec(Box::new(a.remove(0))),
                    ("Array", 1) => Ty::Array(Box::new(a.remove(0))),
                    ("Ref", 1)
                    | ("Weak", 1)
                    | ("Mutex", 1)
                    | ("MutexGuard", 1)
                    | ("Atomic", 0)
                    | ("Bytes", 0)
                    | ("Pending", 1)
                    | ("Secret", 1)
                    | ("Signal", 0) => Ty::Std(n.clone(), a),
                    ("HashMap", 2) => {
                        let v = a.pop().unwrap();
                        Ty::HashMap(Box::new(a.pop().unwrap()), Box::new(v))
                    }
                    ("Slice", 1) => Ty::Slice(Box::new(a.remove(0))),
                    ("Option", 1) if !self.program_declares("Option") => {
                        Ty::Option(Box::new(a.remove(0)))
                    }
                    ("Result", 2) if !self.program_declares("Result") => {
                        let e = a.pop().unwrap();
                        Ty::Result(Box::new(a.pop().unwrap()), Box::new(e))
                    }
                    ("Pair", 2) if !self.program_declares("Pair") => {
                        let b = a.pop().unwrap();
                        Ty::Pair(Box::new(a.pop().unwrap()), Box::new(b))
                    }
                    _ => Ty::Data(n.clone(), a),
                }
            }
            // A handler arm's operation generic: whatever the perform chose.
            TTy::Param(p, _) if matches!(p.id(), ParamId::Skolem { .. }) => Ty::Infer,
            TTy::Param(p, _) => match self.param_name(p).map(str::to_string) {
                Some(name) => Ty::Param(name),
                None => {
                    let message = format!(
                        "error: type parameter `{}` has no binding in the lowered declaration",
                        p.name()
                    );
                    if !self.build_errors.contains(&message) {
                        self.build_errors.push(message);
                    }
                    Ty::Infer
                }
            },
            TTy::Info(t) => Ty::Info(Box::new(self.conv(t))),
            TTy::Borrow(t, m) => {
                let inner = Box::new(self.conv(t));
                if *m {
                    Ty::RefMut(inner)
                } else {
                    Ty::Ref(inner)
                }
            }
            TTy::Var(_) => Ty::Infer,
        }
    }

    pub fn param_name(&self, p: &TParam) -> Option<&str> {
        self.param_names
            .get(p.id())
            .or_else(|| self.declaration_param_names.get(p.id()))
            .map(String::as_str)
    }

    /// Structural order with declaration-local output tokens instead of IDs.
    fn stable_type_key(&self, t: &TTy) -> TypeKey {
        let many = |ts: &[TTy]| ts.iter().map(|t| self.stable_type_key(t)).collect();
        match t {
            TTy::Int(w) => TypeKey::Int(*w),
            TTy::Bool => TypeKey::Bool,
            TTy::Text => TypeKey::Text,
            TTy::Unit => TypeKey::Unit,
            TTy::Never => TypeKey::Never,
            TTy::Decimal => TypeKey::Decimal,
            TTy::Float => TypeKey::Float,
            TTy::Float32 => TypeKey::Float32,
            TTy::Fn(ps, r, k) => TypeKey::Fn(many(ps), Box::new(self.stable_type_key(r)), *k),
            TTy::Union(ts) => {
                let mut keys: Vec<TypeKey> = many(ts);
                keys.sort();
                TypeKey::Union(keys)
            }
            TTy::Product(ts) => TypeKey::Product(many(ts)),
            TTy::Tagged(tags, t) => {
                TypeKey::Tagged(tags.clone(), Box::new(self.stable_type_key(t)))
            }
            TTy::Named(n, args) => TypeKey::Named(n.clone(), many(args)),
            TTy::Param(p, k) => TypeKey::Param(self.param_name(p).map(str::to_string), *k),
            TTy::Info(t) => TypeKey::Info(Box::new(self.stable_type_key(t))),
            TTy::Borrow(t, m) => TypeKey::Borrow(Box::new(self.stable_type_key(t)), *m),
            TTy::Var(_) => TypeKey::Infer,
            TTy::Poly(ps, t) => TypeKey::Poly(
                ps.iter()
                    .map(|(p, k)| (self.param_name(p).map(str::to_string), *k))
                    .collect(),
                Box::new(self.stable_type_key(t)),
            ),
            TTy::App(f, a) => TypeKey::App(
                Box::new(self.stable_type_key(f)),
                Box::new(self.stable_type_key(a)),
            ),
        }
    }

    /// The positions of a data type's generics that only its fields' effect
    /// rows mention.
    pub fn row_parameters(&self, name: &str) -> Vec<usize> {
        self.row_params.get(name).cloned().unwrap_or_default()
    }

    /// Refuses a constructor of an extern type (`extern { type T }`): only
    /// extern functions make its values.
    pub fn refuse_extern_type(&mut self, ctor: &str) {
        let host = self.program.stmts.iter().any(|s| {
            matches!(s, Stmt::Struct(d) if d.host && d.constructors.iter().any(|c| c.name == ctor))
        });
        let m = format!("error: {ctor} is an extern type; only extern functions make its values");
        if host && !self.build_errors.contains(&m) {
            self.build_errors.push(m);
        }
    }

    pub fn program_declares(&self, name: &str) -> bool {
        self.program.stmts.iter().any(|s| match s {
            Stmt::Struct(d) | Stmt::Enum(d) => d.name == name,
            _ => false,
        })
    }

    /// `conv`, with the tier a written function type gives its outermost
    /// function (under a borrow too).
    pub fn conv_in(&mut self, cx: &Cx, t: &TTy, declared: Option<&SurfaceTerm>) -> Ty {
        let mut out = self.conv(t);
        if let Some(declared) = declared {
            set_written_tiers(&mut out, declared, &mut |row| self.row_tier_in(row, cx));
        }
        out
    }

    pub fn union_id(&mut self, members: Vec<Ty>) -> Ty {
        if let Some(id) = self.union_ids.get(&members) {
            return Ty::Union(*id);
        }
        let id = self.unions.len();
        self.union_ids.insert(members.clone(), id);
        self.unions.push(UnionDef {
            id,
            members,
            kind: Kind::Shared,
        });
        Ty::Union(id)
    }

    pub fn ety(&mut self, t: &SurfaceTerm) -> Ty {
        match self.types.term(t) {
            Some(ty) => {
                let ty = ty.clone();
                self.conv(&ty)
            }
            None => Ty::Infer,
        }
    }

    pub fn use_of(&self, t: &TTy) -> Use {
        match t {
            TTy::Borrow(inner, _) => match &**inner {
                TTy::Param(..) => Use::Clone,
                inner => match self.kind_of(inner) {
                    Kind::Copy => Use::Copy,
                    _ => Use::Clone,
                },
            },
            TTy::Param(_, k) => {
                if k.dup() {
                    Use::Clone
                } else {
                    Use::Move
                }
            }
            // A function value is an `Rc`, even when what it captured is copy.
            TTy::Fn(..) if self.kind_of(t).dup() => Use::Clone,
            t => match self.kind_of(t) {
                Kind::Copy => Use::Copy,
                Kind::Shared => Use::Clone,
                Kind::Affine | Kind::Linear => Use::Move,
            },
        }
    }

    /// How the value a `Ref(x)` points at is read, when it may be: `None`
    /// when `x` is not duplicable.
    pub fn dup_use(&self, t: &Ty) -> Option<Use> {
        match t {
            Ty::Int(Width::Nat) | Ty::Text => Some(Use::Clone),
            Ty::Int(_) | Ty::Bool | Ty::Unit | Ty::Float | Ty::Float32 | Ty::Never => {
                Some(Use::Copy)
            }
            // A `Pending` is taken once (it can hold a thread's result), a guard is
            // the one holder of a lock.
            Ty::Std(n, _) => (n != "Pending" && n != "MutexGuard").then_some(Use::Clone),
            Ty::Fn(f) => f.kind.dup().then_some(Use::Clone),
            Ty::Option(a) => self.dup_use(a),
            Ty::Product(ms) => {
                let mut all_copy = true;
                for (_, m) in ms {
                    all_copy &= self.dup_use(m)? == Use::Copy;
                }
                Some(if all_copy { Use::Copy } else { Use::Clone })
            }
            Ty::Result(a, b) | Ty::Pair(a, b) => {
                let (x, y) = (self.dup_use(a)?, self.dup_use(b)?);
                Some(if x == Use::Copy && y == Use::Copy {
                    Use::Copy
                } else {
                    Use::Clone
                })
            }
            Ty::Data(n, args) => {
                let d = &self.datas[*self.data_index.get(n)?];
                if !d.clone {
                    return None;
                }
                let mut all = d.kind.dup();
                let mut copy = d.copy;
                for a in args {
                    match self.dup_use(a) {
                        Some(Use::Copy) => {}
                        Some(_) => copy = false,
                        None => all = false,
                    }
                }
                all.then_some(if copy { Use::Copy } else { Use::Clone })
            }
            Ty::Union(id) => {
                let mut copy = true;
                for m in &self.unions[*id].members {
                    match self.dup_use(m) {
                        Some(Use::Copy) => {}
                        Some(_) => copy = false,
                        None => return None,
                    }
                }
                Some(if copy { Use::Copy } else { Use::Clone })
            }
            Ty::Param(_) => Some(Use::Clone),
            Ty::Ref(_) => Some(Use::Copy),
            _ => None,
        }
    }

    pub fn build_datas(&mut self) -> R<()> {
        if self.rc_enabled {
            self.rc_datas = self.shared_datas();
        }
        let datas: &Datas = &self.types.datas;
        let mut names: Vec<&String> = datas.decls.keys().collect();
        names.sort();
        // Most syntax types belong only to compile-time macros. Start with
        // that exclusion, then retain the transitive dependencies of runtime
        // declarations (including generated ASTs and parser result types).
        let mut macro_only: HashSet<&str> = names
            .iter()
            .filter(|n| n.starts_with("Syn") && !self.program_declares(n))
            .map(|n| n.as_str())
            .collect();
        loop {
            let before = macro_only.len();
            for n in &names {
                let holds = datas.decls[*n]
                    .constructors
                    .iter()
                    .any(|c| c.fields.iter().any(|(_, t)| mentions_any(t, &macro_only)));
                if holds && !self.program_declares(n) {
                    macro_only.insert(n.as_str());
                }
            }
            if macro_only.len() == before {
                break;
            }
        }
        let mut runtime: HashSet<&str> = names
            .iter()
            .filter(|n| {
                self.program_declares(n)
                    || self.fns.iter().any(|(name, f)| {
                        f.origin == Origin::Program
                            && self
                                .types
                                .scheme(name)
                                .is_some_and(|s| mentions_any(&s.ty, &HashSet::from([n.as_str()])))
                    })
            })
            .map(|n| n.as_str())
            .collect();
        loop {
            let before = runtime.len();
            for candidate in &names {
                let singleton = HashSet::from([candidate.as_str()]);
                if names.iter().any(|n| {
                    runtime.contains(n.as_str())
                        && datas.decls[*n]
                            .constructors
                            .iter()
                            .any(|c| c.fields.iter().any(|(_, t)| mentions_any(t, &singleton)))
                }) {
                    runtime.insert(candidate.as_str());
                }
            }
            if before == runtime.len() {
                break;
            }
        }
        macro_only.retain(|n| !runtime.contains(n));
        let mut out = Vec::new();
        for name in names {
            let d = &datas.decls[name];
            if d.builtin {
                continue;
            }
            if matches!(name.as_str(), "Option" | "Result" | "Pair") && !self.program_declares(name)
            {
                continue;
            }
            if macro_only.contains(name.as_str()) {
                continue;
            }
            out.push(name.clone());
        }
        for name in out {
            let def = self.data_def(&name)?;
            self.data_index.insert(name, self.datas.len());
            self.datas.push(def);
        }
        self.box_large_fields();
        Ok(())
    }

    /// Whether the values of data `name` are shared, so that its fields
    /// behind an indirection are behind an `Rc`.
    fn shares(&self, name: &str) -> bool {
        let d = &self.types.datas.decls[name];
        let linear = TTy::Named(
            d.name.clone(),
            d.parameters()
                .into_iter()
                .map(|g| TTy::Param(g, Kind::Linear))
                .collect(),
        );
        self.types.datas.kind(&linear).dup() || self.rc_datas.contains(name)
    }

    /// Puts a large field of a shared data behind an `Rc`, as a recursive
    /// field already is. An enum is as large as its largest constructor,
    /// and a value is moved whole, so a constructor holding a large value
    /// inline makes every move of its type copy that much: a machine whose
    /// state holds its code and frames inline copies the state at each step.
    /// Behind an `Rc`, a move copies a pointer, and a clone shares the
    /// field instead of copying it. Only a data whose values are shared
    /// does this; an affine one keeps its fields owned and inline.
    /// The sizes are estimates in words, as `Ty` gives them; boxing a field
    /// makes its data smaller, so this runs until nothing more is boxed.
    fn box_large_fields(&mut self) {
        loop {
            let mut boxed = Vec::new();
            for (di, d) in self.datas.iter().enumerate() {
                if d.copy || d.view || d.host || !self.shares(&d.name) {
                    continue;
                }
                for (ci, c) in d.ctors.iter().enumerate() {
                    for (fi, f) in c.fields.iter().enumerate() {
                        if f.indirect == Indirect::None
                            && matches!(f.ty, Ty::Data(..))
                            && self.words(&f.ty, &[], &mut Vec::new()) > LARGE_FIELD_WORDS
                        {
                            boxed.push((di, ci, fi));
                        }
                    }
                }
            }
            if boxed.is_empty() {
                return;
            }
            for (di, ci, fi) in boxed {
                self.datas[di].ctors[ci].fields[fi].indirect = Indirect::Shared;
            }
        }
    }

    /// An estimate of the words a value of `t` takes inline; `env` gives
    /// the arguments of the data whose field `t` is.
    fn words(&self, t: &Ty, env: &[(&String, &Ty)], seen: &mut Vec<String>) -> usize {
        match t {
            Ty::Int(Width::Nat) => 2,
            Ty::Int(_) | Ty::Bool | Ty::Unit | Ty::Never | Ty::Float | Ty::Float32 => 1,
            Ty::Text | Ty::Buf | Ty::Vec(_) | Ty::Shown => 3,
            Ty::Array(_) | Ty::Slice(_) | Ty::Fn(_) => 2,
            Ty::Option(a) | Ty::BudgetAnswer(a) => 1 + self.words(a, env, seen),
            Ty::Result(a, b) => 1 + self.words(a, env, seen).max(self.words(b, env, seen)),
            Ty::Pair(a, b) => self.words(a, env, seen) + self.words(b, env, seen),
            Ty::Product(ms) => ms.iter().map(|(_, t)| self.words(t, env, seen)).sum(),
            Ty::Info(a) => self.words(a, env, seen),
            Ty::Param(p) => match env.iter().find(|(g, _)| *g == p) {
                Some((_, a)) => self.words(a, &[], seen),
                None => 1,
            },
            Ty::Data(n, args) => {
                let Some(d) = self.data_index.get(n).map(|i| &self.datas[*i]) else {
                    return 3;
                };
                if seen.contains(n) {
                    return 1;
                }
                // The arguments are in terms of the enclosing data's own.
                let args: Vec<Ty> = args
                    .iter()
                    .map(|a| match a {
                        Ty::Param(p) => env
                            .iter()
                            .find(|(g, _)| *g == p)
                            .map_or_else(|| a.clone(), |(_, t)| (*t).clone()),
                        _ => a.clone(),
                    })
                    .collect();
                let inner: Vec<(&String, &Ty)> = d.generics.iter().zip(args.iter()).collect();
                seen.push(n.clone());
                let largest = d
                    .ctors
                    .iter()
                    .map(|c| {
                        c.fields
                            .iter()
                            .map(|f| match f.indirect {
                                Indirect::None => self.words(&f.ty, &inner, seen),
                                _ => 1,
                            })
                            .sum::<usize>()
                    })
                    .max()
                    .unwrap_or(0);
                seen.pop();
                largest + usize::from(!d.is_struct && d.ctors.len() > 1)
            }
            _ => 1,
        }
    }

    /// The recursive generic data (`List(A)`, a map) that the program only
    /// ever fills with values that can be cloned: its cells share their tails
    /// (`Rc`), so a clone of it, and a `match` on one, take a step and not
    /// the whole structure. A program that fills it with an affine or linear
    /// value keeps the owned (`Box`) cells.
    fn shared_datas(&self) -> HashSet<String> {
        let datas = &self.types.datas;
        let mut candidates: HashSet<String> = datas
            .decls
            .iter()
            .filter(|(_, d)| {
                !d.builtin
                    && d.recursive
                    && !d.generics.is_empty()
                    && datas
                        .no_clone(&TTy::Named(
                            d.name.clone(),
                            d.parameters()
                                .into_iter()
                                .map(|g| TTy::Param(g, Kind::Shared))
                                .collect(),
                        ))
                        .is_none()
                    && !(matches!(d.name.as_str(), "Option" | "Result" | "Pair")
                        && !self.program_declares(&d.name))
            })
            .map(|(n, _)| n.clone())
            .collect();
        fn concrete(t: &TTy) -> bool {
            match t {
                TTy::Param(..) | TTy::Var(_) => false,
                TTy::Fn(ps, r, _) => ps.iter().all(concrete) && concrete(r),
                TTy::Union(ts) => ts.iter().all(concrete),
                TTy::Tagged(_, t) | TTy::Info(t) | TTy::Borrow(t, _) => concrete(t),
                TTy::Named(_, args) => args.iter().all(concrete),
                _ => true,
            }
        }
        fn visit(datas: &Datas, t: &TTy, candidates: &mut HashSet<String>) {
            match t {
                TTy::Named(n, args) => {
                    if args.iter().any(|a| concrete(a) && !datas.kind(a).dup()) {
                        candidates.remove(n);
                    }
                    for a in args {
                        visit(datas, a, candidates);
                    }
                }
                TTy::Fn(ps, r, _) => {
                    for p in ps {
                        visit(datas, p, candidates);
                    }
                    visit(datas, r, candidates);
                }
                TTy::Union(ts) => {
                    for t in ts {
                        visit(datas, t, candidates);
                    }
                }
                TTy::Tagged(_, t) | TTy::Info(t) | TTy::Borrow(t, _) => visit(datas, t, candidates),
                _ => {}
            }
        }
        for t in self.types.terms.values().chain(self.types.locals.values()) {
            visit(datas, t, &mut candidates);
        }
        for s in self.types.schemes.values() {
            visit(datas, &s.ty, &mut candidates);
        }
        candidates
    }

    fn data_def(&mut self, name: &str) -> R<DataDef> {
        let d: Data = self.types.datas.decls[name].clone();
        let params = |k: Kind| -> TTy {
            TTy::Named(
                d.name.clone(),
                d.parameters()
                    .into_iter()
                    .map(|g| TTy::Param(g, k))
                    .collect(),
            )
        };
        let kind = self.types.datas.kind(&params(Kind::Copy));
        let clone = self.types.datas.no_clone(&params(Kind::Shared)).is_none();
        let rc = self.shares(&d.name);
        let mut ctors = Vec::new();
        for (ci, c) in d.constructors.iter().enumerate() {
            let rows = self.field_rows(&d.name, ci);
            let written = self.field_terms(&d.name, ci);
            let mut fields = Vec::new();
            for (fi, (n, f)) in c.fields.iter().enumerate() {
                let indirect = if self.inline_reaches(f, &d.name, &mut HashSet::new()) {
                    if rc {
                        Indirect::Shared
                    } else {
                        Indirect::Unique
                    }
                } else {
                    Indirect::None
                };
                let mut ty = self.conv(f);
                // A function in a type argument of the field (`Option(() -> () ! {e})`)
                // keeps the tier of the row written on it.
                let mut nested_m = false;
                if let Some(written) = written.get(fi) {
                    set_written_tiers_in_args(&mut ty, written, &mut |row| {
                        let tier = self.field_tier(row);
                        nested_m |= tier == Tier::M;
                        tier
                    });
                }
                if nested_m {
                    return Err(Unsupported {
                        what: msg!("nir-field-resumes-more-than-once", data = d.name.as_str())
                            .to_string(),
                        span: None,
                    });
                }
                if let Some(Some(row)) = rows.get(fi) {
                    let tier = self.field_tier(row);
                    if tier == Tier::M {
                        return Err(Unsupported {
                            what: msg!("nir-field-resumes-more-than-once", data = d.name.as_str())
                                .to_string(),
                            span: None,
                        });
                    }
                    set_fn_tier(&mut ty, tier);
                }
                fields.push(FieldDef {
                    name: n.clone(),
                    ty,
                    indirect,
                });
            }
            ctors.push(CtorDef {
                name: c.name.clone(),
                fields,
            });
        }
        let rows = self.row_parameters(&d.name);
        Ok(DataDef {
            name: d.name.clone(),
            generics: d
                .generics
                .iter()
                .enumerate()
                .filter(|(i, _)| !rows.contains(i))
                .map(|(_, g)| g.clone())
                .collect(),
            kind,
            is_struct: d.is_struct,
            ctors,
            clone,
            copy: kind == Kind::Copy && !d.recursive,
            linear: d.declared == Some(Kind::Linear),
            view: d.view,
            host: self
                .program
                .stmts
                .iter()
                .any(|s| matches!(s, Stmt::Struct(x) if x.host && x.name == d.name)),
        })
    }

    /// Whether a value of type `t` holds a value of `owner` without an
    /// indirection (so the field needs one).
    fn inline_reaches(&self, t: &TTy, owner: &str, seen: &mut HashSet<String>) -> bool {
        self.reaches(t, owner, seen, &[])
    }

    /// `env` gives the arguments of the data whose field `t` is, by its
    /// parameters: `List(A)` holds an `A`, so a `List(Ty)` holds a `Ty`.
    fn reaches(
        &self,
        t: &TTy,
        owner: &str,
        seen: &mut HashSet<String>,
        env: &[(&ParamId, &TTy)],
    ) -> bool {
        match t {
            TTy::Param(p, _) => env
                .iter()
                .find(|(g, _)| *g == p.id())
                .is_some_and(|(_, arg)| self.reaches(arg, owner, seen, &[])),
            TTy::Named(n, args) => {
                if matches!(n.as_str(), "Option" | "Result" | "Pair") && !self.program_declares(n) {
                    return args.iter().any(|a| self.reaches(a, owner, seen, env));
                }
                if n == owner {
                    return true;
                }
                let Some(d) = self.types.datas.decls.get(n) else {
                    return false;
                };
                if d.builtin || !seen.insert(format!("{n}{args:?}")) {
                    return false;
                }
                // The arguments are in terms of the enclosing data's own.
                let args: Vec<TTy> = args
                    .iter()
                    .map(|a| match a {
                        TTy::Param(p, _) => env
                            .iter()
                            .find(|(g, _)| *g == p.id())
                            .map_or_else(|| a.clone(), |(_, arg)| (*arg).clone()),
                        _ => a.clone(),
                    })
                    .collect();
                let parameters = d.parameters();
                let inner: Vec<(&ParamId, &TTy)> =
                    parameters.iter().map(|p| p.id()).zip(args.iter()).collect();
                d.constructors.iter().any(|c| {
                    c.fields
                        .iter()
                        .any(|(_, f)| self.reaches(f, owner, seen, &inner))
                })
            }
            TTy::Union(ts) => ts.iter().any(|t| self.reaches(t, owner, seen, env)),
            // A product holds its members in place.
            TTy::Product(ts) => ts.iter().any(|t| self.reaches(t, owner, seen, env)),
            TTy::Tagged(_, t) => self.reaches(t, owner, seen, env),
            _ => false,
        }
    }

    pub fn ctor_ref(&self, name: &str) -> Option<CtorRef> {
        self.ctor_ref_in(name, None)
    }

    pub fn ctor_ref_in(&self, name: &str, ty: Option<&TTy>) -> Option<CtorRef> {
        let (d, i) = self.types.datas.resolve_ctor(name, ty).ok()?;
        let decl = &self.types.datas.decls[d];
        let c = &decl.constructors[*i];
        let data = match d.as_str() {
            "Option" if !self.program_declares("Option") => DataRef::Option,
            "Result" if !self.program_declares("Result") => DataRef::Result,
            "Pair" if !self.program_declares("Pair") => DataRef::Pair,
            _ => DataRef::Gen(d.clone()),
        };
        let (indirect, linear) = match self.data_index.get(d) {
            Some(ix) => {
                let def = &self.datas[*ix];
                (
                    def.ctors[*i].fields.iter().map(|f| f.indirect).collect(),
                    def.linear,
                )
            }
            None => (vec![Indirect::None; c.fields.len()], false),
        };
        Some(CtorRef {
            data,
            name: c.name.clone(),
            index: *i,
            indirect,
            linear,
            fields: c.fields.iter().map(|(n, _)| n.clone()).collect(),
            nullary: c.fields.is_empty() && !decl.is_struct,
        })
    }

    /// The field types of constructor `ctor` of the type `ty`.
    /// The rows written on the function types of a constructor's fields:
    /// `None` for a field that is not a function or has no written row.
    pub fn ctor_field_rows(&self, ctor: &str, ty: &TTy) -> Vec<Option<Row>> {
        match self.types.datas.resolve_ctor(ctor, Some(ty)) {
            Ok((d, i)) => self.field_rows(d, *i),
            Err(_) => Vec::new(),
        }
    }

    fn field_terms(&self, data: &str, ctor: usize) -> Vec<SurfaceTerm> {
        for s in &self.program.stmts {
            if let Stmt::Struct(d) | Stmt::Enum(d) = s
                && d.name == data
                && let Some(c) = d.constructors.get(ctor)
            {
                return c.fields.iter().map(|(_, t)| t.clone()).collect();
            }
        }
        Vec::new()
    }

    fn field_rows(&self, data: &str, ctor: usize) -> Vec<Option<Row>> {
        for s in &self.program.stmts {
            if let Stmt::Struct(d) | Stmt::Enum(d) = s
                && d.name == data
                && let Some(c) = d.constructors.get(ctor)
            {
                return c
                    .fields
                    .iter()
                    .map(|(_, t)| pi_effects(t).map(|e| self.carried_field_row(data, e)))
                    .collect();
            }
        }
        Vec::new()
    }

    /// The tier of the function in the field `name` of a value of type `base`,
    /// when its type is written with a row.
    pub fn named_field_tier(&self, base: &TTy, name: &str) -> Option<Tier> {
        self.named_field_row(base, name)
            .map(|row| self.field_tier(&row))
    }

    /// The row written on the function type of the field `name` of a value
    /// of type `base`.
    pub fn named_field_row(&self, base: &TTy, name: &str) -> Option<Row> {
        let TTy::Named(data, _) = base.unborrowed() else {
            return None;
        };
        self.program.stmts.iter().find_map(|s| match s {
            Stmt::Struct(d) | Stmt::Enum(d) if d.name == *data => {
                d.constructors.iter().find_map(|c| {
                    c.fields.iter().find_map(|(n, t)| {
                        (n.as_deref() == Some(name))
                            .then(|| pi_effects(t))
                            .flatten()
                            .map(|e| self.carried_field_row(data, e))
                    })
                })
            }
            _ => None,
        })
    }

    /// The row of a field's function as the program writes it, with its row
    /// variables read as the tier `data` carries (`Lowerer::carried`).
    fn carried_field_row(&self, data: &str, effects: Vec<String>) -> Row {
        let Some(&tier) = self.carried.get(data) else {
            return effects.into_iter().collect();
        };
        effects
            .into_iter()
            .map(|e| {
                if e.starts_with('|') {
                    super::carried_row(tier)
                } else {
                    e
                }
            })
            .collect()
    }

    /// The tier of a function held in a field: a data type has no handlers
    /// in place, so its row alone decides.
    pub fn field_tier(&self, row: &Row) -> Tier {
        self.row_tier(row, &HashMap::new())
    }

    pub fn ctor_fields(&self, ctor: &str, ty: &TTy) -> Vec<TTy> {
        let Ok((d, i)) = self.types.datas.resolve_ctor(ctor, Some(ty)) else {
            return Vec::new();
        };
        let args = match ty.unborrowed() {
            TTy::Named(n, args) if n == d => args.clone(),
            _ => Vec::new(),
        };
        self.types
            .datas
            .fields(d, *i, &args)
            .into_iter()
            .map(|(_, t)| t)
            .collect()
    }
}

/// Sets the tier of each function the written type `declared` gives a row:
/// the outermost one (under a borrow too) and those in its type arguments.
pub(crate) fn set_written_tiers(
    t: &mut Ty,
    declared: &SurfaceTerm,
    tier_of: &mut dyn FnMut(&Row) -> Tier,
) {
    if let Some(effects) = pi_effects(declared) {
        let row: Row = effects.into_iter().collect();
        set_fn_tier(t, tier_of(&row));
        return;
    }
    set_written_tiers_in_args(t, declared, tier_of);
}

/// `set_written_tiers` for the type arguments of `declared` only, paired
/// with those of `t` when both have them in the same number.
pub(crate) fn set_written_tiers_in_args(
    t: &mut Ty,
    declared: &SurfaceTerm,
    tier_of: &mut dyn FnMut(&Row) -> Tier,
) {
    let declared = match &*declared.kind {
        TermKind::Borrow { term, .. } => {
            if let Ty::Ref(i) | Ty::RefMut(i) = t {
                return set_written_tiers_in_args(i, term, tier_of);
            }
            return;
        }
        _ => declared,
    };
    let TermKind::App { arguments, .. } = &*declared.kind else {
        return;
    };
    let args: Vec<&mut Ty> = match t {
        Ty::Vec(a) | Ty::Array(a) | Ty::Slice(a) | Ty::Option(a) => vec![&mut **a],
        Ty::Result(a, b) | Ty::Pair(a, b) | Ty::HashMap(a, b) => vec![&mut **a, &mut **b],
        Ty::Std(_, a) | Ty::Data(_, a) => a.iter_mut().collect(),
        _ => return,
    };
    // A row parameter has no Rust type, so the counts differ and the
    // arguments cannot be paired by position.
    if args.len() != arguments.len() {
        return;
    }
    for (a, d) in args.into_iter().zip(arguments) {
        set_written_tiers(a, d, tier_of);
    }
}

pub(crate) fn set_fn_tier(t: &mut Ty, tier: Tier) {
    match t {
        Ty::Fn(f) => f.tier = tier,
        Ty::Ref(i) | Ty::RefMut(i) => set_fn_tier(i, tier),
        _ => {}
    }
}

fn mentions_any(t: &TTy, names: &HashSet<&str>) -> bool {
    match t {
        TTy::Named(n, args) => {
            names.contains(n.as_str()) || args.iter().any(|a| mentions_any(a, names))
        }
        TTy::Fn(ps, r, _) => ps.iter().any(|p| mentions_any(p, names)) || mentions_any(r, names),
        TTy::Union(ts) => ts.iter().any(|a| mentions_any(a, names)),
        TTy::Tagged(_, a) | TTy::Info(a) | TTy::Borrow(a, _) => mentions_any(a, names),
        _ => false,
    }
}
