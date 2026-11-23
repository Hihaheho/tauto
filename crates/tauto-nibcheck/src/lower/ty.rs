use std::collections::HashSet;

use crate::types::{Data, Kind, Ty as TTy};
use tauto_surface::surface::SurfaceTerm;

use super::*;

/// A field of more words than this goes behind an `Rc` (`box_large_fields`).
const LARGE_FIELD_WORDS: usize = 8;

/// The data a `&rc T` is lowered to: a struct of one field, `value`, behind
/// a shared box, so that every copy shares the box and the last one drops
/// the contents. `&rc` is no name a program can declare.
pub(crate) fn rc_box_name() -> Name {
    Name::from("&rc")
}

pub(crate) const RC_FIELD: &str = "value";

pub(crate) fn rc_box_def() -> DataDef {
    DataDef {
        name: rc_box_name(),
        generics: vec!["T".to_string()],
        kind: Kind::Shared,
        is_struct: true,
        ctors: vec![CtorDef {
            name: rc_box_name(),
            fields: vec![FieldDef {
                name: Some(RC_FIELD.to_string()),
                ty: Ty::Param("T".to_string()),
                indirect: Indirect::Shared,
            }],
        }],
        clone: true,
        copy: false,
        linear: false,
        view: false,
        host: false,
        shown: String::new(),
    }
}

pub(crate) fn rc_box_ctor() -> CtorRef {
    CtorRef {
        data: DataRef::Gen(rc_box_name()),
        name: rc_box_name(),
        index: 0,
        indirect: vec![Indirect::Shared],
        linear: false,
        fields: vec![Some(RC_FIELD.to_string())],
        nullary: false,
    }
}

/// The field a borrow of the contents of a `&rc T` goes through.
pub(crate) fn rc_field() -> FieldRef {
    FieldRef {
        name: RC_FIELD.to_string(),
        index: None,
        indirect: Indirect::Shared,
    }
}

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
    Tagged(BTreeSet<String>, Box<TypeKey>),
    Named(String, Vec<TypeKey>),
    Param(Option<String>, Kind),
    Info(Box<TypeKey>),
    Borrow(Box<TypeKey>, bool),
    Rc(Box<TypeKey>),
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
                // The build is refused: the type is not read.
                Ty::Never
            }
            // The dictionary of a method with generics of its own: the rust
            // backend does not write these.
            TTy::Poly(..) | TTy::App(..) => {
                let m = "error: a class method with generics or a type constructor variable is not supported by the rust backend"
                    .to_string();
                if !self.build_errors.contains(&m) {
                    self.build_errors.push(m);
                }
                // The build is refused: the type is not read.
                Ty::Never
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
                if matches!(n, Name::Global(_))
                    && !tauto_surface::bindings::is_library(n, n.as_str())
                {
                    return Ty::Data(n.clone(), a);
                }
                match (n.as_str(), a.len()) {
                    // The library's `Nat` runs as the language's unbounded
                    // natural number, as a `nat` written in Nib does.
                    ("Nat", 0) => Ty::Int(Width::Nat),
                    ("Buf", 0) => Ty::Buf,
                    ("Vec", 1) => Ty::Vec(Box::new(a.remove(0))),
                    ("Array", 1) => Ty::Array(Box::new(a.remove(0))),
                    ("SynDeclaration", 0) => Ty::Std(StdType::SynDeclaration, a),
                    ("Ref", 1) => Ty::Std(StdType::Ref, a),
                    ("Weak", 1) => Ty::Std(StdType::Weak, a),
                    ("Mutex", 1) => Ty::Std(StdType::Mutex, a),
                    ("MutexGuard", 1) => Ty::Std(StdType::MutexGuard, a),
                    ("Atomic", 0) => Ty::Std(StdType::Atomic, a),
                    ("Bytes", 0) => Ty::Std(StdType::Bytes, a),
                    ("Pending", 1) => Ty::Std(StdType::Pending, a),
                    ("Secret", 1) => Ty::Std(StdType::Secret, a),
                    // Regions and their places are the runtime's; the policy's
                    // state stays with whoever made it
                    // (`std/builtin/region.taut`).
                    ("Region", 1) => Ty::Std(StdType::Region, Vec::new()),
                    ("Place", 1) => Ty::Std(StdType::Place, a),
                    ("RcRegion", 1) => Ty::Std(StdType::RcRegion, Vec::new()),
                    ("RcPlace", 1) => Ty::Std(StdType::RcPlace, a),
                    ("Slots", 3) => Ty::Std(StdType::Slots, a),
                    // `SlotsModel` of `std/slots.taut` written in a program's
                    // type: its fourth argument is the policy's `used`, which
                    // `Slots` leaves to the proofs.
                    ("Slots", 4) => {
                        a.pop();
                        Ty::Std(StdType::Slots, a)
                    }
                    ("Signal", 0) => Ty::Std(StdType::Signal, a),
                    ("CancelSource", 0)
                        if !self.program_declares(&tauto_surface::bindings::library_name(
                            "CancelSource",
                        )) =>
                    {
                        Ty::Std(StdType::CancelSource, a)
                    }
                    ("Slice", 1) => Ty::Slice(Box::new(a.remove(0))),
                    ("Option", 1)
                        if !self
                            .program_declares(&tauto_surface::bindings::library_name("Option")) =>
                    {
                        Ty::Option(Box::new(a.remove(0)))
                    }
                    ("Result", 2)
                        if !self
                            .program_declares(&tauto_surface::bindings::library_name("Result")) =>
                    {
                        let e = a.pop().unwrap();
                        Ty::Result(Box::new(a.pop().unwrap()), Box::new(e))
                    }
                    ("Pair", 2)
                        if !self
                            .program_declares(&tauto_surface::bindings::library_name("Pair")) =>
                    {
                        let b = a.pop().unwrap();
                        Ty::Pair(Box::new(a.pop().unwrap()), Box::new(b))
                    }
                    _ => Ty::Data(n.clone(), a),
                }
            }
            // A handler arm's operation generic: whatever the perform chose.
            // `arms::instantiate` writes the arm once for each type it is
            // given.
            TTy::Param(p, _) if let ParamId::Skolem { serial } = p.id() => {
                Ty::Param(tauto_nir::arms::skolem(*serial))
            }
            TTy::Param(p, _) if let Some(t) = self.param_values.get(p.id()) => t.clone(),
            TTy::Param(p, _)
                if self.param_names.get(p.id()).is_none()
                    && let Some(skolems) = &mut self.host_skolems =>
            {
                let next = skolems.len();
                let serial = *skolems.entry(p.id().clone()).or_insert(next);
                Ty::Param(tauto_nir::arms::skolem(
                    super::handle::HOST_SKOLEM_BASE + serial,
                ))
            }
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
                    Ty::Never
                }
            },
            TTy::Info(t) => Ty::Info(Box::new(self.conv(t))),
            // The backends do not write `&orig` yet; it points at
            // the owner.
            TTy::Orig(t) => Ty::Ref(Box::new(self.conv(t))),
            TTy::Rc(t) => {
                self.rc_box = true;
                Ty::Data(rc_box_name(), vec![self.conv(t)])
            }
            TTy::Borrow(t, m) => {
                let inner = Box::new(self.conv(t));
                if *m {
                    Ty::RefMut(inner)
                } else {
                    Ty::Ref(inner)
                }
            }
            // A type the checker left open: nothing in the program fixes it,
            // so no value of it is made, and `Never` is one of the types it
            // may be.
            TTy::Var(_) => Ty::Never,
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
            TTy::Tagged(tags, t) => {
                TypeKey::Tagged(tags.clone(), Box::new(self.stable_type_key(t)))
            }
            TTy::Named(n, args) => TypeKey::Named(n.to_string(), many(args)),
            TTy::Param(p, k) => TypeKey::Param(self.param_name(p).map(str::to_string), *k),
            TTy::Info(t) => TypeKey::Info(Box::new(self.stable_type_key(t))),
            TTy::Borrow(t, m) => TypeKey::Borrow(Box::new(self.stable_type_key(t)), *m),
            TTy::Orig(t) => TypeKey::Borrow(Box::new(self.stable_type_key(t)), false),
            TTy::Rc(t) => TypeKey::Rc(Box::new(self.stable_type_key(t))),
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
    pub fn row_parameters(&self, name: &Name) -> Vec<usize> {
        self.row_params.get(name).cloned().unwrap_or_default()
    }

    /// Refuses a constructor of an extern type (`extern { type T }`): only
    /// extern functions make its values. Also seals replaceable extern
    /// `struct`/`enum` to their block's functions.
    pub fn refuse_extern_type(&mut self, ctor: &Name) {
        if let Some(owner) = self.program.stmts.iter().find_map(|s| match s {
            Stmt::Struct(d)
                if d.host
                    && (d.name.as_str() == ctor.as_str()
                        || d.constructors
                            .iter()
                            .any(|c| c.name.as_str() == ctor.as_str())) =>
            {
                Some(d.name.clone())
            }
            _ => None,
        }) {
            let m = format!("{owner} is an extern type; only extern functions make its values");
            if !self.build_errors.contains(&m) {
                self.build_errors.push(m);
            }
            return;
        }
        let accessor = self.current_fn.clone();
        self.refuse_sealed_repr(ctor, accessor.as_ref());
    }

    /// Refuses construction, projection, update, or match on a replaceable
    /// extern type outside its block.
    pub fn refuse_sealed_repr(&mut self, data_or_ctor: &Name, accessor: Option<&Name>) {
        let blocks =
            tauto_surface::surface::extern_blocks::ExternBlocks::collect(&self.program.stmts);
        // Match by spelling: pushed `Stmt::Struct` copies resolve to `Global`,
        // while the `extern` block's own decls may still be `Spelled`.
        let owner = self.program.stmts.iter().find_map(|s| match s {
            Stmt::Struct(d) | Stmt::Enum(d)
                if d.name.as_str() == data_or_ctor.as_str()
                    || d.constructors
                        .iter()
                        .any(|c| c.name.as_str() == data_or_ctor.as_str()) =>
            {
                Some(d.name.clone())
            }
            _ => None,
        });
        let Some(owner) = owner else {
            return;
        };
        if tauto_surface::surface::extern_blocks::may_access_repr(&blocks, &owner, accessor) {
            return;
        }
        if blocks.replaceable_data(&owner).is_none() {
            return;
        }
        let m =
            tauto_message::msg!("surface-extern-repr-sealed", name = owner.to_string()).to_string();
        if !self.build_errors.contains(&m) {
            self.build_errors.push(m);
        }
    }

    pub fn program_declares(&self, name: &Name) -> bool {
        self.program.stmts.iter().any(|s| match s {
            Stmt::Struct(d) | Stmt::Enum(d) => &d.name == name,
            _ => false,
        })
    }

    /// `conv`, with the tier a written function type gives its outermost
    /// function (under a borrow too).
    pub fn conv_in(&mut self, cx: &Cx, t: &TTy, declared: Option<&SurfaceTerm>) -> Ty {
        let mut out = self.conv(t);
        if let Some(declared) = declared {
            self.written_tiers(&mut out, declared, cx);
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
            None => self.untyped(t),
        }
    }

    /// A term the checker recorded no type for: the build is refused.
    pub fn untyped(&mut self, t: &SurfaceTerm) -> Ty {
        let m = format!(
            "error: the term at byte {} has no checked type",
            t.span.start
        );
        if !self.build_errors.contains(&m) {
            self.build_errors.push(m);
        }
        Ty::Never
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
            Ty::Std(n, _) => (!n.taken_once()).then_some(Use::Clone),
            Ty::Fn(f) => f.kind.dup().then_some(Use::Clone),
            Ty::Option(a) => self.dup_use(a),
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
        let mut names: Vec<&Name> = datas.decls.keys().collect();
        names.sort();
        // Most syntax types belong only to compile-time macros. Start with
        // that exclusion, then retain the transitive dependencies of runtime
        // declarations (including generated ASTs and parser result types).
        let mut macro_only: HashSet<Name> = names
            .iter()
            .filter(|n| {
                n.starts_with("Syn")
                    && tauto_surface::bindings::is_library(n, n.as_str())
                    && !self.program_declares(n)
            })
            .map(|n| (*n).clone())
            .collect();
        loop {
            let before = macro_only.len();
            for n in &names {
                let holds = datas.decls[*n]
                    .constructors
                    .iter()
                    .any(|c| c.fields.iter().any(|(_, t)| mentions_any(t, &macro_only)));
                if holds && !self.program_declares(n) {
                    macro_only.insert((*n).clone());
                }
            }
            if macro_only.len() == before {
                break;
            }
        }
        let mut occurrences = HashSet::new();
        for statement in &self.program.stmts {
            tauto_surface::surface::walk::stmt(&mut statement.clone(), &mut |term| {
                occurrences.insert(term.id());
            });
        }
        let mut runtime: HashSet<Name> = names
            .iter()
            .filter(|n| {
                self.program_declares(n)
                    || self.types.terms.iter().any(|(site, ty)| {
                        occurrences.contains(site)
                            && mentions_any(ty, &HashSet::from([(**n).clone()]))
                    })
                    || self.fns.iter().any(|(name, f)| {
                        f.origin == Origin::Program
                            && self.types.scheme(name).is_some_and(|s| {
                                mentions_any(&s.ty, &HashSet::from([(**n).clone()]))
                            })
                    })
            })
            .map(|n| (*n).clone())
            .collect();
        loop {
            let before = runtime.len();
            for candidate in &names {
                let singleton = HashSet::from([(*candidate).clone()]);
                if names.iter().any(|n| {
                    runtime.contains(*n)
                        && datas.decls[*n]
                            .constructors
                            .iter()
                            .any(|c| c.fields.iter().any(|(_, t)| mentions_any(t, &singleton)))
                }) {
                    runtime.insert((*candidate).clone());
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
            if (tauto_surface::bindings::is_library(&name, "Option")
                || tauto_surface::bindings::is_library(&name, "Result")
                || tauto_surface::bindings::is_library(&name, "Pair"))
                && !self.program_declares(name)
            {
                continue;
            }
            if macro_only.contains(name) {
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
    fn shares(&self, name: &Name) -> bool {
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
    fn words(&self, t: &Ty, env: &[(&String, &Ty)], seen: &mut Vec<Name>) -> usize {
        match t {
            Ty::Int(Width::Nat) => 2,
            Ty::Int(_) | Ty::Bool | Ty::Unit | Ty::Never | Ty::Float | Ty::Float32 => 1,
            Ty::Text | Ty::Buf | Ty::Vec(_) | Ty::Shown => 3,
            Ty::Array(_) | Ty::Slice(_) | Ty::Fn(_) => 2,
            Ty::Option(a) | Ty::BudgetAnswer(a) => 1 + self.words(a, env, seen),
            Ty::Result(a, b) => 1 + self.words(a, env, seen).max(self.words(b, env, seen)),
            Ty::Pair(a, b) => self.words(a, env, seen) + self.words(b, env, seen),
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
    fn shared_datas(&self) -> HashSet<Name> {
        let datas = &self.types.datas;
        let mut candidates: HashSet<Name> = datas
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
                    && !((tauto_surface::bindings::is_library(&d.name, "Option")
                        || tauto_surface::bindings::is_library(&d.name, "Result")
                        || tauto_surface::bindings::is_library(&d.name, "Pair"))
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
        fn visit(datas: &Datas, t: &TTy, candidates: &mut HashSet<Name>) {
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

    /// `A` for a field `&A` of a duplicable, known `A`: the field holds the
    /// value (`&A ≡ A`), so that the owner may change while it lives.
    pub(crate) fn plain_borrow(&self, t: &TTy) -> Option<TTy> {
        match t {
            TTy::Borrow(inner, false) if !mentions_param(inner) && self.kind_of(inner).dup() => {
                Some((**inner).clone())
            }
            _ => None,
        }
    }

    /// Whether data `name` holds a borrow the backend sees: a field that is
    /// a borrow other than `&A` of a duplicable `A`, or holds such data.
    fn holds_seen_borrow(&self, name: &Name, seen: &mut Vec<Name>) -> bool {
        let Some(d) = self.types.datas.decls.get(name) else {
            return false;
        };
        if !d.view || seen.contains(name) {
            return false;
        }
        if d.constructors.iter().all(|c| c.fields.is_empty()) {
            return true;
        }
        seen.push(name.clone());
        let found = d
            .constructors
            .iter()
            .flat_map(|c| c.fields.iter())
            .any(|(_, f)| self.ty_holds_seen_borrow(f, seen));
        seen.pop();
        found
    }

    fn ty_holds_seen_borrow(&self, t: &TTy, seen: &mut Vec<Name>) -> bool {
        match t {
            TTy::Borrow(..) => self.plain_borrow(t).is_none(),
            TTy::Named(n, args) => {
                // Only a field itself is read as the value of a `&A` of a
                // duplicable `A`; a borrow in an argument stays a borrow
                // (`List(&u64)`).
                self.holds_seen_borrow(n, seen)
                    || args
                        .iter()
                        .any(|a| matches!(a, TTy::Borrow(..)) || self.ty_holds_seen_borrow(a, seen))
            }
            _ => false,
        }
    }

    fn data_def(&mut self, name: &Name) -> R<DataDef> {
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
                let mut ty = match self.plain_borrow(f) {
                    Some(plain) => self.conv(&plain),
                    None => self.conv(f),
                };
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
                        what: msg!("nir-field-resumes-more-than-once", data = d.name.as_str()),
                        span: None,
                    });
                }
                if let Some(Some(row)) = rows.get(fi) {
                    let tier = self.field_tier(row);
                    if tier == Tier::M {
                        return Err(Unsupported {
                            what: msg!("nir-field-resumes-more-than-once", data = d.name.as_str()),
                            span: None,
                        });
                    }
                    set_fn_tier(&mut ty, tier);
                }
                // Its function's parameters of function type are taken at
                // the tiers the rows written on them carry.
                if let Ty::Fn(function) = &mut ty {
                    let carried = self.carried.contains_key(&d.name);
                    for (p, row) in function
                        .params
                        .iter_mut()
                        .zip(self.field_param_rows(&d.name, ci, fi))
                    {
                        if let Some(row) = row
                            && let Some(tier) = self.field_param_tier(carried, &row)
                        {
                            set_fn_tier(p, tier);
                        }
                    }
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
        // A view holds a borrow the backend sees: not one whose borrows are
        // all of duplicable values, held as the values.
        let view = self.holds_seen_borrow(&d.name, &mut Vec::new());
        Ok(DataDef {
            name: d.name.clone(),
            generics: d
                .generics
                .iter()
                .enumerate()
                .filter(|(i, _)| !rows.contains(i))
                .map(|(_, g)| g.to_string())
                .collect(),
            kind,
            is_struct: d.is_struct,
            ctors,
            clone,
            copy: kind == Kind::Copy && !d.recursive,
            linear: d.declared == Some(Kind::Linear),
            view,
            host: self
                .program
                .stmts
                .iter()
                .any(|s| matches!(s, Stmt::Struct(x) if x.host && x.name == d.name)),
            shown: if d.is_struct {
                display_name(&d.name).to_string()
            } else {
                String::new()
            },
        })
    }

    /// Whether a value of type `t` holds a value of `owner` without an
    /// indirection (so the field needs one).
    fn inline_reaches(&self, t: &TTy, owner: &Name, seen: &mut HashSet<(Name, Vec<TTy>)>) -> bool {
        self.reaches(t, owner, seen, &[])
    }

    /// `env` gives the arguments of the data whose field `t` is, by its
    /// parameters: `List(A)` holds an `A`, so a `List(Ty)` holds a `Ty`.
    fn reaches(
        &self,
        t: &TTy,
        owner: &Name,
        seen: &mut HashSet<(Name, Vec<TTy>)>,
        env: &[(&ParamId, &TTy)],
    ) -> bool {
        match t {
            TTy::Param(p, _) => env
                .iter()
                .find(|(g, _)| *g == p.id())
                .is_some_and(|(_, arg)| self.reaches(arg, owner, seen, &[])),
            TTy::Named(n, args) => {
                if (tauto_surface::bindings::is_library(&n, "Option")
                    || tauto_surface::bindings::is_library(&n, "Result")
                    || tauto_surface::bindings::is_library(&n, "Pair"))
                    && !self.program_declares(n)
                {
                    return args.iter().any(|a| self.reaches(a, owner, seen, env));
                }
                if n == owner {
                    return true;
                }
                // A value in a region is already behind a pointer into the
                // region: a `Placed(Tree)` field of a `Tree` needs no box.
                if tauto_surface::bindings::is_library(n, "Placed") && !self.program_declares(n) {
                    return false;
                }
                let Some(d) = self.types.datas.decls.get(n) else {
                    return false;
                };
                if d.builtin || !seen.insert((n.clone(), args.clone())) {
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
            TTy::Tagged(_, t) => self.reaches(t, owner, seen, env),
            _ => false,
        }
    }

    /// A constructor by name.
    pub fn ctor_ref(&self, name: &Name) -> Option<CtorRef> {
        self.ctor_ref_in(name, None)
    }

    pub fn ctor_ref_in(&self, name: &Name, ty: Option<&TTy>) -> Option<CtorRef> {
        let (d, i) = self.types.datas.resolve_ctor(name, ty).ok()?;
        let decl = &self.types.datas.decls[d];
        let c = &decl.constructors[*i];
        let library = |short: &str| {
            tauto_surface::bindings::is_library(d, short)
                && !self.program_declares(&tauto_surface::bindings::library_name(short))
        };
        let data = if library("Option") {
            DataRef::Option
        } else if library("Result") {
            DataRef::Result
        } else if library("Pair") {
            DataRef::Pair
        } else {
            DataRef::Gen(d.clone())
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
    pub fn ctor_field_rows(&self, ctor: &Name, ty: &TTy) -> Vec<Option<Row>> {
        match self.types.datas.resolve_ctor(ctor, Some(ty)) {
            Ok((d, i)) => self.field_rows(d, *i),
            Err(_) => Vec::new(),
        }
    }

    /// The field types of a constructor as the program writes them.
    fn field_terms(&self, data: &Name, ctor: usize) -> Vec<SurfaceTerm> {
        for s in &self.program.stmts {
            if let Stmt::Struct(d) | Stmt::Enum(d) = s
                && &d.name == data
                && let Some(c) = d.constructors.get(ctor)
            {
                return c.fields.iter().map(|(_, t)| t.clone()).collect();
            }
        }
        Vec::new()
    }

    fn field_rows(&self, data: &Name, ctor: usize) -> Vec<Option<Row>> {
        for s in &self.program.stmts {
            if let Stmt::Struct(d) | Stmt::Enum(d) = s
                && &d.name == data
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

    /// The rows of the function parameters of field `ix` of `ctor`, as the
    /// data writes them: `lift: (part: () -> Unit ! {rt} ∪ e) -> …` gives
    /// `part` the row `{rt} ∪ e`. The data's row variables are read as the
    /// tier the data carries them at, and left out where it carries none, so
    /// that a name of the enclosing function is not taken for them.
    pub fn ctor_field_param_rows(&self, ctor: &Name, ty: &TTy, ix: usize) -> Vec<Option<Row>> {
        match self.types.datas.resolve_ctor(ctor, Some(ty)) {
            Ok((d, i)) => {
                let (d, i) = (d.clone(), *i);
                self.field_param_rows(&d, i, ix)
            }
            Err(_) => Vec::new(),
        }
    }

    /// [`Lowerer::ctor_field_param_rows`] by the data and constructor.
    fn field_param_rows(&self, d: &Name, ctor: usize, ix: usize) -> Vec<Option<Row>> {
        let Some(field) = self.field_terms(d, ctor).into_iter().nth(ix) else {
            return Vec::new();
        };
        let mut t = &field;
        while let TermKind::FnKind { ty, .. } | TermKind::Borrow { term: ty, .. } = &*t.kind {
            t = ty;
        }
        let TermKind::Pi { params, .. } = &*t.kind else {
            return Vec::new();
        };
        let carried = self.carried.contains_key(d);
        params
            .iter()
            .map(|(_, p)| {
                pi_effects(p).map(|effects| {
                    let effects = effects
                        .into_iter()
                        .filter(|e| carried || e.row_variable().is_none())
                        .collect();
                    self.carried_field_row(d, effects)
                })
            })
            .collect()
    }

    /// The tier a function parameter of a field's function is taken at: the
    /// tier of its row where the data carries a suspending row
    /// (`Lowerer::carried`), else the plain one, as before the data carried it,
    /// but for a divergent one in a program that runs a budget.
    pub fn field_param_tier(&self, data_carried: bool, row: &Row) -> Option<Tier> {
        let tier = self.field_tier(row);
        if !data_carried {
            // A divergent function in a program that runs a budget is held
            // at the O tier wherever it is (`Lowerer::value_tier`), a
            // parameter of a field's function too: the body that calls it
            // may count the steps of a budget.
            return (tier == Tier::O
                && self.has_budget
                && row.contains(&tauto_surface::bindings::divergence()))
            .then_some(tier);
        }
        (tier > Tier::S).then_some(tier)
    }

    /// Whether `ctor`'s data carries a suspending row (`Lowerer::carried`).
    pub fn ctor_carried(&self, ctor: &Name, ty: &TTy) -> bool {
        self.types
            .datas
            .resolve_ctor(ctor, Some(ty))
            .is_ok_and(|(d, _)| self.carried.contains_key(d))
    }

    /// The tier of the function in the field `name` of a value of type `base`,
    /// when its type is written with a row.
    pub fn named_field_tier(&self, base: &TTy, name: &str) -> Option<Tier> {
        self.named_field_row(base, name)
            .map(|row| self.field_tier(&row))
    }

    /// The tier of the function in the field `name` of a value of type `base`
    /// whose field is a type parameter of its data (a record without a name),
    /// from the tier the lowered type `lowered` of the value gives that
    /// parameter's argument.
    pub fn argument_field_tier(&self, base: &TTy, lowered: &Ty, name: &str) -> Option<Tier> {
        let TTy::Named(data, _) = base.unborrowed() else {
            return None;
        };
        let d = self.types.datas.decls.get(data)?;
        let params = d.parameters();
        let field = d
            .constructors
            .iter()
            .find_map(|c| c.fields.iter().find(|(n, _)| n.as_deref() == Some(name)))?;
        let TTy::Param(p, _) = &field.1 else {
            return None;
        };
        let k = params.iter().position(|x| x == p)?;
        let mut lowered = lowered;
        while let Ty::Ref(i) | Ty::RefMut(i) = lowered {
            lowered = i;
        }
        match lowered {
            Ty::Data(_, args) if args.len() == params.len() => match &args[k] {
                Ty::Fn(f) => Some(f.tier),
                _ => None,
            },
            _ => None,
        }
    }

    /// The type the program writes for the field `name` of a value of type
    /// `base`, for reading the rows of the functions in its type arguments
    /// (`Option((Text) -> Located ! {e})`). A data type that carries a row
    /// reads its fields' row variables as that row, which the written term
    /// does not say, so it gives none.
    pub fn named_field_term(&self, base: &TTy, name: &str) -> Option<SurfaceTerm> {
        let TTy::Named(data, _) = base.unborrowed() else {
            return None;
        };
        if self.carried.contains_key(data) {
            return None;
        }
        self.program.stmts.iter().find_map(|s| match s {
            Stmt::Struct(d) | Stmt::Enum(d) if d.name == *data => {
                d.constructors.iter().find_map(|c| {
                    c.fields
                        .iter()
                        .find_map(|(n, t)| (n.as_deref() == Some(name)).then(|| t.clone()))
                })
            }
            _ => None,
        })
    }

    /// The field types the program writes for constructor `ctor` of `ty`,
    /// read as `named_field_term` reads one.
    pub fn ctor_field_terms(&self, ctor: &Name, ty: &TTy) -> Vec<SurfaceTerm> {
        match self.types.datas.resolve_ctor(ctor, Some(ty)) {
            Ok((d, i)) if !self.carried.contains_key(d) => {
                let (d, i) = (d.clone(), *i);
                self.field_terms(&d, i)
            }
            _ => Vec::new(),
        }
    }

    /// The row written on the function type of the field `name` of a value
    /// of type `base`.
    /// The tiers the data holds the function parameters of the function in
    /// field `name` at, as its definition makes them (`data_def`).
    pub fn named_field_param_tiers(&self, base: &TTy, name: &str) -> Vec<Option<Tier>> {
        let TTy::Named(data, _) = base.unborrowed() else {
            return Vec::new();
        };
        let found = self.program.stmts.iter().find_map(|s| match s {
            Stmt::Struct(d) | Stmt::Enum(d) if d.name == *data => {
                d.constructors.iter().enumerate().find_map(|(ci, c)| {
                    c.fields
                        .iter()
                        .position(|(n, _)| n.as_deref() == Some(name))
                        .map(|fi| (ci, fi))
                })
            }
            _ => None,
        });
        let Some((ci, fi)) = found else {
            return Vec::new();
        };
        let carried = self.carried.contains_key(data);
        self.field_param_rows(data, ci, fi)
            .into_iter()
            .map(|row| row.and_then(|row| self.field_param_tier(carried, &row)))
            .collect()
    }

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
    fn carried_field_row(&self, data: &Name, effects: Vec<Name>) -> Row {
        let Some(&tier) = self.carried.get(data) else {
            return effects.into_iter().collect();
        };
        effects
            .into_iter()
            .map(|e| {
                if e.row_variable().is_some() {
                    Name::from(super::carried_row(tier))
                } else {
                    e
                }
            })
            .collect()
    }

    /// The tier of a function held in a field: a data type has no handlers
    /// in place, so its row alone decides.
    pub fn field_tier(&self, row: &Row) -> Tier {
        self.value_tier(row, &HashMap::new())
    }

    /// `set_written_tiers` with `cx`'s rows, each function held as a
    /// function value is ([`Lowerer::value_tier_in`]).
    pub fn written_tiers(&self, t: &mut Ty, declared: &SurfaceTerm, cx: &Cx) {
        set_written_tiers(t, declared, &mut |row| self.value_tier_in(row, cx));
    }

    pub fn ctor_fields(&self, ctor: &Name, ty: &TTy) -> Vec<TTy> {
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
        set_written_tiers_in_pi(t, declared, tier_of);
        return;
    }
    set_written_tiers_in_args(t, declared, tier_of);
}

/// `set_written_tiers` for the parameters and the result of the function
/// type `declared`: `part` in `lift: (part: () -> Unit ! e) -> Unit` is
/// made at the tier the row `e` is specialized to, as `lift`'s caller and
/// its body both read it.
pub(crate) fn set_written_tiers_in_pi(
    t: &mut Ty,
    declared: &SurfaceTerm,
    tier_of: &mut dyn FnMut(&Row) -> Tier,
) {
    let declared = match &*declared.kind {
        TermKind::Borrow { term, .. }
        | TermKind::Tagged { term, .. }
        | TermKind::FnKind { ty: term, .. } => {
            return set_written_tiers_in_pi(t, term, tier_of);
        }
        _ => declared,
    };
    let TermKind::Pi { params, result, .. } = &*declared.kind else {
        return;
    };
    let f = match t {
        Ty::Fn(f) => f,
        Ty::Ref(i) | Ty::RefMut(i) => return set_written_tiers_in_pi(i, declared, tier_of),
        _ => return,
    };
    if f.params.len() != params.len() {
        return;
    }
    for (p, (_, d)) in f.params.iter_mut().zip(params) {
        set_written_tiers(p, d, tier_of);
    }
    set_written_tiers(&mut f.ret, result, tier_of);
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
        Ty::Result(a, b) | Ty::Pair(a, b) => vec![&mut **a, &mut **b],
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

fn mentions_any(t: &TTy, names: &HashSet<Name>) -> bool {
    match t {
        TTy::Named(n, args) => names.contains(n) || args.iter().any(|a| mentions_any(a, names)),
        TTy::Fn(ps, r, _) => ps.iter().any(|p| mentions_any(p, names)) || mentions_any(r, names),
        TTy::Union(ts) => ts.iter().any(|a| mentions_any(a, names)),
        TTy::Tagged(_, a) | TTy::Info(a) | TTy::Borrow(a, _) | TTy::Poly(_, a) => {
            mentions_any(a, names)
        }
        TTy::App(head, argument) => mentions_any(head, names) || mentions_any(argument, names),
        _ => false,
    }
}

#[cfg(test)]
mod reference_dependency_tests {
    use super::*;

    #[test]
    fn runtime_type_dependencies_compare_declarations_not_displays() {
        let first = Name::Global(tauto_surface::identity::DeclRef::fresh("SynPayload"));
        let second = Name::Global(tauto_surface::identity::DeclRef::fresh("SynPayload"));
        let ty = TTy::Union(vec![TTy::Named(first.clone(), vec![])]);
        assert!(mentions_any(&ty, &HashSet::from([first])));
        assert!(!mentions_any(&ty, &HashSet::from([second])));
    }
}

/// Whether a function in the type arguments of the written type `t` has a
/// row written on it, which gives it a tier its checked type does not say.
pub(crate) fn written_args_have_rows(t: &SurfaceTerm) -> bool {
    let t = match &*t.kind {
        TermKind::Borrow { term, .. } => term,
        _ => t,
    };
    let TermKind::App { arguments, .. } = &*t.kind else {
        return false;
    };
    arguments
        .iter()
        .any(|a| pi_effects(a).is_some_and(|e| !e.is_empty()) || written_args_have_rows(a))
}

/// The tier of the function `t` is, under a borrow too.
pub(crate) fn fn_tier_of(t: &Ty) -> Option<Tier> {
    match t {
        Ty::Fn(f) => Some(f.tier),
        Ty::Ref(i) | Ty::RefMut(i) => fn_tier_of(i),
        _ => None,
    }
}

fn mentions_param(t: &TTy) -> bool {
    match t {
        TTy::Param(..) | TTy::Var(_) => true,
        TTy::Named(_, args) => args.iter().any(mentions_param),
        TTy::Borrow(t, _) | TTy::Tagged(_, t) | TTy::Info(t) => mentions_param(t),
        TTy::Union(ts) => ts.iter().any(mentions_param),
        TTy::Fn(..) | TTy::Poly(..) | TTy::App(..) => true,
        _ => false,
    }
}
