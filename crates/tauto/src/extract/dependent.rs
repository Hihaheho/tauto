//! Value representation for checked programs whose data carries erased constraints.
//!
//! The representation is private to the checked compilation unit. Boundary
//! wrappers use nominal data types; no representation cast is exposed to Nib.
use super::*;
use std::collections::BTreeMap;
use tauto_parol::Span;

mod boundary;
mod calls;
mod patterns;
mod runtime;

const ERASED: &str = "TautoErasedUnit#r0";
const VALUE: &str = "TautoErasedValue#r0";
const NAT: &str = "TautoErasedNat#r0";
const BOOL: &str = "TautoErasedBool#r0";
const FUN: &str = "TautoErasedFunction#r0";

pub(super) struct Lowered {
    pub text: String,
    pub functions: HashSet<String>,
    pub families: HashSet<String>,
    pub exports: HashSet<String>,
    pub total: HashSet<String>,
    pub protected: HashSet<String>,
}

pub(super) fn lower(
    input: &crate::read::ExtractionInput,
    roots: &[PathBuf],
    std: &StdNames,
) -> Result<Option<Lowered>, String> {
    let checked = &input.checked;
    let mut functions = BTreeMap::new();
    fn gather(stmts: &[Stmt], path: &Path, fs: &mut BTreeMap<String, (PathBuf, FnDecl)>) {
        for s in stmts {
            match s {
                Stmt::Fn(f) => {
                    fs.insert(f.name.clone(), (path.to_owned(), f.clone()));
                }
                Stmt::Mutual { items, .. } => gather(items, path, fs),
                _ => {}
            }
        }
    }
    gather(
        &crate::check::kernel_prelude()?.stmts,
        Path::new("prelude"),
        &mut functions,
    );
    for (file, stmts) in &input.sources {
        gather(stmts, &file.path, &mut functions);
    }
    let root_paths: HashSet<_> = roots
        .iter()
        .map(|p| crate::program::canonical_path(p))
        .collect();
    let mut requested = HashSet::new();
    for (_, stmts) in &input.sources {
        for stmt in stmts {
            if executable(stmt, &checked.runtime) {
                let mut stmt = stmt.clone();
                crate::surface::walk::stmt(&mut stmt, &mut |t| {
                    if let TermKind::Var(n) = &*t.kind {
                        requested.insert(n.clone());
                    }
                    if let Some(n) = dotted(t) {
                        requested.insert(n);
                    }
                });
            }
        }
    }
    let mut constrained: HashSet<_> = checked
        .families
        .iter()
        .filter(|(_, f)| {
            !f.prop
                && !f.predicate
                && (f.indices > 0
                    || f.ctors
                        .first()
                        .and_then(|c| checked.signatures.get(c))
                        .is_some_and(|s| s.params[..f.params].iter().any(|r| *r != Role::Type))
                    || f.ctors.iter().any(|c| {
                        checked
                            .signatures
                            .get(c)
                            .is_some_and(|s| s.params[f.params..].contains(&Role::Type))
                    }))
        })
        .map(|(n, _)| n.clone())
        .collect();
    let mut family_refs = BTreeMap::new();
    fn family_dependencies(stmts: &[Stmt], out: &mut BTreeMap<String, HashSet<String>>) {
        for stmt in stmts {
            match stmt {
                Stmt::Inductive(i) => {
                    let mut refs = HashSet::new();
                    for c in &i.constructors {
                        for (_, ty) in &c.params {
                            let mut ty = ty.clone();
                            crate::surface::walk::term(&mut ty, &mut |t| {
                                if let TermKind::Var(n) = &*t.kind {
                                    refs.insert(n.clone());
                                }
                            });
                        }
                    }
                    out.insert(i.name.clone(), refs);
                }
                Stmt::Mutual { items, .. } => family_dependencies(items, out),
                _ => {}
            }
        }
    }
    for (_, stmts) in &input.sources {
        family_dependencies(stmts, &mut family_refs);
    }
    fn data(stmts: &[Stmt], out: &mut BTreeMap<String, InductiveDecl>) {
        for stmt in stmts {
            match stmt {
                Stmt::Inductive(i) => {
                    out.insert(i.name.clone(), i.clone());
                }
                Stmt::Mutual { items, .. } => data(items, out),
                _ => {}
            }
        }
    }
    let mut declarations = BTreeMap::new();
    data(&crate::check::kernel_prelude()?.stmts, &mut declarations);
    for (_, stmts) in &input.sources {
        data(stmts, &mut declarations);
    }
    loop {
        let before = constrained.len();
        for (name, refs) in &family_refs {
            if refs.iter().any(|n| constrained.contains(n)) {
                constrained.insert(name.clone());
            }
        }
        if before == constrained.len() {
            break;
        }
    }
    let mut dependencies = BTreeMap::new();
    let mut affected = constrained.clone();
    let mut contracts: BTreeMap<String, HashSet<usize>> = BTreeMap::new();
    fn callable_contracts(info: &crate::check::BoundaryType, out: &mut HashSet<usize>) {
        if matches!(&*info.ty.kind, TermKind::Pi { .. }) {
            out.insert(info.id);
        }
        for argument in &info.arguments {
            callable_contracts(argument, out);
        }
    }
    for (name, types) in &checked.boundary_types {
        let mut ids = HashSet::new();
        for info in types.iter().flatten() {
            callable_contracts(info, &mut ids);
        }
        contracts.insert(name.clone(), ids);
    }
    for (name, (_, f)) in &functions {
        let mut refs = HashSet::new();
        if let Some(sig) = checked.signatures.get(name) {
            let arity = checked
                .arities
                .get(name)
                .copied()
                .unwrap_or(sig.params.len());
            let offset = arity.saturating_sub(f.params.len());
            let roles = sig.params.get(offset..arity).unwrap_or_default();
            let parameters = f.param_types.iter().zip(roles).filter_map(|(ty, role)| {
                if *role == Role::Value {
                    ty.as_ref()
                } else {
                    None
                }
            });
            for ty in parameters.chain(f.result.iter().filter(|_| sig.result == Role::Value)) {
                let mut callable = false;
                let mut erased_domain = false;
                let mut ty = ty.clone();
                crate::surface::walk::term(&mut ty, &mut |term| {
                    callable |= matches!(&*term.kind, TermKind::Pi { .. });
                    erased_domain |= matches!(&*term.kind, TermKind::Var(n)
                        if n == "Type" || n == "Prop" || n == "=" || checked.props.contains(n));
                });
                if callable && erased_domain {
                    affected.insert(name.clone());
                }
            }
        }
        if !std.of(name).is_some_and(|n| mapped_fn(n).is_some()) {
            let mut stmt = Stmt::Fn(f.clone());
            crate::surface::walk::stmt(&mut stmt, &mut |t| {
                if let TermKind::Var(n) = &*t.kind {
                    refs.insert(n.clone());
                }
                if let TermKind::App {
                    function,
                    arguments,
                } = &*t.kind
                    && matches!(&*function.kind, TermKind::Var(n) if n == name)
                    && let Some(sig) = checked.signatures.get(name)
                    && arguments.len() == sig.params.len()
                    && arguments
                        .iter()
                        .zip(&sig.params)
                        .any(|(a, r)| *r == Role::Type && !matches!(&*a.kind, TermKind::Var(_)))
                {
                    affected.insert(name.clone());
                }
            });
        }
        dependencies.insert(name.clone(), refs);
    }
    loop {
        let before = affected.len();
        for (name, refs) in &dependencies {
            if refs.iter().any(|n| affected.contains(n)) {
                affected.insert(name.clone());
            }
        }
        let opaque_contracts: HashSet<_> = contracts
            .iter()
            .filter(|(name, _)| affected.contains(*name))
            .flat_map(|(_, ids)| ids.iter().copied())
            .collect();
        for (name, ids) in &contracts {
            if ids.iter().any(|id| opaque_contracts.contains(id)) {
                affected.insert(name.clone());
            }
        }
        if before == affected.len() {
            break;
        }
    }
    let seeds: Vec<_> = functions
        .iter()
        .filter(|(n, (p, _))| {
            affected.contains(*n)
                && (root_paths.contains(&crate::program::canonical_path(p))
                    || requested.contains(*n))
                && !checked.runtime.contains(*n)
                && checked
                    .signatures
                    .get(*n)
                    .is_some_and(|s| s.result == Role::Value)
        })
        .map(|(n, _)| n.clone())
        .collect();
    if seeds.is_empty() && constrained.is_empty() {
        return Ok(None);
    }
    let mut e = Eraser {
        applications: calls::Applications::new(checked),
        checked,
        std,
        functions,
        emitted: HashSet::new(),
        definitions: Vec::new(),
        ctors: BTreeMap::new(),
        families: HashSet::new(),
        next: 0,
        names: BTreeMap::new(),
        opaque: BTreeMap::new(),
        exports: HashSet::new(),
        total: HashSet::new(),
        forbidden: HashSet::new(),
        declarations,
        constrained: constrained.clone(),
        bridges: BTreeMap::new(),
        active_bridges: HashSet::new(),
    };
    for name in &seeds {
        e.function(name)?;
    }
    let mut wrappers = Vec::new();
    for name in &seeds {
        if let Some(w) = e.wrapper(name)? {
            wrappers.push(w);
        }
    }
    let mut text = format!(
        "shared enum {VALUE} {{\n  {NAT}(nat)\n  {BOOL}(Bool)\n  TautoErasedI64#r0(i64)\n  TautoErasedText#r0(Text)\n  {ERASED}\n  {FUN}(nat, (List({VALUE})) -> {VALUE} ! {{Div}})\n"
    );
    for (name, (variant, fields)) in &e.ctors {
        let _ = name;
        if *fields == 0 {
            let _ = writeln!(text, "  {variant}");
        } else {
            let _ = writeln!(text, "  {variant}({})", vec![VALUE; *fields].join(", "));
        }
    }
    text.push_str("}\n");
    text.push_str(&format!("\nfn TautoErasedGetNat#r0(v: {VALUE}): nat {{ match v {{ {NAT}(n) => n\n _ => extract_unreachable() }} }}\nfn TautoErasedGetBool#r0(v: {VALUE}): Bool {{ match v {{ {BOOL}(b) => b\n _ => extract_unreachable() }} }}"));
    text.push_str(&format!("\nfn TautoErasedGetI64#r0(v: {VALUE}): i64 {{ match v {{ TautoErasedI64#r0(n) => n\n _ => extract_unreachable() }} }}\nfn TautoErasedGetText#r0(v: {VALUE}): Text {{ match v {{ TautoErasedText#r0(t) => t\n _ => extract_unreachable() }} }}\n"));
    text.push_str(&runtime::definitions());
    e.total
        .extend(runtime::FUNCTIONS.iter().map(|name| (*name).to_string()));
    e.forbidden
        .extend(runtime::FUNCTIONS.iter().map(|name| (*name).to_string()));
    e.forbidden.insert(ERASED.into());
    e.total.extend([
        "TautoErasedGetI64#r0".into(),
        "TautoErasedGetText#r0".into(),
    ]);
    e.total.extend([
        "TautoErasedGetNat#r0".into(),
        "TautoErasedGetBool#r0".into(),
        "TautoErasedApply#r0".into(),
    ]);
    for (_, name) in &e.opaque {
        let _ = writeln!(text, "pub struct {name} {{ value: {VALUE} }}");
    }
    for d in &e.definitions {
        text.push_str(d);
        text.push('\n');
    }
    for w in wrappers {
        text.push_str(&w);
        text.push('\n');
    }
    e.forbidden.extend([
        VALUE.into(),
        NAT.into(),
        BOOL.into(),
        FUN.into(),
        "TautoErasedGetNat#r0".into(),
        "TautoErasedGetBool#r0".into(),
        "TautoErasedApply#r0".into(),
    ]);
    e.forbidden.extend(e.names.values().cloned());
    e.forbidden.extend(e.ctors.values().map(|(n, _)| n.clone()));
    e.forbidden.extend(e.opaque.values().cloned());
    e.forbidden.extend([
        "TautoErasedI64#r0".into(),
        "TautoErasedText#r0".into(),
        "TautoErasedGetI64#r0".into(),
        "TautoErasedGetText#r0".into(),
    ]);
    Ok(Some(Lowered {
        text,
        functions: e
            .emitted
            .into_iter()
            .filter(|n| affected.contains(n))
            .collect(),
        families: constrained,
        exports: e.exports,
        total: e.total,
        protected: e.forbidden,
    }))
}

#[derive(Clone, Copy)]
enum Binding {
    Value,
    Erased,
}

#[derive(Clone, Default)]
struct Scope {
    bindings: HashMap<String, Binding>,
}

impl Scope {
    fn contains(&self, name: &str) -> bool {
        self.bindings.contains_key(name)
    }
    fn is_erased(&self, name: &str) -> bool {
        matches!(self.bindings.get(name), Some(Binding::Erased))
    }
    fn insert(&mut self, name: String) {
        self.bindings.insert(name, Binding::Value);
    }
    fn extend(&mut self, names: impl IntoIterator<Item = String>) {
        for name in names {
            self.insert(name);
        }
    }
    fn erase_pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Bind(name) => self.erase(name.clone()),
            Pattern::Ctor { args, .. } => {
                for arg in args {
                    self.erase_pattern(arg);
                }
            }
            _ => {}
        }
    }
    fn erase(&mut self, name: String) {
        self.bindings.insert(name, Binding::Erased);
    }
}

struct Eraser<'a> {
    applications: calls::Applications,
    checked: &'a Checked,
    std: &'a StdNames,
    functions: BTreeMap<String, (PathBuf, FnDecl)>,
    emitted: HashSet<String>,
    definitions: Vec<String>,
    ctors: BTreeMap<String, (String, usize)>,
    families: HashSet<String>,
    next: usize,
    names: BTreeMap<String, String>,
    opaque: BTreeMap<usize, String>,
    exports: HashSet<String>,
    total: HashSet<String>,
    forbidden: HashSet<String>,
    declarations: BTreeMap<String, InductiveDecl>,
    constrained: HashSet<String>,
    bridges: BTreeMap<String, (String, String)>,
    active_bridges: HashSet<String>,
}

impl Eraser<'_> {
    fn fresh(&mut self, suffix: &str) -> String {
        self.next += 1;
        format!("TautoErased{suffix}{}#r0", self.next)
    }
    fn name(&mut self, name: &str) -> String {
        if let Some(n) = self.names.get(name) {
            return n.clone();
        }
        let n = self.fresh("Fn");
        self.names.insert(name.into(), n.clone());
        n
    }
    fn ctor(&mut self, name: &str) -> Result<String, String> {
        if let Some((n, _)) = self.ctors.get(name) {
            return Ok(n.clone());
        }
        let (family, fam) = self
            .checked
            .families
            .iter()
            .find(|(_, f)| f.ctors.iter().any(|c| c == name))
            .ok_or_else(|| format!("dependent extraction: unknown constructor {name}"))?;
        self.families.insert(family.clone());
        let fields = self.checked.signatures[name].params[fam.params..]
            .iter()
            .filter(|r| **r == Role::Value)
            .count();
        let variant = self.fresh("Ctor");
        self.ctors.insert(name.into(), (variant.clone(), fields));
        Ok(variant)
    }
    fn function(&mut self, name: &str) -> Result<String, String> {
        let generated = self.name(name);
        if !self.emitted.insert(name.into()) {
            return Ok(generated);
        }
        let (_, f) = self
            .functions
            .get(name)
            .cloned()
            .ok_or_else(|| format!("dependent extraction: no checked body for {name}"))?;
        let Stmt::Fn(mut f) = record_sugar(&self.checked.records, &Stmt::Fn(f)) else {
            unreachable!("record sugar preserves function declarations")
        };
        crate::surface::walk::strip_recursion_proofs(&mut f);
        if f.effects.as_ref().is_some_and(|r| !r.is_empty()) {
            return Err(format!(
                "dependent extraction: effectful body {name} needs a boundary adapter"
            ));
        }
        let sig = &self.checked.signatures[name];
        let offset = self
            .arity(name)
            .checked_sub(f.params.len())
            .ok_or("dependent extraction: parameter roles")?;
        let mut locals = Scope::default();
        for name in &f.generics {
            locals.erase(name.clone());
        }
        let mut params = Vec::new();
        for (n, role) in f.params.iter().zip(&sig.params[offset..]) {
            if *role == Role::Value {
                params.push(format!("{}: {VALUE}", raw(n)));
                locals.insert(n.clone());
            } else {
                locals.erase(n.clone());
            }
        }
        let mut mapped_body = None;
        if let Some(template) = self.std.of(name).and_then(mapped_fn)
            && let Some(types) = self.checked.boundary_types.get(name).cloned()
            && types.len() == sig.params.len() + 1
        {
            let mut native = Vec::new();
            let mut supported = true;
            for (k, n) in f.params.iter().enumerate() {
                if sig.params[offset + k] != Role::Value {
                    continue;
                }
                match types[offset + k].as_ref() {
                    Some(info) => match self.boundary(info)? {
                        Some((_, _, unpack)) => native.push(unpack.replace("$v", &raw(n))),
                        None => {
                            supported = false;
                            break;
                        }
                    },
                    None => {
                        supported = false;
                        break;
                    }
                }
            }
            if supported
                && let Some(Some(info)) = types.last()
                && let Some((_, pack, _)) = self.boundary(info)?
            {
                mapped_body = Some(pack.replace("$v", &format!("({})", fill(template, &native))));
            }
        }
        let body = match mapped_body {
            Some(body) => body,
            None => self.expr(&f.body, &locals)?,
        };
        self.definitions.push(format!(
            "fn {generated}({}): {VALUE} {{ {body} }}\n",
            params.join(", ")
        ));
        self.total.insert(generated.clone());
        Ok(generated)
    }
    fn expr(&mut self, t: &SurfaceTerm, locals: &Scope) -> Result<String, String> {
        match &*t.kind {
            TermKind::Nat(n) => Ok(format!("{NAT}({n})")),
            TermKind::Bool(b) => Ok(format!("{BOOL}({b})")),
            TermKind::Text(t) => Ok(format!("TautoErasedText#r0({})", text_literal(t))),
            TermKind::Var(n) if locals.is_erased(n) => Ok(ERASED.into()),
            TermKind::Var(n) if locals.contains(n) => Ok(raw(n)),
            TermKind::Var(n) => self.global(n, &[], locals, t.span, false),
            TermKind::App {
                function,
                arguments,
            } => {
                if let TermKind::Var(n) = &*function.kind
                    && !locals.contains(n)
                {
                    return self.global(n, arguments, locals, t.span, true);
                }
                let f = self.expr(function, locals)?;
                let callee = match &*function.kind {
                    TermKind::Var(name) => Some(name.as_str()),
                    _ => None,
                };
                let omitted = self.omitted(t.span, arguments.len(), callee)?.unwrap_or(0);
                let mut args = vec![ERASED.to_string(); omitted];
                for arg in arguments {
                    args.push(self.expr(arg, locals)?);
                }
                Ok(format!("TautoErasedApply#r0({f}, [{}])", args.join(", ")))
            }
            TermKind::Pi { .. } => Ok(ERASED.into()),
            TermKind::Ascribe { term, .. } | TermKind::Tagged { term, .. } => {
                self.expr(term, locals)
            }
            TermKind::Lam { params, body, .. } => {
                let keep = params.clone();
                let mut inner = locals.clone();
                inner.extend(keep.iter().cloned());
                let b = self.expr(body, &inner)?;
                Ok(self.closure(&keep, &b))
            }
            TermKind::Block(stmts) => {
                let mut inner = locals.clone();
                let mut out = Vec::new();
                for s in stmts {
                    match s {
                        Stmt::Let {
                            name, ty, value, ..
                        } => {
                            if ty.as_ref().is_some_and(|t| self.prop(t)) {
                                inner.erase(name.clone());
                                continue;
                            }
                            let v = self.expr(value, &inner)?;
                            out.push(format!("let {}: {VALUE} := {v}", raw(name)));
                            inner.insert(name.clone());
                        }
                        Stmt::Expr(e) => out.push(self.expr(e, &inner)?),
                        _ => return Err("dependent extraction: unsupported block statement".into()),
                    }
                }
                Ok(format!("{{\n{}\n}}", out.join("\n")))
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => self.matching(scrutinee, arms, locals),
            TermKind::If {
                condition,
                then,
                otherwise: Some(otherwise),
            } => {
                let c = self.expr(condition, locals)?;
                let a = self.expr(then, locals)?;
                let b = self.expr(otherwise, locals)?;
                Ok(format!(
                    "if TautoErasedGetBool#r0({c}) {{ {a} }} else {{ {b} }}"
                ))
            }
            TermKind::Field { base, name } => {
                if let Some(global) = dotted(t)
                    && self.checked.signatures.contains_key(&global)
                {
                    return self.global(&global, &[], locals, t.span, false);
                }
                let mut owners: Vec<_> = self
                    .checked
                    .records
                    .iter()
                    .filter(|(_, (_, ns))| ns.contains(name))
                    .map(|(f, (c, ns))| (f.clone(), c.clone(), ns.clone()))
                    .collect();
                owners.sort();
                let mut arms = Vec::new();
                let value = self.expr(base, locals)?;
                for (family, ctor, names) in owners {
                    if self.checked.families[&family].prop {
                        continue;
                    }
                    if self.std.of(&family) == Some("I64") && name == "val" {
                        let (_, pack, _) = self.integer_bridge()?;
                        arms.push(format!(
                            "TautoErasedI64#r0(selected) => {}",
                            pack.replace("$v", "extract_i64_int(selected)")
                        ));
                        continue;
                    }
                    if self.std.of(&family) == Some("I64") {
                        arms.push(format!("TautoErasedI64#r0(_) => {ERASED}"));
                        continue;
                    }
                    let sig = &self.checked.signatures[&ctor];
                    let skip = self.checked.families[&family].params;
                    let fields: Vec<_> = names
                        .iter()
                        .zip(&sig.params[skip..])
                        .filter(|(_, r)| **r == Role::Value)
                        .map(|(n, _)| if n == name { "selected" } else { "_" })
                        .collect();
                    let result = if fields.contains(&"selected") {
                        "selected"
                    } else {
                        ERASED
                    };
                    let c = self.ctor(&ctor)?;
                    let pattern = if fields.is_empty() {
                        c
                    } else {
                        format!("{c}({})", fields.join(", "))
                    };
                    arms.push(format!("{pattern} => {result}"));
                }
                arms.push(format!("{ERASED} => {ERASED}"));
                arms.push("_ => extract_unreachable()".into());
                Ok(format!("match ({value}) {{\n{}\n}}", arms.join("\n")))
            }
            _ => Err(format!(
                "dependent extraction: unsupported term {}",
                show(t)
            )),
        }
    }
}
