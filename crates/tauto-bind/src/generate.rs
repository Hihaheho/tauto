use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use rustdoc_types::{
    Crate, Function, GenericArg, GenericArgs, GenericBound, GenericParamDefKind, Id, ItemEnum,
    Type, Visibility,
};

use crate::config::Config;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Output {
    pub tauto: String,
    pub eure: String,
    pub report: String,
}

/// Words a parameter cannot be named.
const RESERVED: &[&str] = &[
    "let",
    "var",
    "fn",
    "struct",
    "enum",
    "effect",
    "match",
    "if",
    "else",
    "handle",
    "with",
    "perform",
    "return",
    "while",
    "import",
    "extern",
    "module",
    "true",
    "false",
    "theorem",
    "axiom",
    "def",
    "mutual",
    "inductive",
    "break",
    "continue",
    "eqn",
    "opaque",
    "budget",
    "resume",
    "direct",
    "mut",
    "type",
    "in",
    "use",
    "ref",
    "self",
    "Self",
];

/// A bound type: its name in tauto and its path in Rust.
struct Bound {
    id: Id,
    name: String,
    rust: String,
    /// How many lifetimes the type has (`Match<'h>` one, `Matches<'r, 'h>`
    /// two); a type that has any is written `view struct`.
    lifetimes: usize,
}

#[derive(Default)]
struct Module {
    externs: Vec<String>,
    children: BTreeMap<String, Module>,
}

struct Gen<'a> {
    krate: &'a Crate,
    cfg: &'a Config,
    /// Every public path of the crate → the item it names.
    public: BTreeMap<String, Id>,
    bound: Vec<Bound>,
    names: HashMap<Id, String>,
    report: Vec<String>,
    /// Extern name (qualified) → Rust path.
    externs: BTreeMap<String, String>,
    /// Extern name (qualified) → its `usize` / `isize` marks.
    marks: BTreeMap<String, String>,
}

/// A generic parameter filled by the config's `instances`: its type in
/// tauto, and the Rust type it stands for.
type Subst = HashMap<String, (String, String)>;

pub fn generate(krate: &Crate, cfg: &Config, config_file: &str) -> Output {
    let mut g = Gen {
        krate,
        cfg,
        public: BTreeMap::new(),
        bound: Vec::new(),
        names: HashMap::new(),
        report: Vec::new(),
        externs: BTreeMap::new(),
        marks: BTreeMap::new(),
    };
    g.index_public();
    g.run(config_file)
}

impl<'a> Gen<'a> {
    // ---- the public paths of the crate -------------------------------------

    fn index_public(&mut self) {
        let root = self.krate.root;
        let name = self
            .krate
            .index
            .get(&root)
            .and_then(|i| i.name.clone())
            .unwrap_or_default();
        let mut seen = HashSet::new();
        self.walk_module(root, &name, &mut seen);
    }

    fn walk_module(&mut self, id: Id, path: &str, seen: &mut HashSet<Id>) {
        if !seen.insert(id) {
            return;
        }
        let Some(item) = self.krate.index.get(&id) else {
            return;
        };
        let ItemEnum::Module(m) = &item.inner else {
            return;
        };
        for child in m.items.clone() {
            let Some(c) = self.krate.index.get(&child) else {
                continue;
            };
            if !matches!(c.visibility, Visibility::Public) && !matches!(c.inner, ItemEnum::Use(_)) {
                continue;
            }
            match &c.inner {
                ItemEnum::Use(u) => {
                    if !matches!(c.visibility, Visibility::Public) {
                        continue;
                    }
                    let Some(target) = u.id else { continue };
                    if u.is_glob {
                        self.walk_module(target, path, seen);
                    } else {
                        let p = format!("{path}::{}", u.name);
                        self.public.entry(p.clone()).or_insert(target);
                        if matches!(
                            self.krate.index.get(&target).map(|t| &t.inner),
                            Some(ItemEnum::Module(_))
                        ) {
                            self.walk_module(target, &p, seen);
                        }
                    }
                }
                ItemEnum::Module(_) => {
                    let n = c.name.clone().unwrap_or_default();
                    let p = format!("{path}::{n}");
                    self.public.entry(p.clone()).or_insert(child);
                    self.walk_module(child, &p, seen);
                }
                _ => {
                    if let Some(n) = &c.name {
                        self.public.entry(format!("{path}::{n}")).or_insert(child);
                    }
                }
            }
        }
    }

    // ---- the run -------------------------------------------------------------

    fn run(mut self, config_file: &str) -> Output {
        let mut root = Module::default();
        let items = self.cfg.items.clone();
        // Types first, so a function can name them.
        for path in &items {
            self.bind_type(path);
        }
        for path in &items {
            let Some(id) = self.public.get(path).copied() else {
                self.report.push(format!(
                    "{path}: not a public item of {}",
                    self.cfg.crate_name
                ));
                continue;
            };
            if let Some(ItemEnum::Function(f)) = self.krate.index.get(&id).map(|i| i.inner.clone())
            {
                self.free_function(path, &f, &mut root);
            }
        }
        let bound: Vec<(Id, String, String, usize)> = self
            .bound
            .iter()
            .map(|b| (b.id, b.name.clone(), b.rust.clone(), b.lifetimes))
            .collect();
        let mut type_modules: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (id, name, rust, _) in &bound {
            let lines = self.methods(*id, name, rust);
            if !lines.is_empty() {
                type_modules.insert(name.clone(), lines);
            }
        }
        self.render(config_file, &bound, &type_modules, &root)
    }

    fn rename(&self, path: &str, default: &str) -> String {
        self.cfg
            .rename
            .get(path)
            .cloned()
            .unwrap_or_else(|| default.to_string())
    }

    fn bind_type(&mut self, path: &str) {
        let Some(id) = self.public.get(path).copied() else {
            return;
        };
        let Some(item) = self.krate.index.get(&id) else {
            return;
        };
        let generics = match &item.inner {
            ItemEnum::Struct(s) => &s.generics,
            ItemEnum::Enum(e) => &e.generics,
            ItemEnum::Function(_) => return,
            _ => {
                self.report.push(format!(
                    "{path}: only structs, enums and functions are bound"
                ));
                return;
            }
        };
        let mut lifetimes = 0;
        for p in &generics.params {
            match &p.kind {
                GenericParamDefKind::Lifetime { .. } => lifetimes += 1,
                _ => {
                    self.report.push(format!(
                        "{path}: a type with type or const parameters needs its instances in the config (not supported yet)"
                    ));
                    return;
                }
            }
        }
        let last = path.rsplit("::").next().unwrap_or(path);
        let name = self.rename(path, last);
        self.names.insert(id, name.clone());
        self.bound.push(Bound {
            id,
            name,
            rust: path.to_string(),
            lifetimes,
        });
    }

    // ---- functions -----------------------------------------------------------

    fn free_function(&mut self, path: &str, f: &Function, root: &mut Module) {
        let segments: Vec<&str> = path.split("::").collect();
        let name = segments.last().copied().unwrap_or(path);
        match self.signature(name, f, None, path) {
            Ok((line, rust, marks)) => {
                let mut m = &mut *root;
                for s in &segments[..segments.len() - 1] {
                    m = m.children.entry((*s).to_string()).or_default();
                }
                m.externs.push(line);
                let qualified = segments.join("::");
                if !marks.is_empty() {
                    self.marks.insert(qualified.clone(), marks);
                }
                self.externs.insert(qualified, rust);
            }
            Err(why) => self.report.push(format!("{path}: {why}")),
        }
    }

    /// The impl blocks and trait implementations of a bound type.
    fn methods(&mut self, id: Id, name: &str, rust: &str) -> Vec<String> {
        let impls = match self.krate.index.get(&id).map(|i| &i.inner) {
            Some(ItemEnum::Struct(s)) => s.impls.clone(),
            Some(ItemEnum::Enum(e)) => e.impls.clone(),
            _ => Vec::new(),
        };
        let mut lines = Vec::new();
        let mut seen = BTreeSet::new();
        for imp_id in impls {
            let Some(item) = self.krate.index.get(&imp_id) else {
                continue;
            };
            let ItemEnum::Impl(imp) = &item.inner else {
                continue;
            };
            if imp.is_synthetic || imp.blanket_impl.is_some() || imp.is_negative {
                continue;
            }
            match &imp.trait_ {
                None => {
                    for mid in &imp.items {
                        let Some(m) = self.krate.index.get(mid) else {
                            continue;
                        };
                        let ItemEnum::Function(f) = &m.inner else {
                            continue;
                        };
                        if !matches!(m.visibility, Visibility::Public) {
                            continue;
                        }
                        let mname = m.name.clone().unwrap_or_default();
                        if !seen.insert(mname.clone()) {
                            continue;
                        }
                        let qualified = format!("{name}::{mname}");
                        match self.signature(
                            &mname,
                            f,
                            Some((id, name)),
                            &format!("{rust}::{mname}"),
                        ) {
                            Ok((line, call, marks)) => {
                                lines.push(line);
                                if !marks.is_empty() {
                                    self.marks.insert(qualified.clone(), marks);
                                }
                                self.externs.insert(qualified, call);
                            }
                            Err(why) => self.report.push(format!("{rust}::{mname}: {why}")),
                        }
                    }
                }
                Some(tr) => {
                    let tname = tr.path.rsplit("::").next().unwrap_or(&tr.path).to_string();
                    if !self.cfg.traits.contains(&tname) {
                        continue;
                    }
                    let (fname, line, rust_fn) = match tname.as_str() {
                        "Display" => (
                            "to_text",
                            format!("fn to_text(&s: {name}): Text"),
                            format!("<{rust} as ToString>::to_string"),
                        ),
                        "Clone" => (
                            "clone",
                            format!("fn clone(&s: {name}): {name}"),
                            format!("<{rust} as Clone>::clone"),
                        ),
                        "PartialEq" => (
                            "eq",
                            format!("fn eq(&a: {name}, &b: {name}): Bool"),
                            format!("<{rust} as PartialEq>::eq"),
                        ),
                        "Default" => (
                            "default",
                            format!("fn default(): {name}"),
                            format!("<{rust} as Default>::default"),
                        ),
                        "Iterator" => {
                            let item_ty = imp.items.iter().find_map(|i| {
                                let it = self.krate.index.get(i)?;
                                match (&it.inner, it.name.as_deref()) {
                                    (ItemEnum::AssocType { type_: Some(t), .. }, Some("Item")) => {
                                        Some(t.clone())
                                    }
                                    _ => None,
                                }
                            });
                            // `Item = &str` is a `Text` (a copy), marked `u`.
                            let text_item = matches!(&item_ty, Some(Type::BorrowedRef {
                                is_mutable: false, type_, ..
                            }) if matches!(&**type_, Type::Primitive(p) if p == "str"));
                            let item = match &item_ty {
                                Some(_) if text_item => Some(Ok("Text".to_string())),
                                Some(t) => Some(self.ty(t, Some((id, name)), &Subst::new())),
                                None => None,
                            };
                            match item {
                                Some(Ok(t)) => {
                                    if text_item {
                                        self.marks.insert(format!("{name}.next"), "u".into());
                                    }
                                    (
                                        "next",
                                        format!("fn next(&mut it: {name}): Option({t})"),
                                        format!("<{rust} as Iterator>::next"),
                                    )
                                }
                                Some(Err(why)) => {
                                    self.report.push(format!("{rust}: Iterator::Item: {why}"));
                                    continue;
                                }
                                None => continue,
                            }
                        }
                        _ => {
                            self.report.push(format!(
                                "{rust}: the trait {tname} is not one that can be bound"
                            ));
                            continue;
                        }
                    };
                    if seen.insert(fname.to_string()) {
                        lines.push(line);
                        self.externs.insert(format!("{name}::{fname}"), rust_fn);
                    }
                }
            }
        }
        lines
    }

    /// One `fn` line of an `extern` block, and the Rust path it calls.
    fn signature(
        &self,
        name: &str,
        f: &Function,
        owner: Option<(Id, &str)>,
        rust_path: &str,
    ) -> Result<(String, String, String), String> {
        if f.header.is_unsafe {
            return Err("unsafe fn".into());
        }
        if f.header.is_async {
            return Err("async fn".into());
        }
        let type_params: Vec<&str> = f
            .generics
            .params
            .iter()
            .filter(|p| matches!(p.kind, GenericParamDefKind::Type { .. }))
            .map(|p| p.name.as_str())
            .collect();
        if f.generics
            .params
            .iter()
            .any(|p| matches!(p.kind, GenericParamDefKind::Const { .. }))
        {
            return Err("a const generic".into());
        }
        let mut subst = Subst::new();
        let mut call = rust_path.to_string();
        if !type_params.is_empty() {
            let Some(args) = self.cfg.instances.get(rust_path) else {
                return Err("a generic function needs an instance in the config".into());
            };
            if args.len() != type_params.len() {
                return Err(format!(
                    "the config gives {} type arguments, the function has {}",
                    args.len(),
                    type_params.len()
                ));
            }
            for (g, a) in type_params.iter().zip(args) {
                subst.insert((*g).to_string(), (self.instance_type(a)?, a.clone()));
            }
            call = format!("{rust_path}::<{}>", args.join(", "));
        }
        let name = &name.to_string();
        let mut params = Vec::new();
        let mut marks: Vec<String> = Vec::new();
        for (i, (pname, t)) in f.sig.inputs.iter().enumerate() {
            if pname == "self" {
                let o = owner.ok_or("self outside an impl")?.1;
                params.push(match t {
                    Type::BorrowedRef {
                        is_mutable: true, ..
                    } => format!("&mut s: {o}"),
                    Type::BorrowedRef { .. } => format!("&s: {o}"),
                    _ => format!("s: {o}"),
                });
                continue;
            }
            let n = if is_ident(pname) && !RESERVED.contains(&pname.as_str()) {
                pname.clone()
            } else {
                format!("a{i}")
            };
            match int_mark(t) {
                Some((mark, ty)) if mark == "p" || mark == "q" => {
                    marks.push(format!("{mark}{i}"));
                    params.push(format!("{n}: {ty}"));
                }
                _ => params.push(self.param(&n, t, owner, &subst)?),
            }
        }
        let ret = match &f.sig.output {
            None => ": Unit".to_string(),
            Some(Type::Tuple(v)) if v.is_empty() => ": Unit".to_string(),
            Some(Type::BorrowedRef {
                is_mutable: false,
                type_,
                ..
            }) if matches!(&**type_, Type::Primitive(p) if p == "str") => ": Text".to_string(),
            // `Cow<str>` is a `Buf` (the owned copy), marked `c`.
            Some(t) if is_cow_str(t) => {
                marks.push("c".to_string());
                ": Buf".to_string()
            }
            Some(t) => match int_mark(t) {
                Some((mark, ty)) => {
                    marks.push(match mark {
                        "p" => "r".to_string(),
                        "q" => "s".to_string(),
                        m => m.to_string(),
                    });
                    format!(": {ty}")
                }
                None => format!(": {}", self.ty(t, owner, &subst)?),
            },
        };
        Ok((
            format!("fn {name}({}){ret}", params.join(", ")),
            call,
            marks.join(" "),
        ))
    }

    /// A type argument of an instance, written in Rust, as tauto writes it.
    fn instance_type(&self, rust: &str) -> Result<String, String> {
        if rust == "&str" {
            return Ok("&str".into());
        }
        if rust == "String" {
            return Ok("Buf".into());
        }
        if let Some(b) = self.bound.iter().find(|b| b.rust == rust) {
            return Ok(b.name.clone());
        }
        match rust {
            "bool" => Ok("Bool".into()),
            "f64" => Ok("Float".into()),
            "i32" | "i64" | "u8" | "u32" | "u64" => Ok(rust.into()),
            other => Err(format!("the instance type {other} is not bound")),
        }
    }

    fn param(
        &self,
        n: &str,
        t: &Type,
        owner: Option<(Id, &str)>,
        subst: &Subst,
    ) -> Result<String, String> {
        if let Type::Generic(g) = t
            && let Some((tauto, _)) = subst.get(g)
        {
            return Ok(if tauto == "&str" {
                format!("&{n}: Text")
            } else {
                format!("{n}: {tauto}")
            });
        }
        match t {
            Type::BorrowedRef {
                is_mutable, type_, ..
            } => match &**type_ {
                Type::Primitive(p) if p == "str" => {
                    if *is_mutable {
                        return Err("&mut str".into());
                    }
                    Ok(format!("&{n}: Text"))
                }
                Type::Slice(inner) => {
                    if *is_mutable {
                        return Err("&mut [T] is not supported".into());
                    }
                    Ok(format!("&{n}: Slice({})", self.ty(inner, owner, subst)?))
                }
                other => {
                    let inner = self.ty(other, owner, subst)?;
                    Ok(if *is_mutable {
                        format!("&mut {n}: {inner}")
                    } else {
                        format!("&{n}: {inner}")
                    })
                }
            },
            Type::ImplTrait(bounds) => {
                for b in bounds {
                    if let GenericBound::TraitBound { trait_, .. } = b
                        && matches!(
                            trait_.path.rsplit("::").next(),
                            Some("Fn" | "FnMut" | "FnOnce")
                        )
                        && let Some(args) = &trait_.args
                        && let GenericArgs::Parenthesized { inputs, output } = &**args
                    {
                        let ins: Result<Vec<String>, String> =
                            inputs.iter().map(|i| self.ty(i, owner, subst)).collect();
                        let out = match output {
                            Some(o) => self.ty(o, owner, subst)?,
                            None => "Unit".into(),
                        };
                        return Ok(format!("&{n}: ({}) -> {out}", ins?.join(", ")));
                    }
                }
                Err("an `impl Trait` argument".into())
            }
            other => Ok(format!("{n}: {}", self.ty(other, owner, subst)?)),
        }
    }

    /// A type as tauto writes it.
    fn ty(&self, t: &Type, owner: Option<(Id, &str)>, subst: &Subst) -> Result<String, String> {
        match t {
            Type::Primitive(p) => match p.as_str() {
                "bool" => Ok("Bool".into()),
                "f64" => Ok("Float".into()),
                "i32" | "i64" | "u8" | "u32" | "u64" => Ok(p.clone()),
                "usize" | "isize" => Err(format!(
                    "{p} nested in a type (only a parameter, the result, or an Option result is converted)"
                )),
                other => Err(format!("the type {other}")),
            },
            Type::Tuple(v) if v.is_empty() => Ok("Unit".into()),
            Type::Tuple(v) if v.len() == 2 => Ok(format!(
                "Pair({}, {})",
                self.ty(&v[0], owner, subst)?,
                self.ty(&v[1], owner, subst)?
            )),
            Type::Tuple(_) => Err("a tuple of more than two".into()),
            Type::Generic(g) if g == "Self" => match owner {
                Some((_, n)) => Ok(n.to_string()),
                None => Err("Self outside an impl".into()),
            },
            Type::Generic(g) => match subst.get(g) {
                Some((t, _)) if t != "&str" => Ok(t.clone()),
                _ => Err(format!("the type parameter {g}")),
            },
            Type::BorrowedRef {
                is_mutable, type_, ..
            } => match &**type_ {
                Type::Primitive(p) if p == "str" => Err("a &str nested in a type".into()),
                Type::Slice(inner) if !is_mutable => {
                    Ok(format!("&Slice({})", self.ty(inner, owner, subst)?))
                }
                other => {
                    let inner = self.ty(other, owner, subst)?;
                    Ok(if *is_mutable {
                        format!("&mut {inner}")
                    } else {
                        format!("&{inner}")
                    })
                }
            },
            Type::ResolvedPath(p) => {
                if let Some(n) = self.names.get(&p.id) {
                    return Ok(n.clone());
                }
                let last = p.path.rsplit("::").next().unwrap_or(&p.path);
                // `type Result<T> = std::result::Result<T, Error>`.
                if let Some(ItemEnum::TypeAlias(alias)) =
                    self.krate.index.get(&p.id).map(|i| &i.inner)
                {
                    let given: Vec<&Type> = match p.args.as_deref() {
                        Some(GenericArgs::AngleBracketed { args, .. }) => args
                            .iter()
                            .filter_map(|a| match a {
                                GenericArg::Type(t) => Some(t),
                                _ => None,
                            })
                            .collect(),
                        _ => Vec::new(),
                    };
                    let mut inner = Subst::new();
                    let mut given = given.into_iter();
                    for g in &alias.generics.params {
                        if let GenericParamDefKind::Type { .. } = g.kind {
                            let Some(t) = given.next() else {
                                return Err(format!(
                                    "the alias {} has a default parameter",
                                    p.path
                                ));
                            };
                            inner
                                .insert(g.name.clone(), (self.ty(t, owner, subst)?, String::new()));
                        }
                    }
                    return self.ty(&alias.type_, owner, &inner);
                }
                let args: Vec<&Type> = match p.args.as_deref() {
                    Some(GenericArgs::AngleBracketed { args, .. }) => args
                        .iter()
                        .filter_map(|a| match a {
                            GenericArg::Type(t) => Some(t),
                            _ => None,
                        })
                        .collect(),
                    _ => Vec::new(),
                };
                let each = |me: &Self| -> Result<Vec<String>, String> {
                    args.iter().map(|a| me.ty(a, owner, subst)).collect()
                };
                match (last, args.len()) {
                    ("String", 0) => Ok("Buf".into()),
                    ("Vec", 1) => Ok(format!("Vec({})", each(self)?[0])),
                    ("Option", 1) => Ok(format!("Option({})", each(self)?[0])),
                    ("Result", 2) => {
                        let v = each(self)?;
                        Ok(format!("Result({}, {})", v[0], v[1]))
                    }
                    _ => Err(format!("the type {} is not bound", p.path)),
                }
            }
            Type::Slice(_) => Err("an unsized slice".into()),
            Type::DynTrait(_) => Err("dyn Trait".into()),
            Type::ImplTrait(_) => Err("an `impl Trait` result".into()),
            _ => Err("a type that has no tauto form".into()),
        }
    }

    // ---- the files -----------------------------------------------------------

    fn render(
        &self,
        config_file: &str,
        bound: &[(Id, String, String, usize)],
        type_modules: &BTreeMap<String, Vec<String>>,
        root: &Module,
    ) -> Output {
        let version = self.krate.crate_version.clone().unwrap_or_default();
        let header = |c: &str| {
            format!(
                "{c} Generated by `tauto bind {}`: do not edit (change {config_file}).\n\
                 {c} crate {} {version}, rustdoc JSON format_version {}\n",
                self.cfg.crate_name,
                self.cfg.crate_name,
                rustdoc_types::FORMAT_VERSION
            )
        };
        let mut t = header("//");
        t.push('\n');
        for (_, name, _, lifetimes) in bound {
            let kw = if *lifetimes > 0 {
                "view struct"
            } else {
                "affine struct"
            };
            t.push_str(&format!("pub(open) {kw} {name} {{}}\n"));
        }
        for (name, lines) in type_modules {
            t.push_str(&format!("\nmodule {name} {{\n  extern {{\n"));
            for l in lines {
                t.push_str(&format!("    {l}\n"));
            }
            t.push_str("  }\n}\n");
        }
        render_module(&mut t, root, 0);

        let mut e = header("//");
        e.push_str(&format!("crate = \"{}\"\n", self.cfg.crate_name));
        e.push_str(&format!("version = \"{version}\"\n"));
        e.push_str(&format!(
            "format_version = {}\n",
            rustdoc_types::FORMAT_VERSION
        ));
        e.push_str(&format!("config = \"{config_file}\"\n"));
        e.push_str("generated_by = \"tauto bind\"\n\ntypes {\n");
        for (_, name, rust, lifetimes) in bound {
            // A view's Rust type has lifetimes: `Match<'_>`, `Matches<'_, '_>`.
            let lt = if *lifetimes > 0 {
                format!("<{}>", vec!["'_"; *lifetimes].join(", "))
            } else {
                String::new()
            };
            e.push_str(&format!("  {name} = \"{rust}{lt}\"\n"));
        }
        e.push_str("}\n\nextern {\n");
        for (name, rust) in &self.externs {
            e.push_str(&format!("  \"{name}\" = \"{rust}\"\n"));
        }
        e.push_str("}\n");
        if !self.marks.is_empty() {
            e.push_str("\nusize {\n");
            for (name, marks) in &self.marks {
                e.push_str(&format!("  \"{name}\" = \"{marks}\"\n"));
            }
            e.push_str("}\n");
        }

        let mut r = format!(
            "# tauto bind {}: report\n\n{}\nBound: {} types, {} functions.\n\n",
            self.cfg.crate_name,
            header("//").replace("//", ">").trim_end(),
            bound.len(),
            self.externs.len()
        );
        if self.report.is_empty() {
            r.push_str("Everything asked for was bound.\n");
        } else {
            r.push_str("Not bound (item: reason):\n\n");
            for line in &self.report {
                r.push_str(&format!("- {line}\n"));
            }
        }
        Output {
            tauto: t,
            eure: e,
            report: r,
        }
    }
}

fn render_module(out: &mut String, m: &Module, depth: usize) {
    let pad = "  ".repeat(depth);
    if !m.externs.is_empty() {
        out.push_str(&format!("{pad}extern {{\n"));
        for l in &m.externs {
            out.push_str(&format!("{pad}  {l}\n"));
        }
        out.push_str(&format!("{pad}}}\n"));
    }
    for (name, child) in &m.children {
        out.push_str(&format!("\n{pad}module {name} {{\n"));
        render_module(out, child, depth + 1);
        out.push_str(&format!("{pad}}}\n"));
    }
}

fn is_ident(s: &str) -> bool {
    let mut cs = s.chars();
    cs.next().is_some_and(|c| c.is_alphabetic() || c == '_')
        && s != "_"
        && cs.all(|c| c.is_alphanumeric() || c == '_')
}

/// A `usize` / `isize` in a parameter or the result, or an `Option` of one:
/// the mark (`p` / `q` for a parameter, `o` / `t` for an `Option` result)
/// and the type tauto sees (`u64` / `i64`).
fn int_mark(t: &Type) -> Option<(&'static str, String)> {
    match t {
        Type::Primitive(p) if p == "usize" => Some(("p", "u64".into())),
        Type::Primitive(p) if p == "isize" => Some(("q", "i64".into())),
        Type::ResolvedPath(p) if p.path.rsplit("::").next() == Some("Option") => {
            let Some(GenericArgs::AngleBracketed { args, .. }) = p.args.as_deref() else {
                return None;
            };
            match args.as_slice() {
                [GenericArg::Type(Type::Primitive(n))] if n == "usize" => {
                    Some(("o", "Option(u64)".into()))
                }
                [GenericArg::Type(Type::Primitive(n))] if n == "isize" => {
                    Some(("t", "Option(i64)".into()))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// `Cow<'_, str>`, which tauto sees as the `Buf` it turns into.
fn is_cow_str(t: &Type) -> bool {
    let Type::ResolvedPath(p) = t else {
        return false;
    };
    if p.path.rsplit("::").next() != Some("Cow") {
        return false;
    }
    let Some(GenericArgs::AngleBracketed { args, .. }) = p.args.as_deref() else {
        return false;
    };
    matches!(
        args.iter()
            .filter_map(|a| match a {
                GenericArg::Type(t) => Some(t),
                _ => None,
            })
            .collect::<Vec<_>>()
            .as_slice(),
        [Type::Primitive(n)] if n == "str"
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value, json};

    fn item(id: u32, name: &str, inner: Value) -> Value {
        json!({
            "id": id, "crate_id": 0, "name": name, "span": null,
            "visibility": "public", "docs": null, "links": {},
            "attrs": [], "deprecation": null, "inner": inner,
        })
    }

    fn identity(ty: Value, params: Value) -> Value {
        json!({"function": {
            "sig": {"inputs": [["x", ty.clone()]], "output": ty, "is_c_variadic": false},
            "generics": {"params": params, "where_predicates": []},
            "header": {"is_const": false, "is_unsafe": false, "is_async": false, "abi": "Rust"},
            "has_body": true,
        }})
    }

    #[test]
    fn f64_parameters_results_and_instances_use_float() {
        let krate: Crate = serde_json::from_value(json!({
            "root": 0, "crate_version": "0.0.0", "includes_private": false,
            "index": {
                "0": item(0, "fixture", json!({"module": {"is_crate": true, "items": [1, 2], "is_stripped": false}})),
                "1": item(1, "identity", identity(json!({"primitive": "f64"}), json!([]))),
                "2": item(2, "generic_identity", identity(json!({"generic": "T"}), json!([{
                    "name": "T", "kind": {"type": {"bounds": [], "default": null, "is_synthetic": false}}
                }]))),
            },
            "paths": {}, "external_crates": {},
            "target": {"triple": "x86_64-unknown-linux-gnu", "target_features": []},
            "format_version": rustdoc_types::FORMAT_VERSION,
        })).unwrap();
        let cfg = Config {
            crate_name: "fixture".into(),
            items: vec![
                "fixture::identity".into(),
                "fixture::generic_identity".into(),
            ],
            instances: BTreeMap::from([("fixture::generic_identity".into(), vec!["f64".into()])]),
            ..Config::default()
        };
        let out = generate(&krate, &cfg, "fixture.config.eure");
        assert!(
            out.tauto.contains("fn identity(x: Float): Float"),
            "{}",
            out.tauto
        );
        assert!(
            out.tauto.contains("fn generic_identity(x: Float): Float"),
            "{}",
            out.tauto
        );
        assert!(
            out.eure.contains("fixture::generic_identity::<f64>"),
            "{}",
            out.eure
        );
        assert!(
            out.report.contains("Everything asked for was bound."),
            "{}",
            out.report
        );
    }
}
