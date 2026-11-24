//! JavaScript computations with explicit continuations. The runtime drives
//! these computations on the host event loop, independently of Rust tiers.
use crate::{R, bounds, quote, unsupported};
use std::collections::{BTreeMap, BTreeSet};
use tauto_message::msg;
use tauto_nir::cps::{Cps, CpsPat, MatchArm, PathStep, Prim, Unary, Value};
use tauto_nir::*;

// Runtime provenance checks the representation as well: a generic or aggregate
// field is eligible only when its actual value has an ownership certificate.
pub(crate) fn retainable_field(ty: &Ty) -> bool {
    match ty {
        Ty::Ref(_) | Ty::RefMut(_) | Ty::Slice(_) => false,
        Ty::Fn(f) => f.kind.dup(),
        _ => true,
    }
}

/// What the host configuration adds to a module.
#[derive(Debug, Clone, Default)]
pub struct Options {
    /// Fieldless structs whose values are host objects.
    pub host_types: BTreeSet<String>,
    /// Functions an instance of the module exports, by source name.
    pub exports: Vec<String>,
    /// Externs whose callbacks outlive the call: the first host value
    /// argument owns them until Tauto drops its last reference.
    pub retain: BTreeSet<String>,
    /// Modules loaded on the first call of one of their entry functions:
    /// the module's name and the entry functions, by source name.
    pub chunks: BTreeMap<String, Vec<String>>,
}

/// A program written as `program.mjs` and one module per chunk.
#[derive(Debug, Clone)]
pub struct Modules {
    pub program: String,
    pub chunks: Vec<(String, String)>,
}

pub fn generate(pkg: &Package) -> R<String> {
    generate_with(pkg, &Options::default())
}

/// The host type an extern parameter or result carries directly.
fn host_type<'t>(ty: &'t Ty, options: &Options) -> R<Option<&'t str>> {
    let found = |ty: &'t Ty| match ty {
        Ty::Data(name, args) if args.is_empty() && options.host_types.contains(name.as_str()) => {
            Some(name.as_str())
        }
        _ => None,
    };
    let direct = match ty {
        Ty::Ref(inner) | Ty::RefMut(inner) => found(inner),
        _ => found(ty),
    };
    if direct.is_none() && mentions_host_type(ty, options) {
        return unsupported(msg!("jsgen-what-host-type-in-extern"));
    }
    Ok(direct)
}

fn mentions_host_type(ty: &Ty, options: &Options) -> bool {
    let mut found = false;
    let text = format!("{ty:?}");
    for name in &options.host_types {
        found |= text.contains(&format!("Data({name:?}"));
    }
    found
}

fn host_signatures(pkg: &Package, options: &Options) -> R<String> {
    let quoted = |t: Option<&str>| t.map(quote).unwrap_or("null".into());
    let mut out = String::from("const hostSignatures={");
    for x in &pkg.externs {
        let mut params = Vec::new();
        for (_, ty, _) in &x.params {
            params.push(quoted(host_type(ty, options)?));
        }
        let ret = host_type(&x.ret, options)?;
        if matches!(x.ret, Ty::Ref(_) | Ty::RefMut(_)) && ret.is_some() {
            return unsupported(msg!("jsgen-what-borrowed-host-return"));
        }
        let owner = if options.retain.contains(x.name.as_str()) {
            let Some(owner) = params.iter().position(|p| p != "null") else {
                return Err(
                    msg!("jsgen-extern-retain-owner", name = x.name.to_string()).to_string()
                );
            };
            for (_, ty, pass) in &x.params {
                if let Ty::Fn(f) = ty
                    && (*pass != Pass::Value || f.tier != Tier::S)
                {
                    return Err(
                        msg!("jsgen-extern-retain-callbacks", name = x.name.to_string())
                            .to_string(),
                    );
                }
            }
            owner.to_string()
        } else {
            "null".into()
        };
        if ret.is_some() || params.iter().any(|p| p != "null") {
            out.push_str(&format!(
                "{}:{{params:[{}],ret:{},owner:{owner}}},",
                quote(&x.name),
                params.join(","),
                quoted(ret)
            ));
        }
    }
    out.push_str("};\n");
    // The externs whose row is `{wait}`: only these may answer with a Promise.
    let waits: Vec<String> = pkg
        .externs
        .iter()
        .filter(|x| x.waits)
        .map(|x| quote(&x.name))
        .collect();
    out.push_str(&format!(
        "const hostWaits=new Set([{}]);\n",
        waits.join(",")
    ));
    out.push_str(&hash_seed_answer(pkg));
    Ok(out)
}

/// How the runtime makes the answer to the library's `hash_seed` performed
/// outside `Host::run` (by an exported function or a task): the operation's
/// symbol and the `HashSeed` it answers with, which only the package names.
fn hash_seed_answer(pkg: &Package) -> String {
    let answer = pkg
        .ops
        .iter()
        .find(|o| tauto::bindings::is_library_effect(&o.name, "hash_seed"))
        .and_then(|o| match &o.result {
            Ty::Data(n, args) if args.is_empty() => pkg
                .datas
                .iter()
                .find(|d| d.name == *n && d.is_struct && d.ctors.len() == 1)
                .map(|d| (o, d)),
            _ => None,
        })
        .and_then(|(o, d)| {
            let ctor = &d.ctors[0];
            let names: Vec<_> = ctor
                .fields
                .iter()
                .map(|f| f.name.as_deref())
                .collect();
            let at = |n: &str| names.iter().position(|f| *f == Some(n));
            let (k0, k1) = (at("k0")?, at("k1")?);
            (names.len() == 2).then(|| {
                format!(
                    "{{op:{},tag:{},names:[{}],k0:{k0},k1:{k1},owner:{}}}",
                    quote(&crate::operation_symbol(pkg, &o.name)),
                    quote(crate::constructor_symbol(pkg, &ctor.name)),
                    names
                        .iter()
                        .map(|n| quote(n.unwrap_or_default()))
                        .collect::<Vec<_>>()
                        .join(","),
                    quote(&crate::owner_symbol(pkg, &d.name)),
                )
            })
        });
    format!(
        "const hashSeedAnswer={};\n",
        answer.unwrap_or_else(|| "null".into())
    )
}

/// Whether a function reaches the host other than through `show`.
/// A chunk's entry waits for its module the first time.
fn reaches_host(
    pkg: &Package,
    id: InstId,
    waits: &BTreeMap<InstId, String>,
    seen: &mut BTreeSet<InstId>,
) -> bool {
    if !seen.insert(id) {
        return false;
    }
    if waits.contains_key(&id) {
        return true;
    }
    let Some(f) = pkg.fns.iter().find(|f| f.id == id) else {
        return true;
    };
    let mut callees = Vec::new();
    let mut host = false;
    f.body.walk_with_handlers(&mut |e| match &e.kind {
        ExprKind::Call(call) => match &call.callee {
            Callee::Inst(i) => callees.push(*i),
            Callee::Extern(_) => host = true,
            Callee::Builtin(name) if name.starts_with("Os::") => host = true,
            _ => {}
        },
        ExprKind::FnValue { inst, .. } => callees.push(*inst),
        _ => {}
    });
    host || callees
        .into_iter()
        .any(|i| reaches_host(pkg, i, waits, seen))
}

/// How a value of an exported function's signature crosses to the host.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Crossing {
    /// As for externs (`javascript-backend.md`「Host bindings」).
    Value,
    /// A host object kept in a handle of the instance.
    Host(String),
    /// A borrowed host object, valid during the call.
    BorrowedHost(String),
    /// A borrowed host function, callable during the call.
    HostFn,
    /// A Nib function the instance keeps until it is disposed.
    KeptFn,
}

impl Crossing {
    fn js(&self) -> String {
        match self {
            Crossing::Value => "null".into(),
            Crossing::Host(t) => format!("{{host:{}}}", quote(t)),
            Crossing::BorrowedHost(t) => format!("{{host:{},borrowed:true}}", quote(t)),
            Crossing::HostFn => "{fn:true}".into(),
            Crossing::KeptFn => "{kept:true}".into(),
        }
    }
}

pub(crate) struct ExportEntry<'p> {
    pub name: &'p str,
    pub f: &'p FnInst,
    /// Returns its value synchronously.
    pub sync: bool,
    pub params: Vec<Crossing>,
    pub ret: Crossing,
}

/// The exported functions, checked, and whether each one returns synchronously.
pub(crate) fn export_table<'p>(pkg: &'p Package, options: &Options) -> R<Vec<ExportEntry<'p>>> {
    let waits = crate::chunks::entries(pkg, options)?;
    let mut table = Vec::new();
    for name in &options.exports {
        let Some(export) = pkg.exports.iter().find(|e| &e.name == name) else {
            return Err(msg!("jsgen-export-not-function", name = name.to_string()).to_string());
        };
        // A task the export starts runs on in the instance after the call
        // returns, until the instance is disposed. The allowed effects are the
        // library's `show`, `div`, `wait`, `spawn`, `hash_seed` and the
        // operations on a `Ref`, a `Weak`, a `Mutex` or an `Atomic`, which the
        // runtime answers as it does for a task; told by identity: a user
        // effect of the same spelling is not one of them.
        if let Some(effect) = export.foreign_row.first() {
            return Err(msg!("jsgen-export-performs", name = name, effect = effect).to_string());
        }
        let f = pkg
            .fns
            .iter()
            .find(|f| f.id == export.inst)
            .expect("an export is lowered");
        let refuse = |what: &'static str| {
            Err(msg!("jsgen-export-signature", name = name, what = msg!(what)).to_string())
        };
        let host = |ty: &Ty| match ty {
            Ty::Data(n, args) if args.is_empty() && options.host_types.contains(n.as_str()) => {
                Some(n.to_string())
            }
            _ => None,
        };
        let mut params = Vec::new();
        for p in &f.params {
            let (ty, borrowed) = match &p.ty {
                Ty::Ref(inner) => (&**inner, true),
                Ty::RefMut(_) => return refuse("jsgen-what-mutable-borrow"),
                ty => (
                    ty,
                    matches!(p.local.storage(), Storage::Borrow | Storage::BorrowedFn),
                ),
            };
            if p.local.storage() == Storage::BorrowMut {
                return refuse("jsgen-what-mutable-borrow");
            }
            let crossing = match (ty, host(ty)) {
                (_, Some(t)) if borrowed => Crossing::BorrowedHost(t),
                (_, Some(t)) => Crossing::Host(t),
                (Ty::Fn(_), None) if borrowed => Crossing::HostFn,
                (Ty::Fn(_), None) => return refuse("jsgen-what-function-by-value"),
                _ if borrowed => return refuse("jsgen-what-borrow"),
                _ if mentions_host_type(ty, options) => {
                    return refuse("jsgen-what-host-type-inside");
                }
                _ => Crossing::Value,
            };
            params.push(crossing);
        }
        let ret = match (&f.ret, host(&f.ret)) {
            (_, Some(t)) => Crossing::Host(t),
            (Ty::Fn(ft), None) if ft.tier == Tier::S => Crossing::KeptFn,
            (Ty::Fn(_), None) => {
                return refuse("jsgen-what-effectful-function-result");
            }
            (Ty::Ref(_) | Ty::RefMut(_), _) => return refuse("jsgen-what-borrow"),
            _ if mentions_host_type(&f.ret, options) => {
                return refuse("jsgen-what-host-type-inside");
            }
            _ => Crossing::Value,
        };
        // A host function may return a Promise.
        let sync = !params.contains(&Crossing::HostFn)
            && !export.row.iter().any(|effect| effect == "wait")
            && !reaches_host(pkg, export.inst, &waits, &mut BTreeSet::new());
        table.push(ExportEntry {
            name: export.name.as_str(),
            f,
            sync,
            params,
            ret,
        });
    }
    Ok(table)
}

fn exports(pkg: &Package, options: &Options) -> R<String> {
    let table: Vec<String> = export_table(pkg, options)?
        .into_iter()
        .map(|e| {
            let params = e.params.iter().map(Crossing::js).collect::<Vec<_>>();
            format!(
                "{}:[f{},{},[{}],{}]",
                quote(e.name),
                e.f.id,
                e.sync,
                params.join(","),
                e.ret.js()
            )
        })
        .collect();
    Ok(format!(
        "\nexport function instantiate(externs={{}}, options={{}}) {{return instantiateWith({{{}}},externs,options);}}\n",
        table.join(",")
    ))
}

pub fn generate_with(pkg: &Package, options: &Options) -> R<String> {
    let modules = generate_modules(pkg, options)?;
    if !modules.chunks.is_empty() {
        return Err(msg!("jsgen-chunks-need-modules").to_string());
    }
    Ok(modules.program)
}

/// `program.mjs` and the module of each chunk (`chunks.rs`).
/// The name `shown` writes for each constructor whose full name is not the
/// name written. Structures display their type name and enum values display
/// their constructor's leaf, as the evaluator and the Rust backend do.
fn shown_names(pkg: &Package) -> String {
    let pairs: Vec<String> = pkg
        .datas
        .iter()
        .flat_map(|d| d.ctors.iter().map(move |c| (d, c)))
        .filter_map(|(d, c)| {
            let tag = crate::constructor_symbol(pkg, &c.name);
            let short = if d.is_struct {
                tauto::surface::qualify::short(&d.name)
            } else {
                tag.rsplit("::").next().unwrap()
            };
            (short != tag).then(|| format!("[{},{}]", quote(tag), quote(short)))
        })
        .collect();
    format!("\nconst shownNames=new Map([{}]);\n", pairs.join(","))
}

pub fn generate_modules(pkg: &Package, options: &Options) -> R<Modules> {
    let entries = crate::chunks::entries(pkg, options)?;
    let owners = crate::chunks::owners(pkg, &entries);
    // The runtime (`shake.rs`) goes in front once the rest is written.
    let mut out = format!(
        "const declarationRefs=Array.from({{length:{}}},()=>Symbol());\n",
        pkg.declarations.len()
    );
    out.push_str(&host_signatures(pkg, options)?);
    out.push_str(&shown_names(pkg));
    let (parsers, synrun) = crate::syntax::parsers(pkg)?;
    out.push_str(&parsers);
    // An entry is called through its stub, which may wait, so it and its
    // callers have no direct form.
    let direct = crate::direct::functions(pkg, &entries.keys().copied().collect());
    let chunk_names: Vec<&String> = options.chunks.keys().collect();
    let mut chunks: BTreeMap<&str, String> = BTreeMap::new();
    for (i, name) in chunk_names.iter().enumerate() {
        out.push_str(&format!("\nlet chunk{i}=null;\n"));
        chunks.insert(name.as_str(), String::new());
    }
    for f in &pkg.fns {
        if pkg.host_omitted_fns.contains(&f.id) {
            continue;
        }
        // Host-selected replaceable members are `external(...)` calls; their
        // Tauto bodies are not emitted. A thin `fN` stub remains so
        // `FnValue` / function values still resolve.
        if pkg
            .externs
            .iter()
            .any(|e| e.name.as_str() == f.source.as_str())
        {
            let text = match owners.get(&f.id) {
                Some(chunk) => chunks
                    .get_mut(chunk.as_str())
                    .expect("a chunk of the manifest"),
                None => &mut out,
            };
            text.push_str(&format!(
                "\nfunction f{}(c,args,k){{return external({},args.map(pure))(c,k);}}\n",
                f.id,
                quote(&f.source)
            ));
            continue;
        }
        let text = match owners.get(&f.id) {
            Some(chunk) => chunks
                .get_mut(chunk.as_str())
                .expect("a chunk of the manifest"),
            None => &mut out,
        };
        let name = if direct.contains(&f.id) {
            text.push_str(&crate::direct::write(pkg, f, &format!("g{}", f.id))?);
            if crate::direct::constant(f) {
                text.push_str(&crate::direct::constant_cps(f));
                continue;
            }
            "g"
        } else {
            "f"
        };
        let params = f
            .params
            .iter()
            .map(|p| p.local.id.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let export_borrows = crate::borrowed_returns::needs_export(pkg, &f.ret);
        let owned = f
            .params
            .iter()
            .map(|p| (p.local.storage() == Storage::Owned).to_string())
            .collect::<Vec<_>>()
            .join(",");
        // A call marked `recur` restarts the frame (`tailSelfCall`): the marks
        // already ask that what it borrows lives outside the frame, that no drop
        // the frame does early is observable, and that no continuation of the
        // function resumes twice, so a recursion that borrows or performs runs
        // in constant stack and memory too.
        let restart = tauto_nir::recurs(&f.body);
        let body = Print { pkg }
            .cps(&tauto_nir::cps::lower(pkg, f, restart).or_else(|what| unsupported(what))?)?;
        text.push_str(&format!("\nconst b{} = {body};\nfunction {name}{}(c,args,k){{return enterFunction(b{},[{params}],null,c,args,k,false,{export_borrows},[{owned}],{restart});}}\n",f.id,f.id,f.id));
    }
    for (id, chunk) in &entries {
        let i = chunk_names
            .iter()
            .position(|n| *n == chunk)
            .expect("a chunk of the manifest");
        let file = quote(&format!("./chunk-{chunk}.mjs"));
        out.push_str(&format!("\nfunction f{id}(c,args,k){{if(chunk{i})return chunk{i}.f{id}(c,args,k);return import({file}).then(m=>{{chunk{i}=m;return ()=>m.f{id}(c,args,k);}});}}\n"));
    }
    let top = pkg
        .top
        .map(|i| format!("(c,k)=>f{i}(c,[],k)"))
        .unwrap_or("pure(null)".into());
    out.push_str(&exports(pkg, options)?);
    // The permissions of the standard effects that reach the top level: a
    // run without one does not start.
    let needs: Vec<String> = pkg.permissions.iter().map(|p| format!("'{p}'")).collect();
    let check = if needs.is_empty() {
        String::new()
    } else {
        format!(
            "const missing=missingPermissions(options,[{}]);if(missing.length)throw Object.assign(new Error(missingMessage(missing)),{{exitCode:2,denied:true}});",
            needs.join(",")
        )
    };
    out.push_str(&format!("\nexport async function run(show=console.log, externs={{}}, options={{}}) {{{check}return drive({top},show,externs,options);}}\n"));
    let roots: String = chunks.values().fold(out.clone(), |a, b| a + b);
    out = crate::shake::shake(&roots) + &synrun + &out;
    if entries.is_empty() {
        return Ok(Modules {
            program: out,
            chunks: Vec::new(),
        });
    }
    // A chunk reads what `program.mjs` declares through imports.
    let shared = crate::chunks::declared(&out);
    out.push_str(&format!("export {{{}}};\n", shared.join(",")));
    let mut written = Vec::new();
    for (chunk, body) in chunks {
        let own: BTreeSet<String> = crate::chunks::declared(&body).into_iter().collect();
        let imports: Vec<&str> = shared
            .iter()
            .filter(|n| !own.contains(*n))
            .map(String::as_str)
            .collect();
        let exported: Vec<String> = entries
            .iter()
            .filter(|(_, c)| c.as_str() == chunk)
            .map(|(id, _)| format!("f{id}"))
            .collect();
        written.push((
            format!("chunk-{chunk}.mjs"),
            format!(
                "import {{{}}} from './program.mjs';\n{body}export {{{}}};\n",
                imports.join(","),
                exported.join(",")
            ),
        ));
    }
    Ok(Modules {
        program: out,
        chunks: written,
    })
}
/// Writes a computation as the runtime's combinators (`cps.js`).
struct Print<'a> {
    pkg: &'a Package,
}

impl Print<'_> {
    fn all(&self, es: &[Cps]) -> R<String> {
        Ok(es
            .iter()
            .map(|e| self.cps(e))
            .collect::<R<Vec<_>>>()?
            .join(","))
    }
    fn values(&self, args: &[Cps], value: &str) -> R<String> {
        Ok(format!(
            "values([{}],(c,vs,k)=>more(()=>k(c,{value})))",
            self.all(args)?
        ))
    }
    fn arm(&self, a: &MatchArm) -> R<String> {
        Ok(format!(
            "[{},{},{}]",
            pattern(self.pkg, &a.pat),
            self.cps(&a.guard)?,
            self.cps(&a.body)?
        ))
    }
    fn cps(&self, e: &Cps) -> R<String> {
        Ok(match e {
            Cps::Pure(v) => format!("pure({})", value(v)),
            Cps::ReadLocal {
                id,
                deref,
                copy,
                take,
            } => format!("readLocal({id},{deref},{copy},{take})"),
            Cps::Call {
                callee,
                args,
                ticked,
            } => format!(
                "callFunction({},[{}],{ticked})",
                self.cps(callee)?,
                self.all(args)?
            ),
            Cps::TailSelfCall {
                inst,
                args,
                ticked: false,
            } => {
                format!("tailSelfCall(pure(f{inst}),[{}])", self.all(args)?)
            }
            // A step of the host's limit is counted where a call is made.
            Cps::TailSelfCall {
                inst,
                args,
                ticked: true,
            } => format!("callFunction(pure(f{inst}),[{}],true)", self.all(args)?),
            Cps::External { name, args } => {
                format!("external({},[{}])", quote(name), self.all(args)?)
            }
            Cps::Builtin { name, args } => {
                if name.starts_with("Ct::") {
                    // `docs/design/secret.md`: numbers and BigInts promise no
                    // constant time, so the secret words are refused.
                    return unsupported(msg!("jsgen-what-secret-words"));
                }
                if !BUILTINS.contains(&name.as_str())
                    && !crate::FLOAT_BUILTINS.contains(&name.as_str())
                {
                    return unsupported(msg!("jsgen-what-builtin", name = name.as_str()));
                }
                format!("builtin({},[{}])", quote(name), self.all(args)?)
            }
            Cps::Prim { op, args } => self.prim(op, args)?,
            Cps::Map { value, op } => {
                let temporary = matches!(&**value, Cps::External { .. });
                let value = self.cps(value)?;
                match op {
                    Unary::Not => format!("mapValue({value},v=>!v)"),
                    Unary::Field { name, index } => format!(
                        "mapValue({value},v=>field(v,{},{}))",
                        quote(name),
                        index.map(|n| n.to_string()).unwrap_or("null".into())
                    ),
                    Unary::Shown => {
                        format!("mapValue({value},v=>({{kind:'Shown',text:shown(v)}}))")
                    }
                    Unary::TempRef { shared } => {
                        format!("mapValue({value},v=>temporaryRef(v,{shared}))")
                    }
                    // The view a call returns is held by nothing once copied.
                    Unary::Deref { copy: true } if temporary => {
                        format!("mapValue({value},v=>dereferenceTemporary(v))")
                    }
                    Unary::Deref { copy } => format!("mapValue({value},v=>dereference(v,{copy}))"),
                    Unary::Inject { union, variant } => format!(
                        "mapValue({value},value=>({{union:{union},variant:{variant},value}}))"
                    ),
                    Unary::Remap { to, table } => format!(
                        "mapValue({value},v=>remapUnion(v,{},[{}]))",
                        to.map(|n| n.to_string()).unwrap_or("null".into()),
                        table
                            .iter()
                            .map(|n| n.map(|n| n.to_string()).unwrap_or("null".into()))
                            .collect::<Vec<_>>()
                            .join(",")
                    ),
                }
            }
            Cps::Branch {
                cond,
                then,
                otherwise,
            } => format!(
                "branch({},{},{})",
                self.cps(cond)?,
                self.cps(then)?,
                self.cps(otherwise)?
            ),
            Cps::Sequence(es) => format!("sequence([{}])", self.all(es)?),
            Cps::Define {
                id,
                shared,
                init,
                immutable,
                ..
            } => format!("defineLocal({id},{shared},{},{immutable})", self.cps(init)?),
            Cps::Assign {
                id,
                path: p,
                through_borrow,
                value,
            } => format!(
                "assignPlace({id},{},{through_borrow},{})",
                path(p),
                self.cps(value)?
            ),
            Cps::While { cond, body, ticked } => format!(
                "loopWhile({},{},{ticked})",
                self.cps(cond)?,
                self.cps(body)?
            ),
            Cps::Return(v) => format!("returnValue({})", self.cps(v)?),
            Cps::Match { scrut, arms } => {
                // A moved or copied local is the match's own value, so the
                // chosen arm's bindings take its parts instead of copying
                // them. A guard could still reject an arm after binding.
                let owned = matches!(
                    &**scrut,
                    Cps::ReadLocal { take: true, .. } | Cps::ReadLocal { copy: true, .. }
                );
                let guardless = arms
                    .iter()
                    .all(|a| matches!(a.guard, Cps::Pure(Value::Bool(true))));
                format!(
                    "matchValue({},[{}],{})",
                    self.cps(scrut)?,
                    arms.iter()
                        .map(|a| self.arm(a))
                        .collect::<R<Vec<_>>>()?
                        .join(","),
                    owned && guardless
                )
            }
            Cps::Closure(c) => {
                let ids =
                    |ids: &[u32]| ids.iter().map(u32::to_string).collect::<Vec<_>>().join(",");
                format!(
                    "closureValue({},[{}],[{}],{},[{}],{},[{}],[{}],{},[{}])",
                    self.cps(&c.body)?,
                    ids(&c.params),
                    ids(&c.captures),
                    c.borrowed,
                    c.refs
                        .iter()
                        .map(|(inner, outer)| format!("[{inner},{outer}]"))
                        .collect::<Vec<_>>()
                        .join(","),
                    crate::borrowed_returns::needs_export(self.pkg, &c.ret),
                    c.owned
                        .iter()
                        .map(bool::to_string)
                        .collect::<Vec<_>>()
                        .join(","),
                    ids(&c.moves),
                    c.once,
                    ids(&c.owned_refs)
                )
            }
            Cps::Perform { op, quant: q, args } => format!(
                "performValue({},{},[{}])",
                quote(&crate::operation_symbol(self.pkg, op)),
                quote(quant(*q)),
                self.all(args)?
            ),
            Cps::Handle { body, arms, ret } => {
                let arms = arms
                    .iter()
                    .map(|a| {
                        Ok(format!(
                            "{{op:{},pats:[{}],k:{},guard:{},body:{}}}",
                            quote(&crate::operation_symbol(self.pkg, &a.op)),
                            a.pats
                                .iter()
                                .map(|p| pattern(self.pkg, p))
                                .collect::<Vec<_>>()
                                .join(","),
                            a.k.map(|k| k.to_string()).unwrap_or("null".into()),
                            self.cps(&a.guard)?,
                            self.cps(&a.body)?
                        ))
                    })
                    .collect::<R<Vec<_>>>()?
                    .join(",");
                let ret = ret
                    .as_ref()
                    .map(|r| self.arm(r))
                    .transpose()?
                    .unwrap_or("null".into());
                format!("handleValue({},[{arms}],{ret})", self.cps(body)?)
            }
            Cps::BorrowPlace {
                id,
                path: p,
                through_borrow,
                ..
            } => format!("borrowPlace({id},{},{through_borrow})", path(p)),
            Cps::Budget {
                id,
                memory,
                steps,
                body,
            } => format!(
                "budgetValue({id}, {}, {}, {memory})",
                self.cps(steps)?,
                self.cps(body)?
            ),
        })
    }
    fn prim(&self, op: &Prim, args: &[Cps]) -> R<String> {
        if let Prim::SynParse { name, sha, ty } = op {
            let Some(i) = crate::syntax::parser_index(self.pkg, name, sha, ty) else {
                return unsupported(msg!("jsgen-what-syn-parse-without-tables"));
            };
            return Ok(format!(
                "values([{}],(c,vs,k)=>more(()=>k(c,synParse{i}(unref(vs[0])))))",
                self.all(args)?
            ));
        }
        let value = self.prim_value(op)?;
        // An operator whose result does not exist performs `overflow` or
        // `divzero` where it stands.
        if matches!(op, Prim::Arith(..) | Prim::FloatArith(_) | Prim::Float32Arith(_)) {
            return Ok(format!(
                "values([{}],(c,vs,k)=>operated(c,k,()=>{value}))",
                self.all(args)?
            ));
        }
        self.values(args, &value)
    }
    fn prim_value(&self, op: &Prim) -> R<String> {
        Ok(match op {
            Prim::Arith(op, width) => {
                let value = match op {
                    Arith::Add => "vs[0]+vs[1]",
                    Arith::Sub => "vs[0]-vs[1]",
                    Arith::Mul => "vs[0]*vs[1]",
                    Arith::Neg => "-vs[0]",
                    Arith::Div => return unsupported(msg!("jsgen-what-integer-division")),
                };
                format!("checked({value},{})", bounds(*width))
            }
            Prim::FloatArith(op) => match op {
                Arith::Add => "vs[0]+vs[1]",
                Arith::Sub => "vs[0]-vs[1]",
                Arith::Mul => "vs[0]*vs[1]",
                Arith::Neg => "-vs[0]",
                Arith::Div => "floatDiv(vs[0],vs[1])",
            }
            .into(),
            Prim::Float32Arith(op) => match op {
                Arith::Add => "Math.fround(vs[0]+vs[1])",
                Arith::Sub => "Math.fround(vs[0]-vs[1])",
                Arith::Mul => "Math.fround(vs[0]*vs[1])",
                Arith::Neg => "-vs[0]",
                Arith::Div => "float32Div(vs[0],vs[1])",
            }
            .into(),
            Prim::Cmp(op) => format!(
                "vs[0] {} vs[1]",
                match op {
                    Cmp::Lt => "<",
                    Cmp::Gt => ">",
                    Cmp::Le => "<=",
                    Cmp::Ge => ">=",
                }
            ),
            Prim::Eq { negate } => {
                format!("{}equal(vs[0],vs[1])", if *negate { "!" } else { "" })
            }
            Prim::Construct {
                ctor,
                names,
                order,
                is_struct,
                data,
                field_types,
            } => format!(
                "construct({},[{}],vs,[{}],{is_struct},{},{})",
                quote(crate::constructor_symbol(self.pkg, ctor)),
                names
                    .iter()
                    .map(|n| n.as_ref().map(|n| quote(n)).unwrap_or("null".into()))
                    .collect::<Vec<_>>()
                    .join(","),
                order
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(","),
                quote(&crate::owner_symbol(self.pkg, data)),
                field_types.iter().all(retainable_field)
            ),
            Prim::Concat => "vs.join('')".into(),
            Prim::TextOfInt => "String(vs[0])".into(),
            Prim::TextLen => "BigInt(textBytes(unref(vs[0])).length)".into(),
            Prim::TextCompare => "compare(unref(vs[0]),unref(vs[1]))".into(),
            Prim::Divide { name, width } => {
                format!("divide({},vs,{})", quote(name), bounds(*width))
            }
            Prim::SynParse { .. } => unreachable!("a syntax parse is written by `prim`"),
        })
    }
}
fn value(v: &Value) -> String {
    match v {
        Value::Unit => "null".into(),
        Value::Int(n) => format!("{n}n"),
        Value::Float(x) => float_literal(*x),
        Value::Bool(b) => b.to_string(),
        Value::Declaration(slot) => format!("declarationRefs[{slot}]"),
        Value::Text(t) => quote(t),
        Value::Fn(i) => format!("f{i}"),
    }
}
/// A finite `Float` as JavaScript reads it back exactly: Rust's shortest
/// digits, with an exponent where it has one (`1e300`).
pub(crate) fn float_literal(x: f64) -> String {
    format!("{x:?}")
}
fn quant(q: Quant) -> &'static str {
    match q {
        Quant::Direct => "direct",
        Quant::Zero => "zero",
        Quant::AtMostOne => "optional",
        Quant::One => "one",
        Quant::Many => "many",
    }
}
fn pattern(pkg: &Package, p: &CpsPat) -> String {
    match p {
        CpsPat::Wild => "['wild']".into(),
        CpsPat::Bind {
            id, borrow, owned, ..
        } => format!("['bind',{id},{borrow},{owned}]"),
        CpsPat::Literal(v) => format!("['literal',{}]", value(v)),
        CpsPat::Ctor { ctor, fields, data } => format!(
            "['ctor',{},[{}],{}]",
            quote(crate::constructor_symbol(pkg, ctor)),
            fields
                .iter()
                .map(|p| pattern(pkg, p))
                .collect::<Vec<_>>()
                .join(","),
            quote(&crate::owner_symbol(pkg, data))
        ),
        CpsPat::Variant { variant, pat, .. } => {
            format!("['variant',{variant},{}]", pattern(pkg, pat))
        }
    }
}

fn path(steps: &[PathStep]) -> String {
    format!(
        "[{}]",
        steps
            .iter()
            .map(|s| match s {
                PathStep::Index(n) => n.to_string(),
                PathStep::Name(name) => quote(name),
            })
            .collect::<Vec<_>>()
            .join(",")
    )
}

pub const BUILTINS: &[&str] = &[
    "clone",
    "replace",
    "Buf::new",
    "Buf::of",
    "Buf::clone",
    "Buf::push",
    "Text::of",
    "Vec::new",
    "Vec::push",
    "Vec::pop",
    "Vec::len",
    "Slice::len",
    "Vec::as_slice",
    "Vec::as_mut_slice",
    "Vec::clear",
    "Vec::truncate",
    "Vec::swap_within",
    "Slots::new",
    "Slots::copy",
    "Slots::state",
    "Slots::cap",
    "Slots::mark",
    "Slots::get",
    "Slots::get_mut",
    "Slots::put",
    "Slots::take",
    "Slots::resize",
    "Vec::get",
    "Vec::get_mut",
    "Vec::last_mut",
    "Slice::get",
    "Vec::into_list",
    "Vec::into_array",
    "Array::get",
    "Array::set",
    "Array::len",
    "Array::of_list",
    "Array::to_list",
    "Bytes::of_list",
    "Bytes::to_list",
    "Bytes::len",
    "secret",
    "expose",
    "Region::new",
    "Region::place",
    "RcRegion::new",
    "RcRegion::place",
    "RcPlace::heap",
    "Bytes::get",
    "Bytes::find",
    "Bytes::slice",
    "Bytes::concat",
    "Bytes::eq",
    "Bytes::of_text",
    "Text::of_bytes",
    "Text::byte",
    "Text::slice",
    "Text::of_code_point",
    "Text::escape_debug",
    "Text::of_utf8",
    "words",
    "I64::of_i8",
    "I64::of_i16",
    "I8::of_i64",
    "I16::of_i64",
    "U64::of_u16",
    "U16::of_u64",
    "I64::of_i32",
    "I32::of_i64",
    "I64::of_u64",
    "U64::of_i64",
    "U64::of_u32",
    "U32::of_u64",
    "U64::of_u8",
    "U64::of_uhost",
    "UHost::succ_below",
    "UHost::pred_nz",
    "UHost::add_within",
    "UHost::sub",
    "UHost::of_u64_below",
    "U8::of_u64",
    "Nat::of_u64",
    "U64::of_nat",
    "U32::and",
    "U32::or",
    "U32::xor",
    "U32::shl",
    "U32::shr",
    "U32::rotl",
    "U32::rotr",
    "U64::and",
    "U64::or",
    "U64::xor",
    "U64::shl",
    "U64::shr",
    "U64::rotl",
    "U64::rotr",
    "U64::wrapping_add",
    "U64::wrapping_sub",
    "U64::wrapping_mul",
    "Ref::new",
    "Ref::get",
    "Ref::set",
    "Weak::of",
    "Weak::get",
    "Mutex::new",
    "Mutex::claim",
    "Mutex::take_claimed",
    "Mutex::put",
    "Mutex::withdraw",
    "MutexGuard::claimed",
    "MutexGuard::get",
    "MutexGuard::get_mut",
    "Atomic::new",
    "Atomic::load",
    "Atomic::store",
    "Atomic::fetch_add",
    "Pending::ready",
    "pending_spawn",
    "Pending::take",
    "Pending::is_ready",
    "Pending::signal",
    "Signal::fresh",
    "Signal::raise",
    "Signal::is_raised",
    "Signal::either",
    "Signal::listen",
    "budget_value",
    "info_more",
    "info_unbounded",
    "Os::args",
    "Os::print",
    "Os::eprint",
    "Os::read_file",
    "Os::write_file",
    "Os::read_bytes",
    "Os::write_bytes",
    "Os::read_under",
    "Os::read_bytes_under",
    "Os::create_dir",
    "Os::list_dir",
    "Os::remove",
    "Os::stat",
    "Os::read_link",
    "Os::write_new",
    "Os::move_path",
    "Os::set_mode",
    "Os::lock",
    "Os::unlock",
    "Os::copy_file",
    "Os::canonicalize",
    "Os::temp_dir",
    "Os::run",
    "Os::exit",
    "Os::stop",
    "Os::read_line",
    "Os::read_stdin",
    "Os::flush",
    "Os::on_shutdown",
    "Os::env",
    "Os::env_names",
    "Os::wall_ms",
    "Os::monotonic_ns",
    "Os::uhost_add",
    "Os::uhost_sub",
    "Os::uhost_mul",
    "Os::uhost_of_u64",
    "Os::host_bits",
    "Os::hash_seed_k0",
    "Os::hash_seed_k1",
    "Os::sleep_pending",
    "Os::tcp_ready",
    "Os::tcp_send",
    "Os::tls_ready",
    "Os::tls_send",
    "Os::offload",
    "Os::random",
    "Os::secure_random",
    "Os::status",
    "Os::entry",
    "Os::check",
    "Os::fetch",
    "Os::resolve",
    "Os::http_open",
    "Os::http_write",
    "Os::http_finish",
    "Os::http_read",
    "Os::http_close",
    "Os::child_spawn",
    "Os::child_read",
    "Os::child_write",
    "Os::child_close_stdin",
    "Os::child_wait",
    "Os::child_close",
    "Os::tcp_listen",
    "Os::tcp_accept",
    "Os::tcp_connect",
    "Os::tcp_read",
    "Os::tcp_write",
    "Os::tcp_shutdown",
    "Os::tcp_close",
    "Os::tcp_unlisten",
    "Os::tls_accept",
    "Os::tls_connect",
    "Os::tls_read",
    "Os::tls_write",
    "Os::tls_shutdown",
    "Os::tls_close",
];

#[cfg(test)]
mod ownership_tests {
    use super::*;

    fn local(id: u32, repr: Repr) -> Local {
        Local {
            id,
            name: format!("local{id}"),
            repr,
        }
    }

    fn expr(kind: ExprKind, ty: Ty) -> Expr {
        Expr {
            kind,
            ty,
            span: Span::default(),
        }
    }

    fn function_type(kind: Kind) -> Ty {
        Ty::Fn(Box::new(FnTy {
            params: vec![],
            ret: Ty::Unit,
            kind,
            tier: Tier::S,
        }))
    }

    fn caller(id: usize, repr: Repr, kind: Kind) -> FnInst {
        let callee = local(1, repr);
        FnInst {
            id,
            source: format!("caller{id}").into(),
            tier: Tier::S,
            generics: vec![],
            params: vec![Param {
                local: callee.clone(),
                ty: function_type(kind),
            }],
            ret: Ty::Unit,
            lends: None,
            fn_region: false,
            body: expr(
                ExprKind::Call(Box::new(CallNode {
                    callee: Callee::Local(callee),
                    args: vec![],
                    tier: Tier::S,
                    targs: vec![],
                    tick: Tick::None,
                    recur: false,
                    unwind: Vec::new(),
                    span: Span::default(),
                })),
                Ty::Unit,
            ),
            span: Span::default(),
        }
    }

    #[test]
    fn callee_ownership_is_local_to_each_specialized_function() {
        let pkg = Package {
            fns: vec![
                caller(0, Repr::Plain, Kind::Affine),
                caller(1, Repr::Plain, Kind::Shared),
                caller(2, Repr::FnRef, Kind::Affine),
                caller(3, Repr::Plain, Kind::Linear),
            ],
            ..Package::default()
        };
        let output = generate(&pkg).unwrap();
        for id in [0, 3] {
            assert!(output.contains(&format!(
                "const b{id} = callFunction(readLocal(1,false,false,true),[],false);"
            )));
        }
        for id in [1, 2] {
            assert!(output.contains(&format!(
                "const b{id} = callFunction(readLocal(1,false,true,false),[],false);"
            )));
        }
    }

    #[test]
    fn capture_clones_do_not_confuse_copy_values_with_owned_moves() {
        let body = expr(
            ExprKind::Block(Block {
                stmts: vec![
                    Stmt::Expr(expr(
                        ExprKind::Read {
                            local: local(1, Repr::Plain),
                            how: Use::Copy,
                        },
                        Ty::Int(Width::W64),
                    )),
                    Stmt::Expr(expr(
                        ExprKind::Read {
                            local: local(2, Repr::Plain),
                            how: Use::Clone,
                        },
                        Ty::Text,
                    )),
                ],
                tail: Some(Box::new(expr(
                    ExprKind::Read {
                        local: local(3, Repr::Plain),
                        how: Use::Move,
                    },
                    Ty::Buf,
                ))),
            }),
            Ty::Buf,
        );
        let fty = FnTy {
            params: vec![],
            ret: Ty::Buf,
            kind: Kind::Affine,
            tier: Tier::S,
        };
        let closure = expr(
            ExprKind::Closure(Box::new(ClosureNode {
                params: vec![],
                ret: Ty::Buf,
                body,
                fn_ty: fty.clone(),
                borrowed: false,
                clones: vec![local(2, Repr::Plain)],
                pure: false,
                refs: vec![],
                owned_refs: vec![],
                span: Span::default(),
            })),
            Ty::Fn(Box::new(fty)),
        );
        let param = |id, ty| Param {
            local: local(id, Repr::Plain),
            ty,
        };
        let pkg = Package {
            fns: vec![FnInst {
                id: 0,
                source: "f".into(),
                tier: Tier::S,
                generics: vec![],
                params: vec![
                    param(1, Ty::Int(Width::W64)),
                    param(2, Ty::Text),
                    param(3, Ty::Buf),
                ],
                ret: closure.ty.clone(),
                lends: None,
                fn_region: false,
                body: closure,
                span: Span::default(),
            }],
            ..Package::default()
        };
        let output = generate(&pkg).unwrap();
        let output = output
            .lines()
            .find(|line| line.starts_with("const b0 = "))
            .unwrap();
        assert!(
            output.ends_with(",[],[1,2,3],false,[],false,[],[3],true,[]);"),
            "{output}"
        );
    }
}

#[cfg(test)]
mod export_tests {
    use super::*;

    fn exported(row: Vec<String>) -> (Package, Options) {
        let name = "ready_wait";
        let function = FnInst {
            id: 0,
            source: name.into(),
            tier: Tier::O,
            generics: Vec::new(),
            params: Vec::new(),
            ret: Ty::Unit,
            lends: None,
            fn_region: false,
            body: Expr {
                kind: ExprKind::Unit,
                ty: Ty::Unit,
                span: Span::default(),
            },
            span: Span::default(),
        };
        let pkg = Package {
            fns: vec![function],
            exports: vec![Export {
                inst: 0,
                name: name.into(),
                foreign_row: row
                    .iter()
                    .filter(|e| !matches!(e.as_str(), "show" | "div" | "wait" | "spawn"))
                    .cloned()
                    .collect(),
                row,
                pure_borrow_callbacks: Vec::new(),
            }],
            ..Package::default()
        };
        let options = Options {
            exports: vec![name.into()],
            ..Options::default()
        };
        (pkg, options)
    }

    #[test]
    fn a_wait_export_has_an_async_boundary_and_declaration() {
        tauto_messages::install();
        let (pkg, options) = exported(vec!["wait".into()]);
        assert!(!export_table(&pkg, &options).unwrap()[0].sync);
        let declaration = crate::generate_declarations_with(&pkg, &options).unwrap();
        assert!(
            declaration.contains("\"ready_wait\": () => Promise<null>"),
            "{declaration}"
        );
        assert!(generate_with(&pkg, &options).is_ok());
    }

    #[test]
    fn a_source_effect_named_wait_is_not_the_standard_wait() {
        tauto_messages::install();
        let (pkg, options) = exported(vec!["custom::wait".into()]);
        let error = export_table(&pkg, &options)
            .err()
            .expect("source effect is unhandled");
        assert!(error.contains("custom::wait"), "{error}");
    }
}
