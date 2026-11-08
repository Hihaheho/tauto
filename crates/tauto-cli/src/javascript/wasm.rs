//! Typed, checked byte/handle ABI for Rust externs compiled to wasm32.
use super::quote;
use super::specialize::substitute;
use std::{collections::BTreeMap, path::Path, process::Command};
use tauto_nir::{Indirect, Package, Pass, Tier, Ty};
use tauto_rustgen::{Bindings, Sources};

pub fn build(
    pkg: &Package,
    m: &tauto::manifest::Manifest,
    dir: &Path,
    origins: &BTreeMap<tauto_nir::Name, tauto_nir::Name>,
    timings: &mut crate::timings::Timings,
) -> Result<(), String> {
    // The engine suspends the Wasm stack. Rust callback signatures stay ordinary
    // synchronous functions, independently of the callback's Nib effect tier.
    let mut concrete = pkg.clone();
    for x in &mut concrete.externs {
        for (_, ty, _) in &mut x.params {
            native_type(ty);
        }
        native_type(&mut x.ret);
    }
    for data in &mut concrete.datas {
        for ctor in &mut data.ctors {
            for field in &mut ctor.fields {
                native_type(&mut field.ty);
            }
        }
    }
    let pkg = &concrete;
    let bridge = m
        .rust
        .bridge
        .as_ref()
        .map(|_| tauto_rustgen::bridge_ident(&m.package.name));
    let mut original = pkg.clone();
    for x in &mut original.externs {
        if let Some(name) = origins.get(&x.name) {
            x.name = name.clone();
        }
    }
    let mut bindings = Bindings::resolve(&original, Some(m), bridge.as_deref())?;
    for (alias, source) in origins {
        if let Some(binding) = bindings.externs.get(source).cloned() {
            bindings.externs.insert(alias.clone(), binding);
        }
    }
    let mut g = Codec {
        pkg,
        bindings: &bindings,
        ids: BTreeMap::new(),
        code: String::new(),
        access: String::new(),
    };
    let mut dispatch = String::from("fn dispatch(index:u32,args:&Value)->Value {match index {\n");
    let mut host = String::new();
    for (index, x) in pkg.externs.iter().enumerate() {
        let mut body =
            String::from("let frame=Frame::default();let mut roots=Vec::<Value>::new();\n");
        let mut args = Vec::new();
        for (i, (_, t, pass)) in x.params.iter().enumerate() {
            if let Ty::Fn(_) = t {
                let id = g.codec(t)?;
                body.push_str(&format!("let a{i}=from{id}(&args[{i}],&frame);\n"));
                args.push(format!("a{i}"));
            } else if *pass == Pass::Value {
                let id = g.codec(t)?;
                body.push_str(&format!("let a{i}=from{id}(&args[{i}],&frame);\n"));
                args.push(format!("a{i}"));
            } else {
                let actual = if let Ty::Slice(a) = t {
                    Ty::Vec(a.clone())
                } else {
                    t.clone()
                };
                let id = g.codec(&actual)?;
                if g.has_view(t) && g.opaque(t) {
                    body.push_str(&format!("let v{i}=args[{i}].clone();assert!(v{i}[\"handle\"].is_number(),\"view handle required\");\n"));
                } else {
                    body.push_str(&format!("let v{i}=if args[{i}][\"handle\"].is_number(){{args[{i}].clone()}}else{{let v=store(from{id}(&args[{i}],&frame),\"argument\");roots.push(json!({{\"index\":{i},\"codec\":{id},\"value\":v.clone()}}));v}};\n"));
                }
                let method = if *pass == Pass::RefMut {
                    "write"
                } else {
                    "read"
                };
                if let Ty::Slice(a) = t {
                    let ty = g.ty(a);
                    body.push_str(&format!(
                        "let a{i}=frame.{}::<{ty}>(&v{i});\n",
                        if *pass == Pass::RefMut {
                            "slice_mut"
                        } else {
                            "slice"
                        }
                    ));
                } else {
                    let ty = g.static_ty(t);
                    body.push_str(&format!("let a{i}=frame.{method}::<{ty}>(&v{i});\n"));
                }
                args.push(format!("a{i}"));
            }
        }
        let ret = g.codec(&x.ret)?;
        let binding = &bindings.externs[&x.name];
        let mut native_args = Vec::new();
        let marks = binding.marks.split_whitespace().collect::<Vec<_>>();
        for (i, (_, t, pass)) in x.params.iter().enumerate() {
            let arg = if let Ty::Fn(f) = t {
                let params = (0..f.params.len())
                    .map(|j| format!("p{j}"))
                    .collect::<Vec<_>>()
                    .join(",");
                let sep = if params.is_empty() { "" } else { "," };
                if *pass == Pass::Value {
                    format!("move |{params}| a{i}(&Ev::empty(){sep}{params})")
                } else {
                    format!("&mut |{params}| a{i}(&Ev::empty(){sep}{params})")
                }
            } else if *pass == Pass::Ref && *t == Ty::Text {
                format!("&**a{i}")
            } else if marks.contains(&format!("p{i}").as_str()) {
                format!("usize::try_from(a{i}).expect(\"integer out of range\")")
            } else if marks.contains(&format!("q{i}").as_str()) {
                format!("isize::try_from(a{i}).expect(\"integer out of range\")")
            } else {
                args[i].clone()
            };
            native_args.push(arg);
        }
        let call = format!("{}({})", binding.rust, native_args.join(","));
        let call = match &x.ret {
            Ty::Text => format!("Text::from({call})"),
            Ty::Fn(f) => {
                let params = (0..f.params.len())
                    .map(|j| format!("p{j}:{}", g.ty(&f.params[j])))
                    .collect::<Vec<_>>()
                    .join(",");
                let values = (0..f.params.len())
                    .map(|j| format!("p{j}"))
                    .collect::<Vec<_>>()
                    .join(",");
                let sep = if params.is_empty() { "" } else { "," };
                format!(
                    "{{let f={call};{}(move |_ev:&Ev<'_>{sep}{params}| f({values})) as {}}}",
                    if f.kind.dup() { "Rc::new" } else { "Box::new" },
                    g.ty(&x.ret)
                )
            }
            _ if marks.contains(&"r") => format!("({call}) as u64"),
            _ if marks.contains(&"s") => format!("({call}) as i64"),
            _ if marks.contains(&"o") => format!("({call}).map(|v|v as u64)"),
            _ if marks.contains(&"t") => format!("({call}).map(|v|v as i64)"),
            _ => call,
        };
        body.push_str(&format!("let result={call};let value=to{ret}(result,&frame);json!({{\"value\":value,\"roots\":roots}})"));
        dispatch.push_str(&format!("{index}=>{{{body}}},\n"));
        let owned = x
            .params
            .iter()
            .enumerate()
            .filter_map(|(i, (_, _, p))| (*p == Pass::Value).then_some(i))
            .collect::<Vec<_>>();
        host.push_str(&format!(
            "externs[{}]=native(args=>call({index},args,{}));\n",
            quote(&x.name),
            serde_json::to_string(&owned).unwrap()
        ));
    }
    dispatch.push_str("_=>panic!(\"unknown wasm extern\")}}\n");
    let opts = tauto_rustgen::Options::from_manifest(m);
    let mut definitions = pkg.clone();
    definitions.externs.clear();
    let mut ws = tauto_rustgen::workspace(
        "tauto-wasm-externs",
        &definitions,
        &Sources {
            file: "externs",
            text: "",
        },
        &bindings,
        &opts,
    );
    ws.files.retain(|(n, _)| n != "src/main.rs");
    for (n, s) in &mut ws.files {
        if n == "Cargo.toml" {
            *s = s
                .replace(
                    "[dependencies]",
                    "[lib]\ncrate-type = [\"cdylib\"]\n\n[dependencies]\nserde_json = \"=1.0.151\"",
                )
                .replace("panic = \"unwind\"", "panic = \"abort\"")
                // The page downloads this file: the function names are for a
                // debugger only, and one codegen unit lets LTO drop more.
                .replace(
                    "lto = \"thin\"",
                    "lto = \"fat\"\ncodegen-units = 1\nstrip = true",
                );
        }
        if n == "src/lib.rs" {
            s.push_str(include_str!("wasm_runtime.rs"));
            s.push_str(&g.code);
            s.push_str(&dispatch);
            s.push_str(&format!("fn access_value(codec:u32,action:u32,args:&Value)->Value{{let frame=Frame::default();match codec{{{} _=>panic!(\"unknown wasm codec\")}}}}", g.access));
        }
    }
    let root = dir.join("wasm-build");
    let stats = ws.write_with_stats(&root).map_err(|e| e.to_string())?;
    timings.written(stats);
    timings.phase("native_compile");
    let output = Command::new("cargo")
        .args([
            "build",
            "--release",
            "--target",
            "wasm32-unknown-unknown",
            "--manifest-path",
        ])
        .arg(root.join("Cargo.toml"))
        .env(
            "CARGO_TARGET_DIR",
            root.join("target")
                .canonicalize()
                .unwrap_or_else(|_| std::env::current_dir().unwrap().join(&root).join("target")),
        )
        .output()
        .map_err(|e| crate::i18n::t!("js-wasm-build-failed", e = e.to_string()))?;
    if !output.status.success() {
        return Err(crate::i18n::t!(
            "js-wasm-build-errors",
            target = "wasm32-unknown-unknown",
            stderr = String::from_utf8_lossy(&output.stderr).into_owned()
        ));
    }
    timings.phase("codegen_write");
    std::fs::copy(
        root.join("target/wasm32-unknown-unknown/release/tauto_wasm_externs.wasm"),
        dir.join("externs.wasm"),
    )
    .map_err(|e| e.to_string())?;
    std::fs::write(
        dir.join("wasm.mjs"),
        include_str!("wasm_host.js").replace("// BINDINGS", &host),
    )
    .map_err(|e| e.to_string())?;
    Ok(())
}
fn ident(n: &str) -> String {
    tauto_rustgen::field_name(n)
}
struct Codec<'a> {
    pkg: &'a Package,
    bindings: &'a Bindings,
    ids: BTreeMap<Ty, usize>,
    code: String,
    access: String,
}
impl Codec<'_> {
    fn ty(&self, t: &Ty) -> String {
        tauto_rustgen::type_name(self.pkg, self.bindings, t)
    }
    fn static_ty(&self, t: &Ty) -> String {
        if matches!(t, Ty::Fn(_)) {
            return self.ty(t);
        }
        tauto_rustgen::type_name_with_lifetime(self.pkg, self.bindings, t, "'static")
    }
    fn borrowed_ty(&self, t: &Ty) -> String {
        if matches!(t, Ty::Fn(_)) {
            return self.ty(t);
        }
        tauto_rustgen::type_name_with_lifetime(self.pkg, self.bindings, t, "'a")
    }
    fn opaque(&self, t: &Ty) -> bool {
        matches!(t,Ty::Data(n,_) if self.bindings.types.contains_key(n))
    }
    fn codec(&mut self, t: &Ty) -> Result<usize, String> {
        if let Some(i) = self.ids.get(t) {
            return Ok(*i);
        }
        let id = self.ids.len();
        self.ids.insert(t.clone(), id);
        let ty = self.borrowed_ty(t);
        let (from, to) = match t {
            Ty::Int(_) => (
                format!(
                    "v[\"$int\"].as_str().expect(\"integer required\").parse::<{ty}>().expect(\"integer out of range\")"
                ),
                "json!({\"$int\":x.to_string()})".into(),
            ),
            Ty::Bool => (
                "v.as_bool().expect(\"boolean required\")".into(),
                "json!(x)".into(),
            ),
            Ty::Text => (
                "Text::from(v.as_str().expect(\"text required\"))".into(),
                "json!(x.as_ref())".into(),
            ),
            Ty::Buf => (
                "v[\"text\"].as_str().expect(\"Buf required\").to_owned()".into(),
                "json!({\"kind\":\"Buf\",\"text\":x})".into(),
            ),
            Ty::Unit => ("{assert!(v.is_null());()}".into(), "Value::Null".into()),
            Ty::Vec(a) => {
                let a = self.codec(a)?;
                (
                    format!(
                        "v[\"items\"].as_array().expect(\"Vec required\").iter().map(|v|from{a}(v,frame)).collect()"
                    ),
                    format!(
                        "json!({{\"kind\":\"Vec\",\"items\":x.into_iter().map(|x|to{a}(x,frame)).collect::<Vec<_>>()}})"
                    ),
                )
            }
            Ty::Option(a) => {
                let a = self.codec(a)?;
                (
                    format!(
                        "match v[\"tag\"].as_str(){{Some(\"None\")=>None,Some(\"Some\")=>Some(from{a}(&v[\"fields\"][0],frame)),_=>panic!(\"Option required\")}}"
                    ),
                    format!(
                        "match x{{None=>ctor(\"Option\",\"None\",json!([]),json!([]),false),Some(a)=>ctor(\"Option\",\"Some\",json!([null]),json!([to{a}(a,frame)]),false)}}"
                    ),
                )
            }
            Ty::Result(a, b) => {
                let a = self.codec(a)?;
                let b = self.codec(b)?;
                (
                    format!(
                        "match v[\"tag\"].as_str(){{Some(\"Ok\")=>Ok(from{a}(&v[\"fields\"][0],frame)),Some(\"Err\")=>Err(from{b}(&v[\"fields\"][0],frame)),_=>panic!(\"Result required\")}}"
                    ),
                    format!(
                        "match x{{Ok(a)=>ctor(\"Result\",\"Ok\",json!([null]),json!([to{a}(a,frame)]),false),Err(b)=>ctor(\"Result\",\"Err\",json!([null]),json!([to{b}(b,frame)]),false)}}"
                    ),
                )
            }
            Ty::Pair(a, b) => {
                let a = self.codec(a)?;
                let b = self.codec(b)?;
                (
                    format!("(from{a}(&v[\"fields\"][0],frame),from{b}(&v[\"fields\"][1],frame))"),
                    format!(
                        "ctor(\"Pair\",\"Pair\",json!([\"fst\",\"snd\"]),json!([to{a}(x.0,frame),to{b}(x.1,frame)]),true)"
                    ),
                )
            }
            Ty::Ref(a) | Ty::RefMut(a) => {
                let sub = self.codec(a)?;
                let mutable = matches!(t, Ty::RefMut(_));
                let pointee = self.static_ty(a);
                let method = if mutable { "write" } else { "read" };
                let from = if let Ty::Slice(element) = a.as_ref() {
                    format!(
                        "frame.{}::<{}>(v)",
                        if mutable { "slice_mut" } else { "slice" },
                        self.static_ty(element)
                    )
                } else {
                    format!("frame.{method}::<{pointee}>(v)")
                };
                (
                    from,
                    format!(
                        "unsafe{{view(x as *{} {pointee} as *mut {pointee},{mutable},{sub},{},frame)}}",
                        if mutable { "mut" } else { "const" },
                        self.opaque(a)
                    ),
                )
            }
            Ty::Slice(a) => {
                let _ = self.codec(a)?;
                // A slice occurs only behind a reference; its owned wire shape is Vec.
                (
                    "panic!(\"a slice must be borrowed\")".into(),
                    "panic!(\"a slice must be borrowed\")".into(),
                )
            }
            Ty::Fn(f) => {
                if f.tier != Tier::S {
                    return Err(crate::i18n::t!("js-wasm-callback-direct"));
                }
                let ret = self.codec(&f.ret)?;
                let mut params = Vec::new();
                let mut values = Vec::new();
                let mut invoke = Vec::new();
                for (i, t) in f.params.iter().enumerate() {
                    let sub = self.codec(t)?;
                    params.push(format!("a{i}:{}", self.ty(t)));
                    values.push(format!("to{sub}(a{i},&frame)"));
                    invoke.push(format!("from{sub}(&args[\"args\"][{i}],&frame)"));
                }
                let wrapper = if f.kind.dup() { "Rc::new" } else { "Box::new" };
                let sep = if params.is_empty() { "" } else { "," };
                let from = format!(
                    "{{if v[\"handle\"].is_number(){{return {}::<{}>(v,frame);}}let token=Callback(v[\"callback\"].as_u64().expect(\"callback required\") as u32);{wrapper}(move |_ev:&Ev<'_>{sep}{}|{{let frame=Frame::scoped();let result=token.call(json!([{}]));from{ret}(&result,&frame)}})}}",
                    if f.kind.dup() { "shared" } else { "take" },
                    self.static_ty(t),
                    params.join(","),
                    values.join(",")
                );
                let to = format!(
                    "{{let mut v=store(x,\"function\");v[\"kind\"]=json!(\"Function\");v[\"codec\"]=json!({id});v}}"
                );
                let fty = self.static_ty(t);
                let get = if f.kind.dup() { "shared" } else { "take" };
                self.access.push_str(&format!("{id}=>{{assert_eq!(action,3,\"invalid function operation\");let f={get}::<{fty}>(&args[\"value\"],&frame);let result=f(&Ev::empty(){}{});to{ret}(result,&frame)}},",if invoke.is_empty(){""}else{","},invoke.join(",")));
                (from, to)
            }
            Ty::Data(n, _) if self.opaque(t) => {
                let clone = self
                    .pkg
                    .datas
                    .iter()
                    .find(|d| d.name == *n)
                    .is_some_and(|d| d.clone);
                if self.pkg.datas.iter().any(|d| d.name == *n && d.view) {
                    let static_ty = self.static_ty(t);
                    (
                        format!(
                            "unsafe{{std::mem::transmute::<{static_ty},{ty}>(take::<{static_ty}>(v,frame))}}"
                        ),
                        format!(
                            "{{let value: {static_ty}=unsafe{{std::mem::transmute(x)}};let id=insert(Box::new(value),frame.loans.borrow().clone(),true);json!({{\"kind\":\"Opaque\",\"handle\":id,\"name\":{},\"resource\":true}})}}",
                            quote(n)
                        ),
                    )
                } else {
                    (
                        format!("take::<{ty}>(v,frame)"),
                        format!(
                            "{{let mut value=store(x,{});value[\"codec\"]=json!({id});value[\"clone\"]=json!({clone});value}}",
                            quote(n)
                        ),
                    )
                }
            }
            Ty::Data(n, args) => {
                let d = self
                    .pkg
                    .datas
                    .iter()
                    .find(|d| d.name == *n)
                    .cloned()
                    .ok_or_else(|| crate::i18n::t!("js-wasm-unknown-data", name = n.to_string()))?;
                if d.view {
                    return Err(crate::i18n::t!(
                        "js-wasm-borrowed-view",
                        name = n.to_string()
                    ));
                }
                let subst = d
                    .generics
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect::<BTreeMap<_, _>>();
                let mut from =
                    String::from("match v[\"tag\"].as_str().expect(\"constructor required\"){ ");
                let mut to = String::from("match x {");
                let base = self.ty(&Ty::Data(n.clone(), vec![]));
                for c in &d.ctors {
                    let path = if d.is_struct {
                        base.clone()
                    } else {
                        format!("{base}::{}", ident(&c.name))
                    };
                    let named = c.fields.iter().any(|f| f.name.is_some());
                    let mut fs = Vec::new();
                    let mut pats = Vec::new();
                    let mut outs = Vec::new();
                    let mut names = Vec::new();
                    for (i, f) in c.fields.iter().enumerate() {
                        let ft = substitute(&f.ty, &subst);
                        let sub = self.codec(&ft)?;
                        let value = format!("from{sub}(&v[\"fields\"][{i}],frame)");
                        let value = match f.indirect {
                            Indirect::None => value,
                            Indirect::Unique => format!("Box::new({value})"),
                            Indirect::Shared => format!("Rc::new({value})"),
                        };
                        fs.push(if named {
                            format!("{}:{value}", ident(f.name.as_deref().unwrap()))
                        } else {
                            value
                        });
                        pats.push(if named {
                            format!("{}:f{i}", ident(f.name.as_deref().unwrap()))
                        } else {
                            format!("f{i}")
                        });
                        let value = match f.indirect {
                            Indirect::None => format!("f{i}"),
                            Indirect::Unique => format!("*f{i}"),
                            Indirect::Shared => {
                                format!("Rc::try_unwrap(f{i}).unwrap_or_else(|v|(*v).clone())")
                            }
                        };
                        outs.push(format!("to{sub}({value},frame)"));
                        names.push(f.name.clone());
                    }
                    if d.linear {
                        fs.push(if named {
                            format!("bomb:tauto_rt::Bomb::new({})", quote(n))
                        } else {
                            format!("tauto_rt::Bomb::new({})", quote(n))
                        });
                        pats.push("bomb".into());
                    }
                    let wrap = |s: Vec<String>| {
                        if named {
                            format!("{{{}}}", s.join(","))
                        } else if s.is_empty() && !d.is_struct {
                            String::new()
                        } else {
                            format!("({})", s.join(","))
                        }
                    };
                    from.push_str(&format!(
                        "{}=>{path}{},",
                        quote(tauto_jsgen::constructor_symbol(self.pkg, &c.name)),
                        wrap(fs)
                    ));
                    to.push_str(&format!(
                        "{path}{}=>{{{}ctor({},{},json!({}),json!([{}]),{})}},",
                        wrap(pats),
                        if d.linear { "bomb.defuse();" } else { "" },
                        quote(&tauto_jsgen::owner_symbol(self.pkg, n)),
                        quote(tauto_jsgen::constructor_symbol(self.pkg, &c.name)),
                        serde_json::to_string(&names).unwrap(),
                        outs.join(","),
                        d.is_struct
                    ));
                }
                from.push_str("_=>panic!(\"wrong constructor\")}");
                to.push('}');
                (from, to)
            }
            _ => {
                return Err(crate::i18n::t!("js-wasm-type-abi", ty = format!("{t:?}")));
            }
        };
        let owner = match t {
            Ty::Option(_) => Some("Option".to_string()),
            Ty::Result(_, _) => Some("Result".to_string()),
            Ty::Pair(_, _) => Some("Pair".to_string()),
            Ty::Data(n, _) if !self.opaque(t) => Some(tauto_jsgen::owner_symbol(self.pkg, n)),
            _ => None,
        };
        let from = match owner {
            Some(owner) => format!(
                "assert_eq!(v[\"owner\"].as_str(),Some({}),\"wrong or missing constructor owner\");{from}",
                quote(&owner)
            ),
            None => from,
        };
        if !matches!(t, Ty::Slice(_)) {
            self.code.push_str(&format!("fn from{id}<'a>(v:&Value,frame:&'a Frame)->{ty}{{{from}}}\nfn to{id}<'a>(x:{ty},frame:&Frame)->Value{{{to}}}\n"));
        }
        self.peek(t, id)?;
        Ok(id)
    }
    fn peek(&mut self, t: &Ty, id: usize) -> Result<(), String> {
        let ty = self.borrowed_ty(t);
        let static_ty = self.static_ty(t);
        let body = match t {
            Ty::Int(_) => "json!({\"$int\":x.to_string()})".into(),
            Ty::Bool => "json!(x)".into(),
            Ty::Unit => "Value::Null".into(),
            Ty::Text => "json!(x.as_ref())".into(),
            Ty::Buf => "json!({\"kind\":\"Buf\",\"text\":x})".into(),
            Ty::Vec(a) | Ty::Slice(a) => {
                let sub = self.codec(a)?;
                format!(
                    "json!({{\"kind\":\"Vec\",\"items\":x.iter().map(|a|peek{sub}(a,frame)).collect::<Vec<_>>()}})"
                )
            }
            Ty::Option(a) => {
                let sub = self.codec(a)?;
                format!(
                    "match x{{None=>ctor(\"Option\",\"None\",json!([]),json!([]),false),Some(a)=>ctor(\"Option\",\"Some\",json!([null]),json!([peek{sub}(a,frame)]),false)}}"
                )
            }
            Ty::Result(a, b) => {
                let a = self.codec(a)?;
                let b = self.codec(b)?;
                format!(
                    "match x{{Ok(a)=>ctor(\"Result\",\"Ok\",json!([null]),json!([peek{a}(a,frame)]),false),Err(b)=>ctor(\"Result\",\"Err\",json!([null]),json!([peek{b}(b,frame)]),false)}}"
                )
            }
            Ty::Pair(a, b) => {
                let a = self.codec(a)?;
                let b = self.codec(b)?;
                format!(
                    "ctor(\"Pair\",\"Pair\",json!([\"fst\",\"snd\"]),json!([peek{a}(&x.0,frame),peek{b}(&x.1,frame)]),true)"
                )
            }
            Ty::Data(_, _) if self.opaque(t) => format!(
                "unsafe{{view(x as *const {ty} as *mut {static_ty},false,{id},true,frame)}}"
            ),
            Ty::Data(n, args) => {
                let d = self
                    .pkg
                    .datas
                    .iter()
                    .find(|d| d.name == *n)
                    .unwrap()
                    .clone();
                let subst = d
                    .generics
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect();
                let base = self.ty(&Ty::Data(n.clone(), vec![]));
                let mut code = String::from("match x{");
                for c in &d.ctors {
                    let path = if d.is_struct {
                        base.clone()
                    } else {
                        format!("{base}::{}", ident(&c.name))
                    };
                    let named = c.fields.iter().any(|f| f.name.is_some());
                    let mut pats = Vec::new();
                    let mut fields = Vec::new();
                    for (i, f) in c.fields.iter().enumerate() {
                        let sub = self.codec(&substitute(&f.ty, &subst))?;
                        pats.push(if named {
                            format!("{}:f{i}", ident(f.name.as_deref().unwrap()))
                        } else {
                            format!("f{i}")
                        });
                        fields.push(format!("peek{sub}(f{i},frame)"));
                    }
                    if d.linear {
                        pats.push(if named { "bomb:_".into() } else { "_".into() });
                    }
                    let pat = if named {
                        format!("{{{}}}", pats.join(","))
                    } else if pats.is_empty() && !d.is_struct {
                        String::new()
                    } else {
                        format!("({})", pats.join(","))
                    };
                    code.push_str(&format!(
                        "{path}{pat}=>ctor({},{},json!({}),json!([{}]),{}),",
                        quote(&tauto_jsgen::owner_symbol(self.pkg, n)),
                        quote(tauto_jsgen::constructor_symbol(self.pkg, &c.name)),
                        serde_json::to_string(
                            &c.fields.iter().map(|f| &f.name).collect::<Vec<_>>()
                        )
                        .unwrap(),
                        fields.join(","),
                        d.is_struct
                    ));
                }
                code.push('}');
                code
            }
            Ty::Fn(_) => return Ok(()),
            Ty::Ref(a) | Ty::RefMut(a) => {
                let sub = self.codec(a)?;
                format!(
                    "unsafe{{view(&**x as *const {} as *mut {},false,{sub},{},frame)}}",
                    self.ty(a),
                    self.static_ty(a),
                    self.opaque(a)
                )
            }
            _ => {
                return Err(crate::i18n::t!(
                    "js-wasm-no-borrowed",
                    ty = format!("{t:?}")
                ));
            }
        };
        self.code.push_str(&format!(
            "fn peek{id}<'a>(x:&{ty},frame:&Frame)->Value{{{body}}}\n"
        ));
        let operations = self.operations(t, id)?;
        if let Ty::Slice(a) = t {
            let element = self.static_ty(a);
            let vec = self.codec(&Ty::Vec(a.clone()))?;
            self.access.push_str(&format!("{id}=>match action{{{operations}0=>peek{id}(frame.slice::<{element}>(&args[\"value\"]),&frame),1=>{{let replacement=from{vec}(&args[\"replacement\"],&frame);let target=frame.slice_mut::<{element}>(&args[\"value\"]);assert_eq!(target.len(),replacement.len(),\"cannot resize a borrowed slice\");for(a,b)in target.iter_mut().zip(replacement){{*a=b;}}Value::Null}},_=>panic!(\"invalid slice operation\")}},"));
        } else if !matches!(t, Ty::Ref(_) | Ty::RefMut(_)) && !self.has_view(t) {
            let projections = self.projections(t)?;
            self.access.push_str(&format!("{id}=>match action{{{operations}{projections}0=>peek{id}(frame.read::<{static_ty}>(&args[\"value\"]),&frame),1=>{{*frame.write::<{static_ty}>(&args[\"value\"])=from{id}(&args[\"replacement\"],&frame);Value::Null}},2=>to{id}(take::<{static_ty}>(&args[\"value\"],&frame),&frame),_=>panic!(\"invalid value operation\")}},"));
        }
        Ok(())
    }
    fn cloneable(&self, t: &Ty) -> bool {
        match t {
            Ty::Int(_) | Ty::Bool | Ty::Unit | Ty::Text | Ty::Buf => true,
            Ty::Data(n, _) => self
                .pkg
                .datas
                .iter()
                .any(|d| d.name == *n && d.clone && !d.view),
            Ty::Vec(a) | Ty::Option(a) => self.cloneable(a),
            Ty::Pair(a, b) | Ty::Result(a, b) => self.cloneable(a) && self.cloneable(b),
            Ty::Fn(f) => f.kind.dup(),
            _ => false,
        }
    }
    fn operations(&mut self, t: &Ty, id: usize) -> Result<String, String> {
        let mut arms = Vec::new();
        if let Ty::Vec(a) | Ty::Slice(a) = t {
            let elem = self.static_ty(a);
            let sub = self.codec(a)?;
            let opaque = self.opaque(a);
            let read = if matches!(t, Ty::Slice(_)) {
                format!("frame.slice::<{elem}>(&args[\"value\"])")
            } else {
                format!("frame.read::<Vec<{elem}>>(&args[\"value\"])")
            };
            let write = if matches!(t, Ty::Slice(_)) {
                format!("frame.slice_mut::<{elem}>(&args[\"value\"])")
            } else {
                format!("frame.write::<Vec<{elem}>>(&args[\"value\"])")
            };
            let index = "args[\"args\"][0][\"$int\"].as_str().unwrap().parse::<usize>().expect(\"index too large\")";
            arms.push(format!(
                "\"Vec::len\"|\"Slice::len\"=>json!({{\"$int\":{read}.len().to_string()}})"
            ));
            arms.push(format!("\"Vec::get\"|\"Slice::get\"|\"Vec::index\"=>{{let value={read};match value.get({index}){{Some(item)=>{{let view=unsafe{{view(item as *const {elem} as *mut {elem},false,{sub},{opaque},&frame)}};if name==\"Vec::index\"{{view}}else{{ctor(\"Option\",\"Some\",json!([null]),json!([view]),false)}}}},None=>if name==\"Vec::index\"{{json!({{\"abiEffect\":\"out_of_bounds\"}})}}else{{ctor(\"Option\",\"None\",json!([]),json!([]),false)}}}}}}"));
            arms.push(format!("\"Vec::get_mut\"|\"Vec::last_mut\"=>{{let value={write};let index=if name==\"Vec::last_mut\"{{value.len().checked_sub(1)}}else{{Some({index})}};match index.and_then(|i|value.get_mut(i)){{Some(item)=>ctor(\"Option\",\"Some\",json!([null]),json!([unsafe{{view(item as *mut {elem},true,{sub},{opaque},&frame)}}]),false),None=>ctor(\"Option\",\"None\",json!([]),json!([]),false)}}}}"));
            if matches!(t, Ty::Vec(_)) {
                let slice = self.codec(&Ty::Slice(a.clone()))?;
                arms.push(format!("\"Vec::as_slice\"=>unsafe{{view({read}.as_slice() as *const [{elem}] as *mut [{elem}],false,{slice},false,&frame)}}"));
                arms.push(format!("\"Vec::as_mut_slice\"=>unsafe{{view({write}.as_mut_slice() as *mut [{elem}],true,{slice},false,&frame)}}"));
                arms.push(format!("\"Vec::push\"=>{{let item=from{sub}(&args[\"args\"][0],&frame);{write}.push(item);Value::Null}}"));
                arms.push(format!("\"Vec::pop\"=>match {write}.pop(){{Some(item)=>ctor(\"Option\",\"Some\",json!([null]),json!([to{sub}(item,&frame)]),false),None=>ctor(\"Option\",\"None\",json!([]),json!([]),false)}}"));
                arms.push(format!("\"Vec::clear\"=>{{{write}.clear();Value::Null}}"));
                arms.push(format!(
                    "\"Vec::truncate\"=>{{{write}.truncate({index});Value::Null}}"
                ));
                arms.push(format!("\"Vec::swap\"=>{{let a={index};let b=args[\"args\"][1][\"$int\"].as_str().unwrap().parse::<usize>().unwrap();let value={write};if a>=value.len()||b>=value.len(){{json!({{\"abiEffect\":\"out_of_bounds\"}})}}else{{value.swap(a,b);Value::Null}}}}"));
            }
        }
        if *t == Ty::Buf {
            arms.push("\"Buf::push\"=>{frame.write::<String>(&args[\"value\"]).push_str(args[\"args\"][0].as_str().unwrap());Value::Null}".into());
        }
        let ty = self.static_ty(t);
        let mut out = if self.cloneable(t) {
            format!("7=>to{id}(frame.read::<{ty}>(&args[\"value\"]).clone(),&frame),")
        } else {
            String::new()
        };
        if !matches!(t, Ty::Slice(_)) && !self.has_view(t) {
            out.push_str(&format!("6=>{{let replacement=from{id}(&args[\"replacement\"],&frame);let old=std::mem::replace(frame.write::<{ty}>(&args[\"value\"]),replacement);to{id}(old,&frame)}},"));
        }
        if !arms.is_empty() {
            out.push_str(&format!("10=>{{let name=args[\"operation\"].as_str().unwrap();match name{{{},_=>panic!(\"invalid wasm operation\")}}}},",arms.join(",")));
        }
        Ok(out)
    }
    fn projections(&mut self, t: &Ty) -> Result<String, String> {
        let fields = match t {
            Ty::Pair(a, b) => vec![
                (
                    "fst".to_string(),
                    "0".to_string(),
                    (**a).clone(),
                    Indirect::None,
                ),
                (
                    "snd".to_string(),
                    "1".to_string(),
                    (**b).clone(),
                    Indirect::None,
                ),
            ],
            Ty::Data(n, args) if !self.opaque(t) => {
                let d = self
                    .pkg
                    .datas
                    .iter()
                    .find(|d| d.name == *n)
                    .unwrap()
                    .clone();
                if !d.is_struct {
                    return Ok(String::new());
                }
                let subst = d
                    .generics
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect();
                d.ctors[0]
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| {
                        (
                            f.name.clone().unwrap_or_else(|| i.to_string()),
                            f.name
                                .as_deref()
                                .map(ident)
                                .unwrap_or_else(|| i.to_string()),
                            substitute(&f.ty, &subst),
                            f.indirect,
                        )
                    })
                    .collect()
            }
            _ => return Ok(String::new()),
        };
        let ty = self.static_ty(t);
        let mut arms = String::new();
        for (i, (name, field, t, indirect)) in fields.into_iter().enumerate() {
            let codec = self.codec(&t)?;
            let field_ty = self.static_ty(&t);
            let read = match indirect {
                Indirect::None => format!("&x.{field}"),
                _ => format!("&*x.{field}"),
            };
            let write = match indirect {
                Indirect::None => format!("&mut x.{field}"),
                Indirect::Unique => format!("&mut *x.{field}"),
                Indirect::Shared => format!("Rc::make_mut(&mut x.{field})"),
            };
            arms.push_str(&format!("key if key=={}||key=={i:?}.to_string()=>{{if action==4{{let x=frame.read::<{ty}>(&args[\"value\"]);unsafe{{view({read} as *const {field_ty} as *mut {field_ty},false,{codec},{},&frame)}}}}else{{let x=frame.write::<{ty}>(&args[\"value\"]);unsafe{{view({write} as *mut {field_ty},true,{codec},{},&frame)}}}}}},",quote(&name),self.opaque(&t),self.opaque(&t)));
        }
        Ok(format!(
            "4|5=>{{let key=args[\"field\"].as_str().map(str::to_owned).unwrap_or_else(||args[\"field\"].to_string());match key.as_str(){{{arms}_=>panic!(\"unknown wasm field\")}}}},"
        ))
    }
    fn has_view(&self, t: &Ty) -> bool {
        match t {
            Ty::Ref(_) | Ty::RefMut(_) => true,
            Ty::Data(n, _) => self.pkg.datas.iter().any(|d| d.name == *n && d.view),
            Ty::Option(a) => self.has_view(a),
            Ty::Result(a, b) | Ty::Pair(a, b) => self.has_view(a) || self.has_view(b),
            _ => false,
        }
    }
}

fn native_type(t: &mut Ty) {
    match t {
        Ty::Fn(f) => {
            f.tier = Tier::S;
            for p in &mut f.params {
                native_type(p);
            }
            native_type(&mut f.ret);
        }
        Ty::Vec(a)
        | Ty::Array(a)
        | Ty::Slice(a)
        | Ty::Option(a)
        | Ty::Ref(a)
        | Ty::RefMut(a)
        | Ty::SharedVar(true, a)
        | Ty::SharedVar(false, a)
        | Ty::Info(a)
        | Ty::BudgetAnswer(a) => native_type(a),
        Ty::Pair(a, b) | Ty::Result(a, b) | Ty::HashMap(a, b) => {
            native_type(a);
            native_type(b);
        }
        Ty::Data(_, args) | Ty::Std(_, args) => {
            for a in args {
                native_type(a);
            }
        }
        _ => {}
    }
}
