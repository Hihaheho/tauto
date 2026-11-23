//! `syn_parse` at run time: the parser of `totes/synrun`, written in Tauto and compiled by
//! this backend, reads the text with the same tables and diagnostics as the Rust backend.
//! What is written here is each parser as `Tables::runtime_text` writes it, with the
//! constructors of the syntax's types numbered, and the values of the answer made with
//! those constructors.
use std::sync::OnceLock;

use crate::{R, quote};
use tauto_message::msg;
use tauto_nir::{Package, Ty};
use tauto_syntax::{RuntimeIds, Tables};

/// The parser that a `syn_parse` call with these literal arguments reads
/// with.
pub(crate) fn parser_index(pkg: &Package, name: &str, sha: &str, result: &Ty) -> Option<usize> {
    pkg.syntax_parsers
        .iter()
        .position(|p| p.name == name && p.sha == sha && p.result == *result)
}

/// A constructor of `data` as `synDecode` makes its values: its symbol, its fields' names,
/// whether it is a structure, and its type's symbol.
fn ctor(pkg: &Package, parser: usize, data: &str, ctor: &str) -> R<String> {
    let d = pkg
        .datas
        .iter()
        .find(|d| pkg.syntax_parsers[parser].data_bindings.get(data) == Some(&d.name))
        .ok_or_else(|| msg!("jsgen-syntax-data-not-retained", data = data).to_string())?;
    let c = d
        .ctors
        .iter()
        .find(|c| {
            d.is_struct
                || pkg.syntax_parsers[parser]
                    .constructor_bindings
                    .get(&(data.to_string(), ctor.to_string()))
                    == Some(&c.name)
        })
        .ok_or_else(|| {
            msg!("jsgen-syntax-schema-constructor", data = data, ctor = ctor).to_string()
        })?;
    let names = c
        .fields
        .iter()
        .map(|f| f.name.as_deref().map(quote).unwrap_or("null".into()))
        .collect::<Vec<_>>()
        .join(",");
    Ok(format!(
        "[{},[{names}],{},{}]",
        quote(crate::constructor_symbol(pkg, &c.name)),
        d.is_struct,
        quote(&crate::owner_symbol(pkg, &d.name))
    ))
}

/// The files of `totes/synrun` and of the totes it depends on, at their places under
/// `totes/`.
const TOTE: &[(&str, &str)] = &[
    (
        "synrun/Tauto.eure",
        include_str!("../../../totes/synrun/Tauto.eure"),
    ),
    (
        "synrun/src/answer.taut",
        include_str!("../../../totes/synrun/src/answer.taut"),
    ),
    (
        "synrun/src/read.taut",
        include_str!("../../../totes/synrun/src/read.taut"),
    ),
    (
        "synrun/src/syn.taut",
        include_str!("../../../totes/synrun/src/syn.taut"),
    ),
    (
        "synrun/src/syntab.taut",
        include_str!("../../../totes/synrun/src/syntab.taut"),
    ),
    (
        "scan/Tauto.eure",
        include_str!("../../../totes/scan/Tauto.eure"),
    ),
    (
        "scan/src/scan.taut",
        include_str!("../../../totes/scan/src/scan.taut"),
    ),
    (
        "scan/src/dynamic.taut",
        include_str!("../../../totes/scan/src/dynamic.taut"),
    ),
    (
        "scan/src/longest.taut",
        include_str!("../../../totes/scan/src/longest.taut"),
    ),
    (
        "text/Tauto.eure",
        include_str!("../../../totes/text/Tauto.eure"),
    ),
    (
        "text/src/text.taut",
        include_str!("../../../totes/text/src/text.taut"),
    ),
    (
        "text/src/nat.taut",
        include_str!("../../../totes/text/src/nat.taut"),
    ),
    (
        "text/src/utf8.taut",
        include_str!("../../../totes/text/src/utf8.taut"),
    ),
];

/// `totes/synrun` compiled by this backend, as a script whose value reads a parser once
/// (`load`, which shares what it read, so that a parse takes it without a copy) and parses
/// with it (`answer`). The
/// tote is written out to a directory of its own (named by its contents) and read as
/// `tauto build` reads a tote; that is done once in a process.
fn tote() -> R<&'static Tote> {
    static TOTE_JS: OnceLock<Result<Tote, String>> = OnceLock::new();
    TOTE_JS
        .get_or_init(|| {
            let mut sha = tauto_syntax::Sha256::new();
            for (path, text) in TOTE {
                sha.update(path.as_bytes());
                sha.update(&[0]);
                sha.update(text.as_bytes());
                sha.update(&[0]);
            }
            let digest = sha.finish_hex();
            let root = std::env::temp_dir().join(format!("tauto-synrun-{}", &digest[..16]));
            for (path, text) in TOTE {
                let file = root.join(path);
                std::fs::create_dir_all(file.parent().expect("a file of the tote"))
                    .map_err(|e| format!("{}: {e}", file.display()))?;
                std::fs::write(&file, text).map_err(|e| format!("{}: {e}", file.display()))?;
            }
            let loaded = tauto::program::load_tote_for_build(&root.join("synrun"))?;
            let entries = ["syn_load", "syn_answer"].map(String::from).into();
            let pkg = tauto_nibcheck::lower::compile_loaded_entries_with_observer(
                &loaded,
                true,
                tauto_nir::Target::JavaScript,
                Some(&entries),
                |_| {},
            )
            .map_err(|e| e.to_string())?;
            let options = crate::Options {
                exports: vec!["syn_load".into(), "syn_answer".into()],
                ..Default::default()
            };
            let program = crate::generate_with(&pkg, &options)?;
            let program = program
                .replace("\nexport function instantiate(", "\nfunction instantiate(")
                .replace("\nexport async function run(", "\nasync function run(");
            Ok(Tote {
                js: format!(
                    "\nconst synTote=(()=>{{{program}\n{BUILD}\nconst instance=instantiate();return {{load:t=>share(instance.syn_load(t)),build:(v,ctors)=>share(synBuild(v,ctors)),compare:synCompare,answer:instance.syn_answer}};}})();\n"
                ),
                pkg,
            })
        })
        .as_ref()
        .map_err(Clone::clone)
}

/// `totes/synrun` compiled: its script, and its package (whose constructors a parser read
/// ahead of time is made of).
struct Tote {
    js: String,
    pkg: Package,
}

impl Tote {
    /// A constructor of the tote's own types, as `synBuild` makes its values: its symbol,
    /// its fields' names, whether it is a structure, and its type's symbol.
    fn ctor(&self, ty: &str, ctor: &str) -> Option<String> {
        // `Option` is the runtime's own (`some`, `none`).
        match (ty, ctor) {
            ("Option", "Some") => return Some(r#"["Some",[null],false,"Option"]"#.into()),
            ("Option", "None") => return Some(r#"["None",[],false,"Option"]"#.into()),
            _ => {}
        }
        let pkg = &self.pkg;
        let last = |n: &str| n.rsplit("::").next().unwrap_or(n).to_string();
        let d = pkg.datas.iter().find(|d| last(d.name.as_str()) == ty)?;
        let c = if d.is_struct {
            d.ctors.first()?
        } else {
            d.ctors.iter().find(|c| last(c.name.as_str()) == ctor)?
        };
        let names = c
            .fields
            .iter()
            .map(|f| f.name.as_deref().map(quote).unwrap_or("null".into()))
            .collect::<Vec<_>>()
            .join(",");
        Some(format!(
            "[{},[{names}],{},{}]",
            quote(crate::constructor_symbol(pkg, &c.name)),
            d.is_struct,
            quote(&crate::owner_symbol(pkg, &d.name))
        ))
    }

    /// The literal that makes the parser written in `text`, and the constructors it
    /// names; `None` when it is read at run time instead.
    fn parser(&self, text: &str) -> Option<String> {
        let v = crate::synvalue::read(text)?;
        let mut ctors = std::collections::HashMap::new();
        ctors.insert(("List", "Cons"), 0);
        ctors.insert(("List", "Nil"), 1);
        let mut lit = String::new();
        crate::synvalue::write(&v, &mut ctors, &mut lit);
        let mut order = ctors.into_iter().collect::<Vec<_>>();
        order.sort_by_key(|(_, n)| *n);
        let descs = order
            .into_iter()
            .map(|((ty, c), _)| self.ctor(ty, c))
            .collect::<Option<Vec<_>>>()?;
        Some(format!("{lit},[{}]", descs.join(",")))
    }
}

/// Makes a parser read ahead of time from its literal (`synvalue::write`).
const BUILD: &str = r#"function synBuild(v,ctors){
    const make=(d,fields)=>({owner:d[3],tag:d[0],names:d[1],fields,struct:d[2]});
    const value=v=>{
        if(typeof v!=='object')return v;
        if(Array.isArray(v)){const fields=[];for(let i=1;i<v.length;i++)fields.push(value(v[i]));return make(ctors[v[0]],fields);}
        if(v.a)return {kind:'Array',items:v.a.map(value)};
        let out=make(ctors[1],[]);
        for(let i=v.l.length-1;i>=0;i--)out=make(ctors[0],[value(v.l[i]),out]);
        return out;
    };
    return value(v);
}
function synCompare(built,read){
    const text=v=>JSON.stringify(v,(k,x)=>typeof x==='bigint'?x+'n':x);
    if(text(built)!==text(read))throw new Error('tauto: a parser read ahead of time is not what the text reads');
    return built;
}"#;

/// The parsers' tables and constructors, and the parser of `totes/synrun` they run on, when
/// the program parses at run time: the first part goes before the runtime is shaken (it
/// names what it uses of it), the second after (it has a runtime of its own).
pub(crate) fn parsers(pkg: &Package) -> R<(String, String)> {
    if pkg.syntax_parsers.is_empty() {
        return Ok((String::new(), String::new()));
    }
    let tote = tote()?;
    let mut out = String::from(RUNTIME);
    for (i, parser) in pkg.syntax_parsers.iter().enumerate() {
        let tables = Tables::read(&parser.tables).map_err(|e| format!("{e:?}"))?;
        let mut ctors = Vec::new();
        let mut number = |c: String| -> u32 {
            ctors.push(c);
            (ctors.len() - 1) as u32
        };
        let ids = RuntimeIds {
            span: number(ctor(pkg, i, "SynSpan", "SynSpan")?),
            ctx: number(ctor(pkg, i, "SynCtx", "SynCtx")?),
            token: number(ctor(pkg, i, "SynToken", "SynToken")?),
            diag: number(ctor(pkg, i, "SynDiag", "SynDiag")?),
            arg: number(ctor(pkg, i, "SynArg", "SynArg")?),
        };
        let mut nodes: Vec<String> = Vec::new();
        let text = tables.runtime_text(
            &parser.name,
            &mut |ty, c| {
                let (name, ctor_name, _) = tables.runtime_constructor(ty, c)?;
                let data = tauto_syntax::type_name(&parser.name, name);
                nodes.push(ctor(pkg, i, &data, ctor_name)?);
                Ok((ctors.len() + nodes.len() - 1) as u32)
            },
            ids,
        )?;
        ctors.extend(nodes);
        // With `TAUTO_JS_SYNTAX_COMPARE` set, the program also reads the text and stops
        // when that is not what was read ahead of time (the tests set it).
        let load = match tote.parser(&text) {
            Some(lit) if std::env::var_os("TAUTO_JS_SYNTAX_COMPARE").is_some() => {
                format!(
                    "synTote.compare(synTote.build({lit}),synTote.load({}))",
                    quote(&text)
                )
            }
            Some(lit) => format!("synTote.build({lit})"),
            None => format!("synTote.load({})", quote(&text)),
        };
        out.push_str(&format!(
            "const synCtors{i}=[{}];\nlet synParser{i};\nfunction synParse{i}(text){{synParser{i}??={load};return synDecode(synTote.answer(synParser{i},text),synCtors{i});}}\n",
            ctors.join(","),
        ));
    }
    Ok((out, tote.js.clone()))
}

/// Reads the answer of `syn_answer` (`totes/synrun/src/answer.taut`) into the program's
/// values.
pub const RUNTIME: &str = r#"
function synDecode(answer,ctors){
    const b=new TextEncoder().encode(answer);let i=0;
    const num=()=>{while(b[i]===32)i++;let n=0;while(b[i]>=48&&b[i]<=57){n=n*10+(b[i]-48);i++;}return n;};
    const text=()=>{while(b[i]===32)i++;i++;const n=num();i++;const s=new TextDecoder().decode(b.subarray(i,i+n));i+=n;return s;};
    const value=()=>{
        switch(num()){
        case 0:{const d=ctors[num()],n=num(),fields=[],order=[];for(let k=0;k<n;k++){fields.push(value());order.push(k);}return construct(d[0],d[1],fields,order,d[2],d[3]);}
        case 1:return BigInt(num());
        case 2:return text();
        case 3:{const n=num(),items=[];for(let k=0;k<n;k++)items.push(value());return list(items);}
        case 4:return num()?some(value()):none();
        }
        throw new Error('tauto: the parser gave an unknown value');
    };
    const tag=num();
    if(tag===2)throw new Error('tauto: the tables of a syntax do not read');
    const v=value();
    return tag===0?ok(v):err(v);
}
"#;

/// `totes/synrun` compiled, as a program that parses at run time carries it.
pub fn synrun_script() -> R<String> {
    Ok(tote()?.js.clone())
}

/// A constructor of `totes/synrun`'s types as a parser read ahead of time names it, or
/// `None` when the tote has none so named.
pub fn synrun_constructor(ty: &str, ctor: &str) -> R<Option<String>> {
    Ok(tote()?.ctor(ty, ctor))
}
