//! `syn_parse` at run time: the parser of `tauto-syntax`, compiled to
//! WebAssembly (`crates/tauto-syntax-wasm`), reads the text with the same
//! tables and diagnostics as the Rust backend; the schema-directed
//! conversion of its tree to the syntax's data is written here, as the Rust
//! backend writes it in `tauto-rustgen/src/syntax.rs`.
use crate::{R, quote};
use tauto_message::msg;
use tauto_nir::{Package, Ty};
use tauto_syntax::{FieldTy, Payload, Tables, TypeDef};

const PARSER: &[u8] = include_bytes!("syntax_parser.wasm");

/// The parser that a `syn_parse` call with these literal arguments reads
/// with.
pub(crate) fn parser_index(pkg: &Package, name: &str, sha: &str, result: &Ty) -> Option<usize> {
    pkg.syntax_parsers
        .iter()
        .position(|p| p.name == name && p.sha == sha && p.result == *result)
}

fn ctor(pkg: &Package, data: &str, ctor: &str, values: &[String]) -> R<String> {
    let d = pkg
        .datas
        .iter()
        .find(|d| d.name == data)
        .ok_or_else(|| msg!("jsgen-syntax-data-not-retained", data = data).to_string())?;
    let c = d
        .ctors
        .iter()
        .find(|c| d.is_struct || c.name == ctor || c.name.rsplit("::").next() == Some(ctor))
        .ok_or_else(|| {
            msg!("jsgen-syntax-schema-constructor", data = data, ctor = ctor).to_string()
        })?;
    if c.fields.len() != values.len() {
        return Err(msg!("jsgen-syntax-schema-fields", data = data, ctor = ctor).to_string());
    }
    let names = c
        .fields
        .iter()
        .map(|f| f.name.as_deref().map(quote).unwrap_or("null".into()))
        .collect::<Vec<_>>()
        .join(",");
    let order = (0..values.len())
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(",");
    Ok(format!(
        "construct({},[{names}],[{}],[{order}],{},{})",
        quote(&c.name),
        values.join(","),
        d.is_struct,
        quote(&d.name)
    ))
}

fn field(pkg: &Package, parser: usize, ty: &FieldTy, ast: &str) -> R<String> {
    Ok(match ty {
        FieldTy::Named(name) => format!("syn{parser}_{name}({ast},text)"),
        FieldTy::Token => {
            let span = ctor(pkg, "SynSpan", "SynSpan", &["BigInt(t[0])".into()])?;
            let empty = ctor(pkg, "List", "Nil", &[])?;
            let ctx = ctor(pkg, "SynCtx", "SynCtx", &[empty])?;
            let token = ctor(
                pkg,
                "SynToken",
                "SynToken",
                &["synText(text,t[0],t[1])".into(), span, ctx],
            )?;
            format!("(t=>{token})({ast}.t)")
        }
        FieldTy::List(inner) => {
            let value = field(pkg, parser, inner, "item")?;
            format!("list({ast}.l.map(item=>{value}))")
        }
        FieldTy::Opt(inner) => {
            let value = field(pkg, parser, inner, "item")?;
            format!("(item=>item===null?none():some({value}))({ast}.o)")
        }
        FieldTy::Expr => return Err(msg!("jsgen-syntax-expression-hole").to_string()),
    })
}

/// The parsers' converters, and the WebAssembly module they run, when the
/// program parses at run time.
pub(crate) fn parsers(pkg: &Package) -> R<String> {
    if pkg.syntax_parsers.is_empty() {
        return Ok(String::new());
    }
    let mut out = format!(
        "\nconst synModule=new WebAssembly.Module(Uint8Array.from(atob({}),c=>c.charCodeAt(0)));\n{}",
        quote(&base64(PARSER)),
        RUNTIME
    );
    for (i, parser) in pkg.syntax_parsers.iter().enumerate() {
        let tables = Tables::read(&parser.tables).map_err(|e| format!("{e:?}"))?;
        for ty in &tables.schema().types {
            let (name, ctors): (&str, Vec<(&str, bool, Vec<&FieldTy>)>) = match ty {
                TypeDef::Struct { name, fields, .. } => (
                    name,
                    vec![(name, true, fields.iter().map(|(_, t)| t).collect())],
                ),
                TypeDef::Enum { name, ctors } => (
                    name,
                    ctors
                        .iter()
                        .map(|c| match &c.payload {
                            Payload::Record(fields) => (
                                c.name.as_str(),
                                true,
                                fields.iter().map(|(_, t)| t).collect(),
                            ),
                            Payload::Single(field) => (c.name.as_str(), false, vec![field]),
                        })
                        .collect(),
                ),
            };
            let data = tauto_syntax::type_name(&parser.name, name);
            let mut arms = Vec::new();
            for (index, (c, span, fields)) in ctors.into_iter().enumerate() {
                let mut values = Vec::new();
                if span {
                    values.push(ctor(pkg, "SynSpan", "SynSpan", &["BigInt(n[2])".into()])?);
                }
                for (k, f) in fields.into_iter().enumerate() {
                    values.push(field(pkg, i, f, &format!("n[4][{k}]"))?);
                }
                arms.push(format!(
                    "case {index}:return {};",
                    ctor(pkg, &data, c, &values)?
                ));
            }
            out.push_str(&format!(
                "function syn{i}_{name}(ast,text){{const n=ast.n;switch(n[1]){{{}default:throw new Error('tauto: the parser gave an unknown constructor');}}}}\n",
                arms.concat()
            ));
        }
        let start = tables
            .start_type()
            .ok_or_else(|| msg!("jsgen-syntax-no-start-type").to_string())?;
        let start = match &tables.schema().types[start as usize] {
            TypeDef::Struct { name, .. } | TypeDef::Enum { name, .. } => name,
        };
        let expected = "list(d.expected)".to_string();
        let diag = ctor(
            pkg,
            "SynDiag",
            "SynDiag",
            &[
                "d.message".into(),
                "BigInt(d.at)".into(),
                expected,
                quote("macro.syntax_error"),
            ],
        )?;
        out.push_str(&format!(
            "function synParse{i}(text){{const a=synRun({},{},text);if(a.ok)return ok(syn{i}_{start}(a.ok,text));const d=a.err;return err({diag});}}\n",
            quote(&parser.name),
            quote(&parser.tables)
        ));
    }
    Ok(out)
}

/// Runs the parser on a text: the parsed tree or a diagnostic, as JSON.
const RUNTIME: &str = r#"let synInstance=null;
function synRun(name,tables,text){
    synInstance??=new WebAssembly.Instance(synModule,{});
    const x=synInstance.exports,encoder=new TextEncoder();
    const put=s=>{const b=encoder.encode(s),p=x.alloc(b.length);new Uint8Array(x.memory.buffer,p,b.length).set(b);return [p,b.length];};
    const [n,nl]=put(name),[t,tl]=put(tables),[s,sl]=put(text);
    const a=x.parse(n,nl,t,tl,s,sl);
    const len=new DataView(x.memory.buffer).getUint32(a,true);
    const json=new TextDecoder().decode(new Uint8Array(x.memory.buffer,a+4,len));
    x.release(a,len+4);x.release(n,nl);x.release(t,tl);x.release(s,sl);
    return JSON.parse(json);
}
function synText(text,start,end){return new TextDecoder().decode(new TextEncoder().encode(text).subarray(start,end));}
"#;

fn base64(bytes: &[u8]) -> String {
    const A: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let n = chunk
            .iter()
            .enumerate()
            .fold(0u32, |n, (i, b)| n | (*b as u32) << (16 - 8 * i));
        for i in 0..4 {
            if i <= chunk.len() {
                out.push(A[(n >> (18 - 6 * i) & 63) as usize] as char);
            } else {
                out.push('=');
            }
        }
    }
    out
}
