//! `totes/eure`'s reading of Eure text against `eure-reader`: the documents
//! both make of each `.eure` file of the repository, written out the same way.
//! A file the tote does not read (sets, `inf`, delimited strings, …) must be
//! one Rust reads, and is counted, not compared.

use std::fs;
use std::path::{Path, PathBuf};

use eure_document::document::node::NodeValue;
use eure_document::document::{EureDocument, NodeId};
use eure_document::text::Language;
use eure_document::value::{ObjectKey, PrimitiveValue as P};
use selfhost_harness::{assert_same_dump, root, run_tote_at};

/// Prints each file's document, or `refused`, between `== <n>` lines.

/// `source` with its statements, those after its imports and functions, in
/// the body of the tote's `main`: a tote's main is a module.
fn entry(source: &str) -> String {
    let lines: Vec<&str> = source.lines().collect();
    let start = lines
        .iter()
        .position(|l| ["match ", "var ", "let ", "print(", "each("].iter().any(|p| l.starts_with(p)))
        .unwrap_or(lines.len());
    let mut out: String = lines[..start].iter().map(|l| format!("{l}\n")).collect();
    out.push_str("perform main(() => {\n");
    for l in &lines[start..] {
        out.push_str(&format!("  {l}\n"));
    }
    out.push_str("})\n");
    out
}

fn main_source() -> &'static str {
    r#"import eure::eure
import eure::value
import std::builtin::os
import std::text

fn esc(t: Text): Text {
  Text::replace_all(Text::replace_all(Text::replace_all(t, "\\", "\\\\"), "\n", "\\n"), "\r", "\\r")
}

fn sign(neg: Bool, n: Nat): Text {
  if neg { Text::concat("-", Text::of_nat(n)) } else { Text::of_nat(n) }
}

fn key(k: Key): Text {
  match k {
    Kstr(t) => Text::concat_all(Cons("\"", Cons(esc(t), Cons("\"", Nil))))
    Knum(neg, n) => sign(neg, n)
    Ktup(items) => Text::concat_all(Cons("(", Cons(keys(items), Cons(")", Nil))))
  }
}

fn keys(ks: List(Key)): Text {
  match ks {
    Nil => ""
    Cons(k, rest) => Text::concat_all(Cons(key(k), Cons(",", Cons(keys(rest), Nil))))
  }
}

fn lang(l: Lang): Text {
  match l {
    Plaintext => "plain"
    Implicit => "implicit"
    Named(n) => Text::concat("lang:", n)
  }
}

fn node(n: Node): Text {
  match n {
    Mk(v, ext) => Text::concat(exts(ext), value(v))
  }
}

fn exts(es: List(Text × Node)): Text {
  match es {
    Nil => ""
    Cons(e, rest) => Text::concat_all(Cons("$", Cons(e.fst, Cons("=", Cons(node(e.snd), Cons(" ", Cons(exts(rest), Nil)))))))
  }
}

fn nodes(ns: List(Node)): Text {
  match ns {
    Nil => ""
    Cons(n, rest) => Text::concat_all(Cons(node(n), Cons(",", Cons(nodes(rest), Nil))))
  }
}

fn entries(es: List(Key × Node)): Text {
  match es {
    Nil => ""
    Cons(e, rest) => Text::concat_all(Cons(key(e.fst), Cons("=>", Cons(node(e.snd), Cons(";", Cons(entries(rest), Nil))))))
  }
}

fn value(v: Value): Text {
  match v {
    Vhole(None) => "!"
    Vhole(Some(l)) => Text::concat("!", l)
    Vnull => "null"
    Vbool(b) => if b { "true" } else { "false" }
    Vint(neg, n) => sign(neg, n)
    Vdec(neg, mant, eneg, exp) => "decimal"
    Vtext(l, t) => Text::concat_all(Cons(lang(l), Cons("\"", Cons(esc(t), Cons("\"", Nil)))))
    Varr(items) => Text::concat_all(Cons("[", Cons(nodes(items), Cons("]", Nil))))
    Vtup(items) => Text::concat_all(Cons("(", Cons(nodes(items), Cons(")", Nil))))
    Vmap(es) => Text::concat_all(Cons("{", Cons(entries(es), Cons("}", Nil))))
  }
}

fn each(paths: List(Text)) {
  match paths {
    Nil => #()
    Cons(p, rest) => {
      match read_file(p) {
        Ok(t) => match parse(t) {
          Ok(d) => print(Text::concat(node(d), "\n"))
          Err(_) => print("refused\n")
        }
        Err(_) => print("refused\n")
      }
      each(rest)
    }
  }
}

each(perform argv())
"#
}

fn esc(t: &str) -> String {
    t.replace('\\', "\\\\")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
}

fn key(k: &ObjectKey) -> String {
    match k {
        ObjectKey::Number(n) => n.to_string(),
        ObjectKey::String(s) => format!("\"{}\"", esc(s)),
        ObjectKey::Tuple(t) => format!("({})", t.iter().map(|k| format!("{},", key(k))).collect::<String>()),
    }
}

fn node(doc: &EureDocument, id: NodeId) -> Option<String> {
    let n = doc.node(id);
    let mut out = String::new();
    for (name, e) in n.extensions.iter() {
        out.push_str(&format!("${name}={} ", node(doc, *e)?));
    }
    let v = match &n.content {
        NodeValue::Hole(None) => "!".to_string(),
        NodeValue::Hole(Some(l)) => format!("!{l}"),
        NodeValue::Primitive(P::Null) => "null".into(),
        NodeValue::Primitive(P::Bool(b)) => b.to_string(),
        NodeValue::Primitive(P::Integer(i)) => i.to_string(),
        NodeValue::Primitive(P::Decimal(_)) => "decimal".into(),
        NodeValue::Primitive(P::Text(t)) => {
            let lang = match &t.language {
                Language::Plaintext => "plain".to_string(),
                Language::Implicit => "implicit".to_string(),
                Language::Other(l) => format!("lang:{l}"),
            };
            format!("{lang}\"{}\"", esc(&t.content))
        }
        NodeValue::Array(items) => {
            let mut s = "[".to_string();
            for i in items.iter() {
                s.push_str(&format!("{},", node(doc, *i)?));
            }
            s + "]"
        }
        NodeValue::Tuple(items) => {
            let mut s = "(".to_string();
            for i in items.iter() {
                s.push_str(&format!("{},", node(doc, *i)?));
            }
            s + ")"
        }
        NodeValue::Map(m) => {
            let mut s = "{".to_string();
            for (k, v) in m.iter() {
                s.push_str(&format!("{}=>{};", key(k), node(doc, *v)?));
            }
            s + "}"
        }
        // What the tote does not read.
        _ => return None,
    };
    out.push_str(&v);
    Some(out)
}

fn eure_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else { return };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        let name = p.file_name().unwrap().to_string_lossy().into_owned();
        if name.starts_with('.') || name == "target" {
            continue;
        }
        if p.is_dir() {
            eure_files(&p, out);
        } else if name.ends_with(".eure") || name == "Tauto.lock" {
            out.push(p);
        }
    }
}

#[test]
fn documents_match_eure_reader() {
    let mut files = Vec::new();
    eure_files(&root(), &mut files);
    assert!(files.len() > 100, "{} files", files.len());
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-eure-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    fs::create_dir_all(base.join("src")).unwrap();
    fs::write(
        base.join("Tauto.eure"),
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  eure {{ path = \"{}\" }}\n}}\n",
            root().join("totes/eure").canonicalize().unwrap().display()
        ),
    )
    .unwrap();
    fs::write(base.join("src/main.taut"), entry(&main_source())).unwrap();
    let args: Vec<String> = files.iter().map(|f| f.to_string_lossy().into_owned()).collect();
    let out = run_tote_at(&base, &args, 40_000_000_000);
    let _ = fs::remove_dir_all(&base);
    assert_eq!(out.error, None, "{}", out.stderr);
    let tauto: Vec<&str> = out.stdout.lines().collect();
    assert_eq!(tauto.len(), files.len(), "{}", out.stdout);
    let (mut rust_dump, mut tote_dump) = (String::new(), String::new());
    let mut unread = Vec::new();
    for (f, t) in files.iter().zip(&tauto) {
        let text = fs::read_to_string(f).unwrap_or_default();
        let rust = eure_reader::parse_to_document(&text, f)
            .ok()
            .and_then(|d| node(&d, d.get_root_id()));
        let place = f.strip_prefix(root()).unwrap_or(f).display().to_string();
        match (rust, *t) {
            (None, "refused") => {}
            (Some(_), "refused") => unread.push(place),
            (r, t) => {
                rust_dump.push_str(&format!("== {place}\n{}\n", r.unwrap_or("refused".into())));
                tote_dump.push_str(&format!("== {place}\n{t}\n"));
            }
        }
    }
    eprintln!("{} files; the tote does not read {}: {unread:?}", files.len(), unread.len());
    assert_same_dump("eure documents", &rust_dump, &tote_dump);
}
