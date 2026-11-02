//! Names: where a use is declared, the uses of a declaration, renaming.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use tauto_analyzer::navigate::{Edit, Navigator, Place, TypeInfo, workspace_files};

fn disk(p: &Path) -> Option<String> {
    std::fs::read_to_string(p).ok()
}

#[test]
#[ignore]
fn scan_repo() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut total = 0;
    let mut bad: std::collections::BTreeMap<String, (usize, String)> = Default::default();
    for dir in ["std", "meta", "examples", "std/prelude", "totes"] {
        for f in workspace_files(&root.join(dir)) {
            let Some(nav) = Navigator::open(&f, &disk) else {
                continue;
            };
            let idx = nav.dump();
            total += idx.0;
            for (n, c, w) in idx.1 {
                let e = bad.entry(n).or_insert((0, w));
                e.0 += c;
            }
        }
    }
    let mut v: Vec<_> = bad.into_iter().collect();
    v.sort_by_key(|(_, c)| std::cmp::Reverse(c.0));
    eprintln!("refs {total}");
    for (n, (c, w)) in v.iter().take(70) {
        eprintln!(
            "{c:5} {n}  {}",
            w.trim_start_matches(root.to_string_lossy().as_ref())
        );
    }
}

/// A directory of files, and positions in them found by their text.
struct Fixture {
    dir: PathBuf,
}

impl Fixture {
    fn new(name: &str, files: &[(&str, &str)]) -> Fixture {
        let dir = std::env::temp_dir().join(format!("tauto-nav-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        for (n, t) in files {
            std::fs::create_dir_all(dir.join(n).parent().unwrap()).unwrap();
            std::fs::write(dir.join(n), t).unwrap();
        }
        Fixture { dir }
    }

    fn path(&self, file: &str) -> PathBuf {
        self.dir.join(file).canonicalize().unwrap()
    }

    fn text(&self, file: &str) -> String {
        std::fs::read_to_string(self.path(file)).unwrap()
    }

    /// The offset of the `nth` (from 0) occurrence of `needle` in `file`,
    /// plus `into` bytes.
    fn at(&self, file: &str, needle: &str, nth: usize, into: usize) -> usize {
        let text = self.text(file);
        let (i, _) = text
            .match_indices(needle)
            .nth(nth)
            .unwrap_or_else(|| panic!("no {nth}th {needle:?}"));
        i + into
    }

    fn workspace(&self) -> Vec<PathBuf> {
        workspace_files(&self.dir)
    }

    /// Applies the edits of a rename to the files on disk's text, in memory.
    fn apply(&self, edits: &[Edit]) -> HashMap<String, String> {
        let mut out: HashMap<String, String> = HashMap::new();
        for e in edits {
            let name = e.path.file_name().unwrap().to_string_lossy().to_string();
            out.entry(name.clone()).or_insert_with(|| self.text(&name));
        }
        for (name, text) in out.iter_mut() {
            let mut mine: Vec<&Edit> = edits
                .iter()
                .filter(|e| e.path.file_name().unwrap().to_string_lossy() == name.as_str())
                .collect();
            mine.sort_by_key(|e| std::cmp::Reverse(e.span.start));
            for e in mine {
                text.replace_range(e.span.start as usize..e.span.end as usize, &e.text);
            }
        }
        out
    }
}

fn open<'a>(f: &Fixture, file: &str) -> Navigator<'a> {
    // The tests read the English text of refusals.
    tauto_messages::install();
    Navigator::open(&f.path(file), &disk).expect("the file loads")
}

fn slice(p: &Place) -> String {
    let t = std::fs::read_to_string(&p.path).unwrap();
    t[p.span.start as usize..p.span.end as usize].to_string()
}

fn scopes_source() -> &'static str {
    r#"fn twice(n: i64): i64 { n + n }
fn main(): i64 {
  let n := 3
  let m := twice(n)
  let k := match Some(m) {
    Some(n) => n + 1
    None => 0
  }
  let add := (n: i64) => n + k
  add(m)
}
"#
}

#[test]
fn a_use_finds_the_binding_in_scope() {
    let f = Fixture::new("scopes", &[("a.nib", scopes_source())]);
    let nav = open(&f, "a.nib");
    // `twice(n)` in main: the call finds the function, its argument the let.
    let def = nav
        .definition(f.at("a.nib", "twice(n)", 0, 1), None)
        .unwrap();
    assert_eq!(slice(&def), "twice");
    assert!(def.span.start < f.at("a.nib", "fn main", 0, 0) as u32);
    let let_n = f.at("a.nib", "let n", 0, 4);
    let arg = nav
        .definition(f.at("a.nib", "twice(n)", 0, 6), None)
        .unwrap();
    assert_eq!(arg.span.start as usize, let_n);
    // `n + 1` in the arm is the pattern's `n`, not the let's.
    let pat = f.at("a.nib", "Some(n)", 0, 5);
    let in_arm = nav.definition(f.at("a.nib", "n + 1", 0, 0), None).unwrap();
    assert_eq!(in_arm.span.start as usize, pat);
    // The lambda's parameter shadows both.
    let lam = f.at("a.nib", "(n: i64)", 1, 1);
    let in_body = nav.definition(f.at("a.nib", "n + k", 0, 0), None).unwrap();
    assert_eq!(in_body.span.start as usize, lam);
    // `k` after the match is the let.
    let k = nav.definition(f.at("a.nib", "n + k", 0, 4), None).unwrap();
    assert_eq!(k.span.start as usize, f.at("a.nib", "let k", 0, 4));
}

#[test]
fn hover_shows_the_declaration_and_the_checker_s_type() {
    let f = Fixture::new("hover", &[("a.nib", scopes_source())]);
    let nav = open(&f, "a.nib");
    let h = nav.hover(f.at("a.nib", "twice(n)", 0, 1), None).unwrap();
    assert!(
        h.contents.contains("fn twice(n: i64): i64"),
        "{}",
        h.contents
    );
    assert!(h.contents.contains("function"));
    let p = f.path("a.nib");
    let types = TypeInfo::build(&p, &f.text("a.nib")).expect("it loads");
    // `let n = 3` has no type written; the checker says i64.
    let h = nav
        .hover(f.at("a.nib", "let n", 0, 4), Some(&types))
        .unwrap();
    assert!(h.contents.contains("let n"), "{}", h.contents);
    assert!(h.contents.contains("type: `i64`"), "{}", h.contents);
    // The same for a use.
    let h = nav
        .hover(f.at("a.nib", "add(m)", 0, 4), Some(&types))
        .unwrap();
    assert!(h.contents.contains("let m"), "{}", h.contents);
    assert!(h.contents.contains("type: `i64`"), "{}", h.contents);
}

#[test]
fn rename_changes_every_use_and_only_those() {
    let f = Fixture::new("rename", &[("a.nib", scopes_source())]);
    let mut nav = open(&f, "a.nib");
    // The let `n` is used once, in `twice(n)`; the parameter and the arm's n are others.
    let edits = nav
        .rename(f.at("a.nib", "let n", 0, 4), "count", &f.workspace())
        .unwrap();
    let out = f.apply(&edits);
    let text = &out["a.nib"];
    assert!(text.contains("let count := 3"));
    assert!(text.contains("twice(count)"));
    assert!(text.contains("fn twice(n: i64): i64 { n + n }"));
    assert!(text.contains("Some(n) => n + 1"));
    assert!(text.contains("(n: i64) => n + k"));
}

#[test]
fn rename_refuses_what_would_capture_or_cannot_be_found() {
    let f = Fixture::new("refuse", &[("a.nib", scopes_source())]);
    let mut nav = open(&f, "a.nib");
    let ws = f.workspace();
    // `k` renamed to `m` is refused: `add(m)` at the end refers to the first
    // `m`, and would then refer to the renamed let instead.
    let e = nav
        .rename(f.at("a.nib", "let k", 0, 4), "m", &ws)
        .unwrap_err();
    assert!(e.contains("would change what"), "{e}");
    assert!(nav.rename(f.at("a.nib", "let k", 0, 4), "fn", &ws).is_err());
    assert!(
        nav.rename(f.at("a.nib", "let k", 0, 4), "not a name", &ws)
            .is_err()
    );
    // The prelude's names are not ours to rename.
    assert!(nav.prepare_rename(f.at("a.nib", "Some(m)", 0, 1)).is_err());
}

#[test]
fn a_function_is_renamed_in_the_files_that_import_it() {
    let f = Fixture::new(
        "files",
        &[
            (
                "lib.nib",
                r#"pub fn double(x: i64): i64 { x + x }
"#,
            ),
            (
                "main.nib",
                r#"import "lib.nib"
fn main(): i64 { double(2) }
"#,
            ),
            (
                "other.nib",
                r#"import "lib.nib"
pub fn twice(): i64 { double(3) + double(4) }
"#,
            ),
            (
                "alone.nib",
                r#"fn unrelated(): i64 { 1 }
"#,
            ),
        ],
    );
    let mut nav = open(&f, "main.nib");
    let def = nav
        .definition(f.at("main.nib", "double", 0, 0), None)
        .unwrap();
    assert_eq!(def.path, f.path("lib.nib"));
    assert_eq!(slice(&def), "double");
    let uses = nav.references(f.at("main.nib", "double", 0, 0), false, &f.workspace());
    assert_eq!(uses.len(), 3, "{uses:?}");
    let edits = nav
        .rename(f.at("main.nib", "double", 0, 0), "dbl", &f.workspace())
        .unwrap();
    let out = f.apply(&edits);
    assert!(out["lib.nib"].starts_with("pub fn dbl(x: i64)"));
    assert!(out["main.nib"].contains("dbl(2)"));
    assert!(out["other.nib"].contains("dbl(3) + dbl(4)"));
    assert!(!out.contains_key("alone.nib"));
}

#[test]
fn a_tote_s_other_files_are_not_edited_blindly() {
    let f = Fixture::new(
        "blind",
        &[
            (
                "src/lib.nib",
                r#"fn double(x: i64): i64 { x + x }
"#,
            ),
            (
                "src/loose.nib",
                r#"fn g(): i64 { double(1) }
"#,
            ),
            (
                "Tauto.eure",
                "package {\n  name = \"blind\"\n  version = \"0.1.0\"\n}\n",
            ),
        ],
    );
    let mut nav = open(&f, "src/lib.nib");
    let e = nav
        .rename(f.at("src/lib.nib", "double", 0, 0), "dbl", &f.workspace())
        .unwrap_err();
    assert!(e.contains("loose.nib"), "{e}");
}

fn proofs_source() -> &'static str {
    r#"inductive Even(n: Nat): Prop {
  EvenZero: Even(0)
  EvenSs<m: Nat>(h: Even(m)): Even(Succ(Succ(m)))
}
theorem even_two(): Even(2) { EvenSs(EvenZero) }
theorem keep<P: Prop>(p: P): P { p }
"#
}

#[test]
fn proofs_have_constructors_generics_and_theorems() {
    let f = Fixture::new("proofs", &[("p.taut", proofs_source())]);
    let mut nav = open(&f, "p.taut");
    let def = nav
        .definition(f.at("p.taut", "EvenSs(EvenZero", 0, 0), None)
        .unwrap();
    assert_eq!(def.span.start as usize, f.at("p.taut", "EvenSs<m", 0, 0));
    let h = nav
        .hover(f.at("p.taut", "EvenSs(EvenZero", 0, 0), None)
        .unwrap();
    assert!(
        h.contents
            .contains("EvenSs<m: Nat>(h: Even(m)): Even(Succ(Succ(m)))"),
        "{}",
        h.contents
    );
    // The family's parameter and a constructor's generic.
    let m = nav
        .definition(f.at("p.taut", "Even(m)", 0, 5), None)
        .unwrap();
    assert_eq!(m.span.start as usize, f.at("p.taut", "m: Nat", 0, 0));
    let edits = nav
        .rename(f.at("p.taut", "EvenZero", 0, 0), "Ev0", &f.workspace())
        .unwrap();
    let out = f.apply(&edits);
    assert!(out["p.taut"].contains("Ev0: Even(0)"));
    assert!(out["p.taut"].contains("EvenSs(Ev0)"));
    let edits = nav
        .rename(f.at("p.taut", "<P: Prop>", 0, 1), "Q", &f.workspace())
        .unwrap();
    let out = f.apply(&edits);
    assert!(
        out["p.taut"].contains("keep<Q: Prop>(p: Q): Q"),
        "{}",
        out["p.taut"]
    );
}

#[test]
fn fields_enums_and_modules() {
    let src = r#"struct Point { x: i64, y: i64 }
enum Shape { Dot(Point), Empty }
fn area(s: Shape): i64 {
  match s {
    Shape::Dot(p) => p.x + p.y
    Empty => 0
  }
}
fn origin(): Point { Point { x: 0, y: 0 } }
"#;
    let f = Fixture::new("data", &[("d.nib", src)]);
    let mut nav = open(&f, "d.nib");
    let ws = f.workspace();
    // A variant written with its enum, and bare.
    let d = nav
        .definition(f.at("d.nib", "Shape::Dot", 0, 7), None)
        .unwrap();
    assert_eq!(slice(&d), "Dot");
    let d = nav
        .definition(f.at("d.nib", "Empty =>", 0, 0), None)
        .unwrap();
    assert_eq!(d.span.start as usize, f.at("d.nib", "Empty }", 0, 0));
    // A field in a literal and, by its name alone, on a value.
    let d = nav.definition(f.at("d.nib", "x: 0", 0, 0), None).unwrap();
    assert_eq!(d.span.start as usize, f.at("d.nib", "x: i64", 0, 0));
    let d = nav.definition(f.at("d.nib", "p.x", 0, 2), None).unwrap();
    assert_eq!(d.span.start as usize, f.at("d.nib", "x: i64", 0, 0));
    // Fields are not renamed; variants are.
    assert!(
        nav.rename(f.at("d.nib", "x: i64", 0, 0), "px", &ws)
            .is_err()
    );
    let out = f.apply(
        &nav.rename(f.at("d.nib", "Empty }", 0, 0), "Nothing", &ws)
            .unwrap(),
    );
    assert!(out["d.nib"].contains("Dot(Point), Nothing }"));
    assert!(out["d.nib"].contains("Nothing => 0"));
}

#[test]
fn a_name_in_a_syntax_literal_or_quote_stops_a_rename() {
    let src = r#"fn helper(x: i64): i64 { x }
fn make(): SynExpr { quote { helper(1) } }
fn user(): i64 { helper(2) }
"#;
    let f = Fixture::new("opaque", &[("q.nib", src)]);
    let mut nav = open(&f, "q.nib");
    let e = nav
        .rename(f.at("q.nib", "helper", 0, 0), "assist", &f.workspace())
        .unwrap_err();
    assert!(e.contains("quote"), "{e}");
}

#[test]
fn a_filled_in_name_in_quote_is_a_use_of_the_local() {
    let src = r#"fn make(a: SynIdent): SynExpr { quote { let tmp := $a } }
"#;
    let f = Fixture::new("fill", &[("q.nib", src)]);
    let mut nav = open(&f, "q.nib");
    let out = f.apply(
        &nav.rename(f.at("q.nib", "a: SynIdent", 0, 0), "name", &f.workspace())
            .unwrap(),
    );
    assert!(out["q.nib"].contains("make(name: SynIdent)"));
    assert!(out["q.nib"].contains("$name"));
}

fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for e in std::fs::read_dir(from).unwrap().flatten() {
        let p = e.path();
        let t = to.join(e.file_name());
        if p.is_dir() {
            copy_dir(&p, &t);
        } else {
            std::fs::copy(&p, &t).unwrap();
        }
    }
}

/// Renaming each name of real files, wherever the rename is allowed, leaves
/// a program the checker still accepts, as it did.
#[test]
fn a_rename_keeps_the_proofs_checking() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let work = std::env::temp_dir().join(format!("tauto-nav-real-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&work);
    copy_dir(&root.join("examples"), &work);
    let mut renamed = 0;
    let mut refused = 0;
    for entry in [
        "proofs.taut",
        "handlers.taut",
        "nat/Add.taut",
        "nat/Order.taut",
    ] {
        let path = work.join(entry);
        let baseline =
            tauto::report::check_report(&path, None).map(|r| r.status().name().to_string());
        let Ok(baseline) = baseline else { continue };
        let probe = Navigator::open(&path, &disk).unwrap();
        let offsets = probe.declared_offsets();
        let ws = workspace_files(&work);
        let stride = (offsets.len() / 8).max(1);
        for offset in offsets.into_iter().step_by(stride) {
            let mut nav = Navigator::open(&path, &disk).unwrap();
            let edits = match nav.rename(offset, "zzq_renamed", &ws) {
                Ok(e) => e,
                Err(why) => {
                    eprintln!("refused: {why}");
                    refused += 1;
                    continue;
                }
            };
            // Check the edited files in a copy.
            let copy = std::env::temp_dir().join(format!("tauto-nav-copy-{}", std::process::id()));
            let _ = std::fs::remove_dir_all(&copy);
            copy_dir(&work, &copy);
            let mut by_file: HashMap<PathBuf, Vec<&Edit>> = HashMap::new();
            for e in &edits {
                by_file.entry(e.path.clone()).or_default().push(e);
            }
            for (file, mut es) in by_file {
                let rel = file
                    .strip_prefix(work.canonicalize().unwrap())
                    .unwrap()
                    .to_path_buf();
                let mut text = std::fs::read_to_string(&file).unwrap();
                es.sort_by_key(|e| std::cmp::Reverse(e.span.start));
                for e in es {
                    text.replace_range(e.span.start as usize..e.span.end as usize, &e.text);
                }
                std::fs::write(copy.join(rel), text).unwrap();
            }
            let after = tauto::report::check_report(&copy.join(entry), None)
                .map(|r| r.status().name().to_string());
            assert_eq!(
                after.as_deref(),
                Ok(baseline.as_str()),
                "renaming at {offset} in {entry}"
            );
            renamed += 1;
            let _ = std::fs::remove_dir_all(&copy);
        }
    }
    eprintln!("renamed {renamed}, refused {refused}");
    assert!(renamed > 20, "only {renamed} renames were made");
}

/// A name a macro declares has no declaration in the text; the span map
/// leads from the declaration it made back to the call that made it.
#[test]
fn a_name_a_macro_declares_goes_to_the_macro_call() {
    let lib = r#"syntax!(swp, ```par
%start Pair
%%
Pair: Name Name;
Name: /[\p{L}_][\p{L}\p{N}_]*/;
```) => struct Pair, fn parse
pub macro fn mk(p: swp::Pair): List(SynStmt) {
  let a := Syn::ident(p.name)
  quote stmts {
    fn $a(): i64 { 1 }
  }
}
"#
    .to_string();
    let main = r#"import "lib.nib"
mk!(`produced unused`) => fn produced
fn user(): i64 { produced() }
"#;
    let f = Fixture::new("generated", &[("lib.nib", &lib), ("main.nib", main)]);
    let tables =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../tauto/tests/syntax_fixtures/.tauto-syntax");
    std::os::unix::fs::symlink(tables, f.dir.join(".tauto-syntax")).unwrap();
    let nav = open(&f, "main.nib");
    let types = TypeInfo::build(&f.path("main.nib"), main).expect("it loads");
    let at = f.at("main.nib", "produced()", 0, 2);
    assert!(nav.definition(at, None).is_none());
    let place = nav
        .definition(at, Some(&types))
        .expect("found through the macro run");
    // The call that made it, in the text as written.
    assert_eq!(place.path, f.path("main.nib"));
    assert_eq!(place.span.start as usize, f.at("main.nib", "mk!", 0, 0));
}
