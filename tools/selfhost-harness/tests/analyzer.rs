//! `totes/analyzer` against `tauto_analyzer::navigate::index`: the names of a
//! file, where each is declared and where it is used (`docs/design/self-host.md`).

use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_native};
use tauto_analyzer::navigate::index::{FileIndex, World};

const STEPS: u64 = 200_000_000_000;

const KERNEL_PRELUDE: &str = include_str!("../../../crates/tauto-kernel/src/prelude.taut");

fn escape(t: &str) -> String {
    t.replace('\\', "\\\\").replace('\n', "\\n")
}

/// The index in the form `totes/analyzer/src/dump.taut` prints.
fn dump(id: usize, f: &FileIndex, imports: &[(String, bool)]) -> String {
    let mut out = format!("== {id}\n");
    if f.broken {
        out.push_str("error\n");
        return out;
    }
    for (path, module) in imports {
        out.push_str(&format!("import {module} {}\n", escape(path)));
    }
    for (i, d) in f.defs.iter().enumerate() {
        out.push_str(&format!("def {i}\n"));
        out.push_str(&format!("  name {}\n", escape(&d.name)));
        out.push_str(&format!("  kind {}\n", d.kind.label()));
        out.push_str("  spans");
        for s in &d.spans {
            out.push_str(&format!(" {}-{}", s.start, s.end));
        }
        out.push('\n');
        out.push_str(&format!("  sig {}\n", escape(&d.signature)));
        let opt = |t: &Option<String>| t.as_deref().map_or("-".to_string(), escape);
        out.push_str(&format!("  declared {}\n", opt(&d.declared)));
        out.push_str(&format!("  exported {}\n", d.exported));
        let num = |n: Option<u64>| n.map_or("-".to_string(), |n| n.to_string());
        out.push_str(&format!("  site {}\n", num(d.site.map(u64::from))));
        out.push_str(&format!("  parent {}\n", num(d.parent.map(|p| p as u64))));
        out.push_str("  members");
        for m in &d.members {
            out.push_str(&format!(" {m}"));
        }
        out.push('\n');
        out.push_str(&format!("  pinned {}\n", opt(&d.pinned.map(str::to_string))));
    }
    for r in &f.refs {
        out.push_str(&format!(
            "ref {}-{} {}:{} {}\n",
            r.span.start, r.span.end, r.target.file, r.target.index, r.approximate
        ));
    }
    for (what, words) in [("unresolved", &f.unresolved), ("opaque", &f.opaque)] {
        for (s, w) in words {
            out.push_str(&format!("{what} {}-{} {}\n", s.start, s.end, escape(w)));
        }
    }
    for s in &f.top_stmts {
        out.push_str(&format!("top {}-{}\n", s.start, s.end));
    }
    for s in &f.macro_calls {
        out.push_str(&format!("macro {}-{}\n", s.start, s.end));
    }
    for (s, d) in &f.theorem_keywords {
        out.push_str(&format!("theorem {}-{} {d}\n", s.start, s.end));
    }
    out.push_str("closure");
    for c in &f.closure {
        out.push_str(&format!(" {c}"));
    }
    out.push('\n');
    let mut top: Vec<_> = f.toplevel.iter().collect();
    top.sort_by(|a, b| a.0.cmp(b.0));
    for (name, d) in top {
        out.push_str(&format!("toplevel {} {}:{}\n", escape(name), d.file, d.index));
    }
    out
}

/// The files of `inputs` in order, each importing the files whose ids are listed
/// with it (the preludes are 0 and 1, the first input 2).
fn compare(label: &str, inputs: Vec<(String, String, Vec<usize>)>) {
    let mut files = vec![
        ("prelude".to_string(), tauto::nibstd::PRELUDE.to_string()),
        ("kernel-prelude".to_string(), KERNEL_PRELUDE.to_string()),
    ];
    files.extend(inputs.iter().map(|(n, t, _)| (n.clone(), t.clone())));
    let m = materialize(label, &files);
    let mut args = vec![m.paths[0].clone(), m.paths[1].clone()];
    for ((_, _, imports), path) in inputs.iter().zip(&m.paths[2..]) {
        if imports.is_empty() {
            args.push(path.clone());
        } else {
            let ids: Vec<String> = imports.iter().map(usize::to_string).collect();
            args.push(format!("{path}={}", ids.join(",")));
        }
    }
    let out = run_tote_native("analyzer", &args, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");

    let read = |_: &std::path::Path| None;
    let mut world = World::new(&read);
    let mut rust = String::new();
    rust.push_str(&dump(0, world.file(0), &World::imports_of(tauto::nibstd::PRELUDE)));
    rust.push_str(&dump(1, world.file(1), &World::imports_of(KERNEL_PRELUDE)));
    for ((_, text, imports), path) in inputs.iter().zip(&m.paths[2..]) {
        let id = world.add(std::path::Path::new(path), text, imports);
        rust.push_str(&dump(id, world.file(id), &World::imports_of(text)));
    }
    assert_same_dump("analyzer", &rust, &out.stdout);
}

/// One part of the corpus, each file on its own, so that the parts run side by side.
fn part(label: &str, n: usize, of: usize) {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .enumerate()
        .filter(|(i, _)| i % of == n)
        .map(|(_, (name, text))| (name, text, Vec::new()))
        .collect();
    compare(label, inputs);
}

#[test]
fn analyzer_matches_the_corpus_0() {
    part("analyzer-0", 0, 4);
}

#[test]
fn analyzer_matches_the_corpus_1() {
    part("analyzer-1", 1, 4);
}

#[test]
fn analyzer_matches_the_corpus_2() {
    part("analyzer-2", 2, 4);
}

#[test]
fn analyzer_matches_the_corpus_3() {
    part("analyzer-3", 3, 4);
}

/// A file sees the top-level names of the files it imports, transitively, and
/// a field read from a value is found by its name in any of them.
#[test]
fn analyzer_matches_across_imports() {
    let file = |name: &str, text: &str, imports: Vec<usize>| {
        (name.to_string(), text.to_string(), imports)
    };
    compare(
        "analyzer-imports",
        vec![
            file(
                "a",
                "pub struct Point { x: i64, y: i64 }\npub enum Shape { Dot, Circle(i64) }\npub fn origin(): Point { Point { x: 0, y: 0 } }\n",
                vec![],
            ),
            file(
                "b",
                "import \"a.taut\"\npub fn area(s: Shape): i64 {\n  match s {\n    Dot => 0\n    Circle(r) => r * r\n  }\n}\n",
                vec![2],
            ),
            file(
                "c",
                "import \"b.taut\"\nfn main(): i64 {\n  let p := origin()\n  p.x + area(Shape::Circle(p.y))\n}\n",
                vec![3],
            ),
        ],
    );
}

/// What `Navigator` tells an editor about the last of `files` (a name and a
/// text each, written to a directory so that imports between them resolve),
/// in the form `an_dump_navigate` prints.
fn navigate_expected(dir: &std::path::Path, files: &[(String, String)], new_name: &str) -> String {
    use tauto_analyzer::editor::{offset_of, position_of};
    use tauto_analyzer::navigate::Navigator;
    let read = |p: &std::path::Path| std::fs::read_to_string(p).ok();
    let paths: Vec<std::path::PathBuf> = files.iter().map(|(n, _)| dir.join(n)).collect();
    let entry = paths.last().unwrap().clone();
    let text = &files.last().unwrap().1;
    let base = |p: &std::path::Path| p.file_name().unwrap().to_string_lossy().to_string();
    let mut nav = Navigator::open(&entry, &read).unwrap();
    let mut out = String::new();
    for (s, colour) in nav.name_colours() {
        out.push_str(&format!("colour {}-{} {colour}\n", s.start, s.end));
    }
    // The places a name starts, from the index of the file.
    let mut world = World::new(&read);
    let id = world.load(&entry).unwrap();
    let f = world.file(id);
    let mut starts: Vec<u32> = Vec::new();
    for d in &f.defs {
        starts.extend(d.spans.iter().map(|s| s.start));
    }
    starts.extend(f.refs.iter().map(|r| r.span.start));
    starts.extend(f.unresolved.iter().map(|(s, _)| s.start));
    starts.extend(f.macro_calls.iter().map(|s| s.start));
    starts.extend(f.theorem_keywords.iter().map(|(s, _)| s.start));
    starts.sort();
    starts.dedup();
    for at in starts {
        let at = at as usize;
        out.push_str(&format!("at {at}\n"));
        let place = |p: &tauto_analyzer::navigate::Place| {
            format!("{} {}-{}", base(&p.path), p.span.start, p.span.end)
        };
        match nav.definition(at, None) {
            Some(p) => out.push_str(&format!("  def {}\n", place(&p))),
            None => out.push_str("  def -\n"),
        }
        match nav.hover(at, None) {
            Some(h) => out.push_str(&format!(
                "  hover {}-{} {}\n",
                h.span.start,
                h.span.end,
                escape(&h.contents)
            )),
            None => out.push_str("  hover -\n"),
        }
        out.push_str("  refs");
        for p in nav.references(at, true, &paths) {
            out.push_str(&format!(" {}", place(&p)));
        }
        out.push('\n');
        match nav.prepare_rename(at) {
            Ok((s, name)) => out.push_str(&format!("  prepare {}-{} {}\n", s.start, s.end, escape(&name))),
            Err(_) => out.push_str("  prepare error\n"),
        }
        out.push_str("  rename");
        match nav.rename(at, new_name, &paths) {
            Ok(edits) => {
                for e in edits {
                    out.push_str(&format!(
                        " {} {}-{} {}",
                        base(&e.path),
                        e.span.start,
                        e.span.end,
                        escape(&e.text)
                    ));
                }
            }
            Err(_) => out.push_str(" error"),
        }
        out.push('\n');
    }
    for at in (0..=text.len()).filter(|at| text.is_char_boundary(*at)) {
        let (line, col) = position_of(text, at);
        out.push_str(&format!(
            "position {at} {line} {col} {}\n",
            offset_of(text, line, col)
        ));
    }
    out
}

/// `files` as a chain: each imports the one before it.
fn compare_navigate(label: &str, files: Vec<(&str, &str)>, new_name: &str) {
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-{label}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("prelude"), tauto::nibstd::PRELUDE).unwrap();
    std::fs::write(dir.join("kernel-prelude"), KERNEL_PRELUDE).unwrap();
    let files: Vec<(String, String)> =
        files.into_iter().map(|(n, t)| (n.to_string(), t.to_string())).collect();
    let mut args = vec![
        "--navigate".to_string(),
        new_name.to_string(),
        dir.join("prelude").to_string_lossy().into_owned(),
        dir.join("kernel-prelude").to_string_lossy().into_owned(),
    ];
    for (i, (name, text)) in files.iter().enumerate() {
        std::fs::write(dir.join(name), text).unwrap();
        let path = dir.join(name).to_string_lossy().into_owned();
        args.push(if i == 0 { path } else { format!("{path}={}", i + 1) });
    }
    let rust = navigate_expected(&dir, &files, new_name);
    let out = run_tote_native("analyzer", &args, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_same_dump("analyzer-navigate", &rust, &out.stdout);
}

/// Definitions, hovers, references and renames, within a file and across
/// imports.
#[test]
fn analyzer_navigates_like_the_rust_one() {
    compare_navigate(
        "analyzer-navigate-imports",
        vec![
            (
                "a.taut",
                "pub struct Point { x: i64, y: i64 }\npub enum Shape { Dot, Circle(i64) }\npub fn origin(): Point { Point { x: 0, y: 0 } }\n",
            ),
            (
                "b.taut",
                "import \"a.taut\"\npub fn area(s: Shape): i64 {\n  match s {\n    Dot => 0\n    Circle(r) => r * r\n  }\n}\n",
            ),
            (
                "c.taut",
                "import \"b.taut\"\nfn main(): i64 {\n  let p := origin()\n  let f := (q: i64) => q + p.x\n  let pt := Point { x: 1, y: 2 }\n  match pt {\n    Point { x, y } => f(x) + area(Shape::Circle(y))\n  }\n}\n",
            ),
        ],
        "renamed",
    );
}

/// Locals, theorems, a macro call, a name the file does not declare and a
/// name a rename would capture.
#[test]
fn analyzer_navigates_one_file_like_the_rust_one() {
    compare_navigate(
        "analyzer-navigate-one",
        vec![(
            "one.taut",
            "// A file of its own.\nfn twice(n: i64): i64 {\n  let m := n + n\n  m\n}\n\nfn other(k: i64): i64 {\n  let renamed := 1\n  twice(k) + renamed + missing\n}\n\ntheorem same(): Eq(Nat, 1, 1) { Refl }\n\nfn shown(): Text { \"é😀\" }\nfn called(): i64 { twice!(1) }\n",
        )],
        "renamed",
    );
}
