//! Import acceptance is distinct from full compiler self-hosting. The source
//! bundle contains original files, including proofs and unsupported constructs.
use selfhost_harness::{run_tote_native, source_bundle::source_bundle};
use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"))
            .canonicalize()
            .unwrap()
            .join(format!(
                "tauto-graph-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, id: &str, source: &str) {
        let path = self.0.join(id);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }
    fn run(&self, wire: &str, mode: &str, module: &str) -> selfhost_harness::RunOutput {
        fs::write(self.0.join("input.bundle"), wire).unwrap();
        let mut args = vec![
            mode.into(),
            self.0.join("input.bundle").to_string_lossy().into_owned(),
            module.into(),
        ];
        if mode == "--bundle" {
            args.push("main".into());
        }
        run_tote_native("rustgen", &args, 200_000_000_000)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn wire(files: &[(&str, &str)]) -> String {
    let mut out = format!("TAUTO-SOURCES-1\n{}\n", files.len());
    for (id, contents) in files {
        out += &format!("{}\n{}\n{}{}\n", id.len(), contents.len(), id, contents);
    }
    out
}
fn success(out: selfhost_harness::RunOutput) -> String {
    assert!(out.error.is_none(), "{out:?}");
    assert_eq!(out.exit, Some(0), "{out:?}");
    assert!(out.stderr.is_empty(), "{out:?}");
    out.stdout
}
fn reject(s: &Scratch, bundle: &str, mode: &str, entry: &str, expected: &str) {
    let out = s.run(bundle, mode, entry);
    assert!(out.error.is_none(), "{out:?}");
    assert_eq!(out.exit, Some(1), "{out:?}");
    assert!(
        out.stdout.is_empty(),
        "failed generation emitted partial output: {out:?}"
    );
    assert!(out.stderr.contains(expected), "{out:?}");
}

fn execute(s: &Scratch, code: &str) -> String {
    s.write("generated/src/main.rs", code);
    s.write("generated/Cargo.toml", &format!(
        "[package]\nname = \"tauto-import-acceptance\"\nversion = \"0.0.0\"\nedition = \"2024\"\n[dependencies]\ntauto-rt = {{ path = {:?} }}\n[workspace]\n", selfhost_harness::root().join("crates/tauto-rt")));
    fs::remove_file(s.0.join("input.bundle")).unwrap();
    let run = std::process::Command::new(env!("CARGO"))
        // Each generated host uses the same package name but different source,
        // so final artifacts stay per test. Intermediate output is shared:
        // Cargo keys each unit by package path, and `tauto-rt` is then built
        // once instead of once per test.
        .current_dir(s.0.join("generated"))
        .env("CARGO_TARGET_DIR", s.0.join("target"))
        .env(
            "CARGO_BUILD_BUILD_DIR",
            std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("bootstrap-graph-build"),
        )
        .args(["run", "--offline", "--quiet"])
        .output()
        .unwrap();
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    String::from_utf8(run.stdout).unwrap()
}

#[test]
fn portable_bundle_is_sorted_and_keeps_source_bytes() {
    let a = Scratch::new();
    let b = Scratch::new();
    for dir in [&a, &b] {
        dir.write(
            "z.taut",
            r#"fn z(): Text { "日本語" }
"#,
        );
        dir.write(
            "sub/a.taut",
            r#"import "../z.taut"
fn main(): Text { z() }
"#,
        );
    }
    let packed = source_bundle(&a.0).unwrap();
    assert_eq!(packed, source_bundle(&b.0).unwrap());
    assert!(packed.contains("日本語"));
    assert!(!packed.contains(a.0.to_str().unwrap()));
    let graph = success(a.run(&packed, "--graph", "sub/a.taut"));
    let dependency_len = fs::read(a.0.join("z.taut")).unwrap().len();
    let entry_len = fs::read(a.0.join("sub/a.taut")).unwrap().len();
    assert_eq!(
        graph,
        format!(
            "z.taut\t0\t{dependency_len}\nsub/a.taut\t{}\t{}\n",
            dependency_len + 1,
            dependency_len + 1 + entry_len
        )
    );
    let code = success(a.run(&packed, "--bundle", "sub/a.taut"));
    assert_eq!(code, success(b.run(&packed, "--bundle", "sub/a.taut")));
    assert_eq!(execute(&a, &code).trim(), "日本語");
}

#[test]
fn diamond_imports_are_dependency_ordered_and_deduplicated() {
    let s = Scratch::new();
    let files = [
        (
            "main.taut",
            r#"import "left.taut"
import "right.taut"
fn main(): i64 { left() + right() }
"#,
        ),
        (
            "left.taut",
            r#"import "shared.taut"
fn left(): i64 { r#shared() }
"#,
        ),
        (
            "right.taut",
            r#"import "./shared.taut"
fn right(): i64 { r#shared() }
"#,
        ),
        (
            "shared.taut",
            r#"fn r#shared(): i64 { 21 }
"#,
        ),
    ];
    let bundle = wire(&files);
    let graph = success(s.run(&bundle, "--graph", "main.taut"));
    assert_eq!(
        graph
            .lines()
            .map(|l| l.split('\t').next().unwrap())
            .collect::<Vec<_>>(),
        ["shared.taut", "left.taut", "right.taut", "main.taut"]
    );
    let code = success(s.run(&bundle, "--bundle", "main.taut"));
    assert_eq!(execute(&s, &code).trim(), "42");
    let reversed = wire(&files.into_iter().rev().collect::<Vec<_>>());
    assert_eq!(code, success(s.run(&reversed, "--bundle", "./main.taut")));
}

#[test]
fn errors_do_not_discard_imports_or_proofs() {
    let s = Scratch::new();
    reject(
        &s,
        &wire(&[
            ("a.taut", r#"import "b.taut""#),
            ("b.taut", r#"import "a.taut""#),
        ]),
        "--graph",
        "a.taut",
        "import cycle",
    );
    reject(
        &s,
        &wire(&[("a.taut", r#"import "missing.taut""#)]),
        "--graph",
        "a.taut",
        "missing bundle module",
    );
    for path in ["../outside.taut", "/outside.taut", "C:/outside.taut"] {
        reject(
            &s,
            &wire(&[("a.taut", &format!("import {path:?}"))]),
            "--graph",
            "a.taut",
            "path",
        );
    }
    // A proof-bearing file must not become an apparently successful stripped
    // bootstrap input. The loader preserves it for the backend to reject.
    reject(
        &s,
        &wire(&[(
            "a.taut",
            r#"theorem retained(): Eq(Nat, 0, 0) { Refl(Nat, 0) }
fn main(): i64 { 0 }
"#,
        )]),
        "--bundle",
        "a.taut",
        "unsupported declaration: StTheorem",
    );
}

#[test]
fn malformed_bundle_is_rejected() {
    let s = Scratch::new();
    for (bundle, message) in [
        ("BAD\n0\n".into(), "unknown source bundle"),
        ("TAUTO-SOURCES-1\n0\nextra".into(), "trailing"),
        (wire(&[("a.taut", ""), ("a.taut", "")]), "duplicate"),
        (wire(&[("./a.taut", "")]), "noncanonical"),
        ("TAUTO-SOURCES-1\n1\n1\n0\nあ\n".into(), "boundary"),
        ("TAUTO-SOURCES-1\n4097\n".into(), "too many"),
    ] {
        reject(&s, &bundle, "--graph", "a.taut", message);
    }
}

#[cfg(unix)]
#[test]
fn host_boundary_rejects_symlinks() {
    let s = Scratch::new();
    let other = Scratch::new();
    other.write("secret.taut", r#"fn hidden(): i64 { 1 }"#);
    std::os::unix::fs::symlink(&other.0, s.0.join("escape")).unwrap();
    assert!(
        source_bundle(&s.0)
            .unwrap_err()
            .to_string()
            .contains("symlink")
    );
}

#[test]
fn compiler_import_graph_matches_host_without_rewriting_sources() {
    fn copy_sources(from: &std::path::Path, to: &std::path::Path) {
        fs::create_dir_all(to).unwrap();
        for entry in fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            if entry.file_type().unwrap().is_dir() {
                copy_sources(&entry.path(), &to.join(entry.file_name()));
            } else if tauto::program::is_source_file(&entry.path()) {
                fs::copy(entry.path(), to.join(entry.file_name())).unwrap();
            }
        }
    }
    let s = Scratch::new();
    let root = selfhost_harness::root().canonicalize().unwrap();
    // Enumerate all source files, not a graph pre-resolved by the host. The
    // independent host load below is only the comparison oracle.
    for dir in ["totes", "std"] {
        copy_sources(&root.join(dir), &s.0.join(dir));
    }
    let bundle = source_bundle(&s.0).unwrap();
    let entry = "totes/rustgen/src/main.taut";
    let host = tauto::program::load(&root.join(entry)).unwrap();
    let expected: String = host
        .files
        .iter()
        .map(|file| {
            format!(
                "{}\t{}\t{}\n",
                match file.path.strip_prefix(tauto::stdlib::ROOT) {
                    // A standard library file is read from inside tauto; the
                    // bundle holds the same text under `std/`.
                    Ok(rel) => Path::new("std").join(rel).to_string_lossy().into_owned(),
                    Err(_) => file
                        .path
                        .canonicalize()
                        .unwrap()
                        .strip_prefix(&root)
                        .unwrap()
                        .to_string_lossy()
                        .into_owned(),
                },
                file.base,
                file.base as usize + file.text.len()
            )
        })
        .collect();
    let graph = success(s.run(&bundle, "--graph", entry));
    assert_eq!(graph, expected);
    assert!(graph.contains("totes/rustgen/src/loader.taut\t"));
    assert!(graph.contains("totes/surface/src/surface.taut\t"));
    // Import closure does not imply a stage1 -> stage2 fixed point. In
    // particular, original proof declarations and generic data remain intact.
    let out = s.run(&bundle, "--bundle", entry);
    assert!(out.error.is_none(), "{out:?}");
    assert_eq!(
        out.exit,
        Some(1),
        "full compiler unexpectedly accepted: {out:?}"
    );
    assert!(out.stdout.is_empty());
    assert!(
        !out.stderr.contains("StImport"),
        "loader failed to consume imports: {out:?}"
    );
    eprintln!(
        "compiler graph accepted; compilation blocker: {}",
        out.stderr.trim()
    );
}

#[test]
fn bundle_command_refuses_to_overwrite_existing_input() {
    let s = Scratch::new();
    s.write("src/main.taut", r#"fn main(): i64 { 42 }"#);
    let output = s.0.join("sources.bundle");
    let run = || {
        std::process::Command::new(env!("CARGO_BIN_EXE_source-bundle"))
            .arg(s.0.join("src"))
            .arg(&output)
            .output()
            .unwrap()
    };
    let first = run();
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let bytes = fs::read(&output).unwrap();
    assert!(!run().status.success());
    assert_eq!(bytes, fs::read(&output).unwrap());
}
