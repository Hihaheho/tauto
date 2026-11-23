//! `totes/nir` against `tauto_nir::text` (`docs/design/nir-text.md`).
//!
//! Every case that shows something is compiled to the package the backends read, before and after
//! the passes a backend runs (`mono::specialize`, `anf::normalize`,
//! `ownership::insert`). The crate prints each package as NIR text; the tote
//! reads the text and prints the package it read. The two texts are the same
//! when the tote keeps everything the text states.

use std::path::Path;

use selfhost_harness::{assert_same_dump, root, run_tote_native};

const STEPS: u64 = 2_000_000_000_000;

/// The packages of a case as NIR text: as compiled, and after the passes.
fn texts(case: &tauto_test_suite::RustCase) -> Vec<(String, String)> {
    if std::env::var_os("NIR_TRACE").is_some() {
        eprintln!("start {}", case.name);
    }
    let pkg = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| case.compile("rust")));
    let Ok(Ok(mut pkg)) = pkg else {
        return Vec::new();
    };
    let mut out = Vec::new();
    if let Ok(t) = tauto_nir::text::print(&pkg) {
        out.push((format!("{} (compiled)", case.name), t));
    }
    if tauto_nir::mono::specialize(&mut pkg).is_err() {
        return out;
    }
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    if let Ok(t) = tauto_nir::text::print(&pkg) {
        out.push((format!("{} (after the passes)", case.name), t));
    }
    out
}

/// The answers of a run of the tote, in the order of its arguments: what
/// follows each line `== FILE`.
fn sections(stdout: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for line in stdout.split_inclusive('\n') {
        if line.starts_with("== ") {
            out.push(String::new());
        } else if let Some(last) = out.last_mut() {
            last.push_str(line);
        }
    }
    out
}

fn write(dir: &Path, name: String, text: &str) -> String {
    let path = dir.join(name);
    std::fs::write(&path, text).unwrap();
    path.to_string_lossy().into_owned()
}

#[test]
fn nir_prints_what_it_reads() {
    tauto_messages::install();
    let only = std::env::var("NIR_ONLY").ok();
    let cases: Vec<_> = tauto_test_suite::rust_cases(&root().join("cases"))
        .unwrap()
        .into_iter()
        .filter(|c| only.as_ref().is_none_or(|o| c.name.contains(o.as_str())))
        // The cases a backend runs: those that show something. A case
        // named by `NIR_ONLY` is read whatever it shows.
        .filter(|c| only.is_some() || (c.stdout.is_some() && c.run_error.is_none()))
        .collect();
    let texts: Vec<(String, String)> =
        tauto_test_suite::parallel_map(&cases, |_| (), |_, _, c| texts(c))
            .into_iter()
            .flatten()
            .collect();
    assert!(!texts.is_empty(), "the crate prints no package");
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-nir-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let paths: Vec<String> = texts
        .iter()
        .enumerate()
        .map(|(i, (_, t))| write(&dir, format!("{i:05}.nir"), t))
        .collect();

    let mut args = vec!["print".to_string()];
    args.extend(paths);
    let out = run_tote_native("nir", &args, STEPS);
    assert_eq!(out.error, None, "{}", out.stderr);
    let got = sections(&out.stdout);
    assert_eq!(got.len(), texts.len(), "`nir print` answers each file");

    let (mut rust, mut tauto) = (String::new(), String::new());
    for ((name, text), printed) in texts.iter().zip(&got) {
        rust.push_str(&format!("== {name}\n{text}"));
        tauto.push_str(&format!("== {name}\n{printed}"));
    }
    assert_same_dump("nir", &rust, &tauto);
    if std::env::var_os("NIR_KEEP").is_none() {
        let _ = std::fs::remove_dir_all(&dir);
    }
}
