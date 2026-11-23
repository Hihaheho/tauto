//! `totes/nir` lowers a function to blocks (`nir-text.md` "Blocks") as
//! `tauto_nir::blocks` does.
//!
//! Every case that shows something is compiled to the package the backends
//! read and put in A-normal form, with and without its drops written. The
//! crate prints each package as NIR text, and each function of it as blocks
//! (`blocks::print`). The tote reads the package text, lowers each function
//! itself and prints it as blocks (`nir blocks`). The two texts are the same
//! when the tote makes the blocks the crate does.
//!
//! `NIR_ONLY=<filter>` runs the cases whose name contains the filter;
//! `NIR_KEEP` keeps the files the tote reads; `NIR_DUMP=<dir>` writes the two
//! texts compared.

use std::path::Path;

use selfhost_harness::{assert_same_dump, root, run_tote_native};

const STEPS: u64 = 2_000_000_000_000;

/// A package as text, and the blocks of each of its functions as the crate
/// prints them, each followed by a line.
fn texts(case: &tauto_test_suite::RustCase) -> Vec<(String, String, String)> {
    if std::env::var_os("NIR_TRACE").is_some() {
        eprintln!("start {}", case.name);
    }
    let pkg = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| case.compile("rust")));
    let Ok(Ok(mut pkg)) = pkg else {
        return Vec::new();
    };
    let mut out = Vec::new();
    if tauto_nir::mono::specialize(&mut pkg).is_err() {
        return out;
    }
    for form in ["anf", "anf+drops"] {
        tauto_nir::anf::normalize(&mut pkg);
        if form == "anf+drops" {
            tauto_nir::ownership::insert(&mut pkg);
        }
        let Ok(text) = tauto_nir::text::print(&pkg) else {
            continue;
        };
        let mut blocks = String::new();
        let mut complete = true;
        for f in &pkg.fns {
            let bf = tauto_nir::blocks::lower_body(&f.body, f.tier);
            match tauto_nir::blocks::print(&pkg, f, &bf) {
                Ok(t) => {
                    blocks.push_str(&t);
                    blocks.push('\n');
                }
                Err(_) => complete = false,
            }
        }
        if complete {
            out.push((format!("{} ({form})", case.name), text, blocks));
        }
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
fn nir_lowers_to_the_blocks_the_crate_makes() {
    tauto_messages::install();
    let only = std::env::var("NIR_ONLY").ok();
    let cases: Vec<_> = tauto_test_suite::rust_cases(&root().join("cases"))
        .unwrap()
        .into_iter()
        .filter(|c| only.as_ref().is_none_or(|o| c.name.contains(o.as_str())))
        .filter(|c| only.is_some() || (c.stdout.is_some() && c.run_error.is_none()))
        .collect();
    // The same source compiles to the same packages: the first case written
    // with it stands for the others.
    let mut seen = std::collections::HashSet::new();
    let cases: Vec<_> = cases
        .into_iter()
        .filter(|c| c.compiled_source().is_none_or(|s| seen.insert(s)))
        .collect();
    let texts: Vec<(String, String, String)> =
        tauto_test_suite::parallel_map(&cases, |_| (), |_, _, c| texts(c))
            .into_iter()
            .flatten()
            .collect();
    assert!(!texts.is_empty(), "the crate prints no package");
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-nir-blocks-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let paths: Vec<String> = texts
        .iter()
        .enumerate()
        .map(|(i, (_, t, _))| write(&dir, format!("{i:05}.nir"), t))
        .collect();

    let mut args = vec!["blocks".to_string()];
    args.extend(paths);
    let out = run_tote_native("nir", &args, STEPS);
    assert_eq!(out.error, None, "{}", out.stderr);
    let got = sections(&out.stdout);
    assert_eq!(got.len(), texts.len(), "`nir blocks` answers each file");

    let (mut rust, mut tauto) = (String::new(), String::new());
    for ((name, _, blocks), made) in texts.iter().zip(&got) {
        rust.push_str(&format!("== {name}\n{blocks}"));
        tauto.push_str(&format!("== {name}\n{made}"));
    }
    if let Some(to) = std::env::var_os("NIR_DUMP") {
        let to = std::path::PathBuf::from(to);
        std::fs::create_dir_all(&to).unwrap();
        std::fs::write(to.join("rust.txt"), &rust).unwrap();
        std::fs::write(to.join("tauto.txt"), &tauto).unwrap();
    }
    assert_same_dump("nir-blocks", &rust, &tauto);
    if std::env::var_os("NIR_KEEP").is_none() {
        let _ = std::fs::remove_dir_all(&dir);
    }
}
