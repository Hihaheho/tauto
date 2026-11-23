//! `totes/lower` against the lowering of `tauto-nibcheck` and `tauto-nir`
//! (`docs/design/self-host.md`).
//!
//! The tote writes as much of a package as it can, as NIR text, and says
//! `unsupported` for a program it cannot write yet. Each program the tote
//! writes is compared with the text the Rust pipeline prints
//! (`tauto build --backend llvm --emit nir`): the part of the package the
//! tote writes, which grows with the tote. Today that is the `data` items.

use selfhost_harness::{assert_same_dump, materialize, root, run_tote_native};

const STEPS: u64 = 2_000_000_000_000;

/// The part of a package's text the tote writes: the `data` items.
fn data_items(nir: &str) -> String {
    let start = nir.find("data ").unwrap_or(nir.len());
    let rest = &nir[start..];
    let end = ["\nop ", "\nunion ", "\nextern ", "\nfn ", "\ntop ", "\nexport "]
        .iter()
        .filter_map(|m| rest.find(m))
        .min()
        .unwrap_or(rest.len());
    format!("{}\n", rest[..end].trim_end())
}

/// What the Rust pipeline prints of a case, or `None` when the case does not
/// reach NIR.
fn expected(case: &tauto_test_suite::RustCase) -> Option<String> {
    let pkg = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| case.compile("llvm")));
    let mut pkg = pkg.ok()?.ok()?;
    tauto_nir::mono::specialize(&mut pkg).ok()?;
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    tauto_nir::mono::check(&pkg).ok()?;
    let nir = tauto_nir::text::print(&pkg).ok()?;
    Some(data_items(&nir))
}

#[test]
fn lower_matches_the_crates() {
    tauto_messages::install();
    let cases: Vec<_> = tauto_test_suite::rust_cases(&root().join("cases"))
        .unwrap()
        .into_iter()
        // A case of one file: the tote reads one file.
        .filter(|c| !c.has_input() && c.imports.is_empty() && c.source_path.is_none() && !c.source.contains("import"))
        .collect();
    let answers: Vec<(String, String, String)> =
        tauto_test_suite::parallel_map(&cases, |_| (), |_, _, c| {
            expected(c).map(|nir| (c.name.clone(), c.source.clone(), nir))
        })
        .into_iter()
        .flatten()
        .collect();
    let mut inputs = vec![("prelude".to_string(), tauto::nibstd::PRELUDE.to_string())];
    inputs.extend(answers.iter().map(|(_, source, _)| ("case".to_string(), source.clone())));
    let m = materialize("lower", &inputs);
    let out = run_tote_native("lower", &m.paths, STEPS);
    assert_eq!(out.error, None, "{}", out.stderr);

    // The tote's answers, one for each case after `== PATH`.
    let mut got: Vec<String> = Vec::new();
    for line in out.stdout.split_inclusive('\n') {
        if line.starts_with("== ") {
            got.push(String::new());
        } else if let Some(last) = got.last_mut() {
            last.push_str(line);
        }
    }
    assert_eq!(got.len(), answers.len(), "the tote answers each case");
    let mut compared = 0;
    let mut differ: Vec<String> = Vec::new();
    let mut first = None;
    for ((name, _, nir), tote) in answers.iter().zip(&got) {
        if tote.starts_with("unsupported") {
            continue;
        }
        compared += 1;
        let tote = format!("{}\n", tote.trim_end());
        if *nir != tote {
            differ.push(name.clone());
            if let Ok(path) = std::env::var("LOWER_DIFFS") {
                let line = nir
                    .lines()
                    .zip(tote.lines())
                    .find(|(a, b)| a != b)
                    .map(|(a, b)| format!("{a}\n   | {b}"))
                    .unwrap_or_else(|| "lengths differ".to_string());
                use std::io::Write;
                let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap();
                writeln!(f, "{name}\n  {line}").unwrap();
            }
            first.get_or_insert_with(|| (name.clone(), nir.clone(), tote));
        }
    }
    eprintln!("{compared} of {} cases are written by the tote", answers.len());
    assert!(compared > 0, "the tote writes no case");
    if let Some((name, rust, tauto)) = first {
        eprintln!("{} cases differ: {:?}", differ.len(), &differ[..differ.len().min(30)]);
        assert_same_dump("lower", &format!("== {name}\n{rust}"), &format!("== {name}\n{tauto}"));
    }
}
