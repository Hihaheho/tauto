//! Every case's NIR is checked statically (`tauto_nir::wf::check` and
//! `tauto_nir::loans::check`), as the compiler gives it and after `anf` and
//! `ownership`, without running it.
//! A finding is a compiler bug; a case says the one it has today with
//! `nir_wf.bug = "<function> <rule>: why"`.
//!
//! The cases checked are the ones whose NIR a backend is asked to give: a
//! case that runs, builds, selects the Rust backend or names a NIR finding.
//! A case that only asks what the checker says of its source (its types, its
//! diagnostics, a rejection) is a program no backend is given, and compiling
//! it takes half of the time for none of the NIR that is run;
//! `WF_EVERY_CASE=1` checks those too.
//!
//! `WF_ONLY=<part of a case name>` checks those cases alone, and
//! `WF_ALL=1` prints every finding, `WF_NIR=1` with its function as text.

use std::path::Path;

use tauto_test_suite::RustCase;

/// Whether a backend is asked for the case's NIR.
fn gives_nir(case: &RustCase) -> bool {
    case.expects_runtime()
        || case.build.is_some()
        || case.probe_drops.is_some()
        || case.extract
        || case.assertions.iter().any(|a| a == "tests")
        || case.selects_backend("rust")
        || case.niri.is_some()
        || case.nir_wf.is_some()
}

/// The findings of one case, one line each: the stage, the function and the
/// rule.
fn findings(case: &RustCase) -> Vec<(String, String)> {
    let pkg = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| case.compile("rust")));
    let Ok(Ok(mut pkg)) = pkg else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let mut add = |stage: &str, pkg: &tauto_nir::Package| {
        for (id, f) in tauto_nir::wf::check(pkg) {
            if std::env::var_os("WF_NIR").is_some() {
                let text = tauto_nir::text::print_fn(pkg, &pkg.fns[id]).unwrap_or_default();
                eprintln!("{} {stage}: {f}\n{text}", case.name);
            }
            out.push((
                format!("{stage} {} {:?}", pkg.fns[id].source, f.rule),
                f.message,
            ));
        }
        for (id, f) in tauto_nir::loans::check(pkg) {
            if std::env::var_os("WF_NIR").is_some() {
                let text = tauto_nir::text::print_fn(pkg, &pkg.fns[id]).unwrap_or_default();
                eprintln!("{} {stage}: {f}\n{text}", case.name);
            }
            out.push((
                format!("{stage} {} loans {:?}", pkg.fns[id].source, f.rule),
                f.message,
            ));
        }
    };
    add("compiled", &pkg);
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    add("lowered", &pkg);
    out.sort();
    out.dedup_by(|a, b| a.0 == b.0);
    out
}

#[test]
fn every_case_is_well_formed() {
    tauto_messages::install();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases");
    let only = std::env::var("WF_ONLY").ok();
    let every = std::env::var_os("WF_EVERY_CASE").is_some();
    let cases: Vec<RustCase> = tauto_test_suite::rust_cases(&root)
        .unwrap()
        .into_iter()
        .filter(|c| only.as_ref().is_none_or(|o| c.name.contains(o.as_str())))
        .filter(|c| every || gives_nir(c))
        .collect();
    let start = std::time::Instant::now();
    let got = tauto_test_suite::parallel_map(&cases, |_| (), |_, _, c| findings(c));
    eprintln!("{} cases checked in {:?}", cases.len(), start.elapsed());
    let all = std::env::var_os("WF_ALL").is_some();
    let mut wrong = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for (c, fs) in cases.iter().zip(&got) {
        for (key, message) in fs {
            if all {
                eprintln!("{}\t{key}\t{message}", c.name);
            }
            let known = c
                .nir_wf
                .as_deref()
                .and_then(|w| w.split_once(": "))
                .is_some_and(|(k, _)| key.ends_with(k));
            if known {
                seen.insert(c.name.as_str());
            } else {
                wrong.push(format!("{}\t{key}\t{message}", c.name));
            }
        }
    }
    if only.is_none() {
        for c in cases.iter().filter(|c| c.nir_wf.is_some()) {
            if !seen.contains(c.name.as_str()) {
                wrong.push(format!("{}: its nir_wf.bug is no longer found", c.name));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "NIR that breaks an invariant:\n{}",
        wrong.join("\n")
    );
}
