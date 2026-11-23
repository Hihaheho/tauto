//! niri: lower with the Rust NIR target, run the same mono / anf /
//! ownership passes as `tauto run --backend niri`, interpret the package,
//! and compare what it prints and how it ends.
//!
//! Judgement matches `crates/tauto-niri/tests/cases.rs` for ownership ends
//! (unsupported counted; `niri.bug` names a violation kind; split/blocks must
//! agree), and matches the other backend runners for `compile_errors.niri`
//! and the shared runtime fields (`stdout`, `stderr`, `exit`, `run_error`).
//! Cases with a function of tier `O` or `M` are also run as continuations,
//! and every case as blocks, unless `NIRI_NO_BLOCKS` is set.

use tauto_niri::Outcome;
use tauto_test_suite::{RustCase, coverage::status};

fn gaps(case: &RustCase) -> Vec<&'static str> {
    let mut gaps = case.assertion_gaps();
    // niri has no case-host probe; drop order is not observed here.
    if case.probe_drops.is_some() {
        gaps.push("probe_drops");
    }
    gaps
}

fn checked(case: &RustCase, what: &str) -> String {
    let gaps = gaps(case);
    if gaps.is_empty() {
        "pass".into()
    } else {
        status("partial", &format!("{what}; {}", gaps.join("; ")))
    }
}

fn first_line(s: &str) -> String {
    let line = s.lines().next().unwrap_or("");
    let mut out = String::new();
    let mut digits = false;
    for c in line.chars() {
        if c.is_ascii_digit() {
            if !digits {
                out.push('N');
            }
            digits = true;
        } else {
            digits = false;
            out.push(c);
        }
    }
    out.replace('\t', " ").chars().take(120).collect()
}

fn declared_compile(case: &RustCase, stage: &str, message: &str) -> Option<String> {
    match case.check_limitation("niri", stage, message) {
        Ok(true) => return Some(status("todo", &format!("declared {stage}: {message}"))),
        Err(e) => return Some(status("fail", &e)),
        Ok(false) => {}
    }
    match case.check_compile_error("niri", stage, message) {
        Ok(true) => Some(checked(case, "rejection checked")),
        Err(e) => Some(status("fail", &e)),
        Ok(false) => None,
    }
}

/// Map a run to the shared runtime contract, or to an ownership/unsupported end.
fn ended(run: &tauto_niri::Run, case: &RustCase) -> String {
    match &run.outcome {
        Outcome::Ok => match case.check_output("niri", &run.stdout, "", Some(0)) {
            Ok(None) => "pass".into(),
            Ok(Some(e)) => status("todo", &format!("declared output: {e}")),
            // Keep the compare message (including a mismatched `run_error`).
            Err(e) => status("fail", &e),
        },
        Outcome::Unsupported(what) => format!("unsupported: {what}"),
        Outcome::Violation(v) => {
            format!("violation: {:?}: {}", v.kind, first_line(&v.detail))
        }
        Outcome::Error(e) => match case.check_output("niri", &run.stdout, e, Some(1)) {
            Ok(None) => "pass".into(),
            Ok(Some(x)) => status("todo", &format!("declared output: {x}")),
            // A wrong or missing `run_error` (and other output gaps) fail with
            // the shared compare text, not a counted `error:` status.
            Err(err) => status("fail", &err),
        },
    }
}

/// Whether `end` is an allowed end for this case, as in
/// `crates/tauto-niri/tests/cases.rs` plus a shared runtime `pass`.
/// The second flag is whether the case's `niri.bug` was consumed.
fn allowed(case: &RustCase, end: &str) -> (bool, bool) {
    if end.starts_with("todo:") || end.starts_with("fail:") || end.starts_with("partial:") {
        return (true, false);
    }
    if end.starts_with("split: ") {
        let known = case.niri.as_deref().is_some_and(|w| w.starts_with("split: "));
        return (known, known);
    }
    if let Some(rest) = end.strip_prefix("violation: ") {
        let kind = rest.split(':').next().unwrap_or(rest);
        let known = case
            .niri
            .as_deref()
            .and_then(|w| w.split_once(": "))
            .is_some_and(|(k, _)| k == kind);
        return (known, known);
    }
    if end == "pass" {
        return (true, false);
    }
    // `error:` is never an allowed end: matched `run_error` becomes `pass` in
    // `ended`, and a mismatch becomes `fail:` with the compare message.
    let ok = !end.starts_with("output:")
        && !end.starts_with("split:")
        && !end.starts_with("blocks:")
        && !end.starts_with("error:");
    (ok, false)
}

fn prepare(case: &RustCase) -> Result<tauto_nir::Package, String> {
    let mut pkg = match case.compile_with_files("niri") {
        Ok((pkg, _, _)) => pkg,
        Err(error) => {
            let (stage, message) = match error {
                tauto_nibcheck::lower::CompileError::Front(m)
                | tauto_nibcheck::lower::CompileError::Package(m) => ("front", m),
                tauto_nibcheck::lower::CompileError::Build(m) => ("build", m),
                tauto_nibcheck::lower::CompileError::Unsupported(u) => {
                    ("unsupported", u.what.to_string())
                }
            };
            if let Some(s) = declared_compile(case, stage, &message) {
                return Err(s);
            }
            // Undeclared front/build gaps are counted, not a suite failure.
            return Err(format!("not compiled: {stage}"));
        }
    };
    if let Err(e) = tauto_nir::mono::specialize(&mut pkg) {
        return Err(format!("mono: {}", first_line(&e)));
    }
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    Ok(pkg)
}

fn outcome(case: &RustCase) -> String {
    let pkg = match prepare(case) {
        Ok(pkg) => pkg,
        Err(s) => return s,
    };
    if let Err(e) = case.check_compiled("niri") {
        return status("fail", &e);
    }
    if !case.expects_runtime() {
        return checked(case, "compile checked");
    }
    let whole = ended(&tauto_niri::run(&pkg), case);
    if pkg.fns.iter().any(|f| f.tier >= tauto_nir::Tier::O) {
        let opts = tauto_niri::Options {
            split: true,
            ..Default::default()
        };
        let split = ended(&tauto_niri::run_with(&pkg, opts), case);
        let both_unsupported =
            split.starts_with("unsupported") && whole.starts_with("unsupported");
        if split != whole && !both_unsupported {
            return format!("split: {split} (whole: {whole})");
        }
    }
    if std::env::var_os("NIRI_NO_BLOCKS").is_some() {
        return whole;
    }
    let opts = tauto_niri::Options {
        blocks: true,
        ..Default::default()
    };
    let blocks = ended(&tauto_niri::run_with(&pkg, opts), case);
    let both_unsupported =
        blocks.starts_with("unsupported") && whole.starts_with("unsupported");
    let further = whole.starts_with("unsupported") && !blocks.starts_with("unsupported");
    if blocks != whole && !both_unsupported && !further {
        return format!("blocks: {blocks} (whole: {whole})");
    }
    whole
}

fn run_case(case: &RustCase) -> String {
    let end = outcome(case);
    // Output / compile failures already carry a `fail:` status from
    // `check_output` or `declared_compile`; keep them as-is.
    if end.starts_with("fail:") || end.starts_with("todo:") || end.starts_with("partial:") {
        return end;
    }
    let (ok, used_bug) = allowed(case, &end);
    if case.niri.is_some() && !used_bug {
        return status(
            "fail",
            &format!(
                "niri.bug {:?} no longer happens; remove the stale limitation",
                case.niri.as_deref().unwrap_or("")
            ),
        );
    }
    if !ok {
        return status("fail", &end);
    }
    if used_bug {
        return status("todo", &end);
    }
    if end == "pass" {
        return checked(case, "output checked");
    }
    // Counted gaps (unsupported, not compiled, …).
    end
}

pub fn runner(_worker: usize) -> impl FnMut(usize, &RustCase) -> String {
    move |_, case| run_case(case)
}
