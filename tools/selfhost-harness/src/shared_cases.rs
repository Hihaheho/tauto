//! Execute shared expectations through Tauto component programs.
//!
//! Rust functions below produce differential reference reports only. They never
//! supply an actual selfhost observation. Unimplemented whole-pipeline stages
//! stay incomplete even when a component comparison passes.
use std::{
    collections::{BTreeMap, BTreeSet},
    path::Path,
};
use tauto_test_suite::selfhost::{
    self, Actual, Backend, Contract, Implementation, Observation, Value, Verdict,
};

#[derive(Debug)]
pub struct CaseExecution {
    pub name: String,
    pub observations: Vec<Observation>,
    pub artifacts: BTreeMap<String, String>,
    pub verdict: Verdict,
}

/// Decode a batch without dropping missing, duplicated, or unexpected records.
/// An empty report is valid for a checker with no diagnostics, but only after its
/// exact file header was observed.
pub fn split_reports(output: &str, paths: &[String]) -> Result<Vec<String>, String> {
    let expected: BTreeSet<_> = paths.iter().collect();
    if expected.len() != paths.len() {
        return Err("duplicate requested component path".into());
    }
    let mut reports = BTreeMap::new();
    let mut current: Option<String> = None;
    for line in output.split_inclusive('\n') {
        if let Some(path) = line.strip_prefix("== ").and_then(|s| s.strip_suffix('\n')) {
            if !expected.contains(&path.to_string()) {
                return Err(format!("unexpected component path {path}"));
            }
            if reports.insert(path.to_string(), String::new()).is_some() {
                return Err(format!("duplicate component output {path}"));
            }
            current = Some(path.to_string());
        } else {
            let path = current
                .as_ref()
                .ok_or("component output precedes its first file header")?;
            reports.get_mut(path).unwrap().push_str(line);
        }
    }
    paths
        .iter()
        .map(|p| {
            reports
                .remove(p)
                .ok_or_else(|| format!("missing component output {p}"))
        })
        .collect()
}

/// Even a complete-looking report is unusable after a failed or interrupted
/// process. Status is checked before output framing or semantic comparisons.
pub fn component_reports(
    name: &str,
    output: &crate::RunOutput,
    paths: &[String],
) -> Result<Vec<String>, String> {
    if let Some(error) = &output.error {
        return Err(error.clone());
    }
    if output.exit != Some(0) || !output.stderr.is_empty() {
        return Err(format!(
            "{name}: exit {:?}, stderr {:?}",
            output.exit, output.stderr
        ));
    }
    split_reports(&output.stdout, paths)
}

fn canonical_variables(dump: &str) -> String {
    let mut names = BTreeMap::new();
    let mut out = String::new();
    let mut rest = dump;
    while let Some(at) = rest.find("Var(") {
        out.push_str(&rest[..at + 4]);
        rest = &rest[at + 4..];
        let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
        if digits > 0 && rest.as_bytes().get(digits) == Some(&b')') {
            let next = names.len();
            let id = *names.entry(rest[..digits].to_owned()).or_insert(next);
            out.push_str(&id.to_string());
            rest = &rest[digits..];
        }
    }
    out.push_str(rest);
    out
}
/// A reference crash is a harness failure, never a language rejection. This
/// wrapper is also used for the bootstrap oracle's legitimate early failures:
/// they are reported as unavailable, not turned into a common placeholder result.
fn guarded_reference(f: impl FnOnce() -> Result<String, Actual>) -> Result<String, Actual> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).unwrap_or_else(|_| {
        Err(Actual::HarnessFailure(
            "bootstrap reference panicked".into(),
        ))
    })
}
fn reference(mode: &str, source: &str) -> Result<String, Actual> {
    guarded_reference(|| {
        let earlier = || {
            Actual::Unsupported(format!(
                "bootstrap {mode} reference failed before a stage-specific report"
            ))
        };
        match mode {
            "syntax" => {
                let p = tauto_parol::parse(source);
                Ok(if p.is_ok() {
                    p.cst.dump()
                } else {
                    "error\n".into()
                })
            }
            "fmt" => tauto::fmt::format(source).map_err(|_| earlier()),
            "types" => tauto::surface::parse_program_as_written(source)
                .map(|p| tauto::types::dump_types(&tauto::types::check_program(&p)))
                .map_err(|_| earlier()),
            "rows" => tauto::surface::parse_program_as_written(source)
                .map(|p| tauto::rows::dump_rows(&tauto::rows::check_program_rows(&p)))
                .map_err(|_| earlier()),
            "lin" => tauto::surface::parse_program_as_written(source)
                .map_err(|_| earlier())
                .and_then(|p| tauto::lin::check_lin_program(&p).map_err(|_| earlier()))
                .map(|r| tauto::lin::dump_lin(&r)),
            _ => Err(Actual::HarnessFailure("unknown reference mode".into())),
        }
    })
}

/// Equality is meaningful only after both reports establish the requested
/// component stage. The nibcheck/formatter bare error has ambiguous provenance.
pub fn differential_report(mode: &str, reference: Result<String, Actual>, report: &str) -> Actual {
    let expected = match reference {
        Ok(r) => r,
        Err(failure) => return failure,
    };
    for (side, text) in [("reference", expected.as_str()), ("actual", report)] {
        let status = match mode {
            "syntax" => parse_result(text),
            "types" | "rows" | "lin" if text == "error\n" => {
                return Actual::Unsupported(format!(
                    "{side} {mode} report is an opaque earlier-stage error"
                ));
            }
            "types" | "rows" | "lin" => checker_status(mode, text),
            "fmt" => format_result(text),
            _ => return Actual::HarnessFailure("unknown differential mode".into()),
        };
        if matches!(status, Actual::HarnessFailure(_) | Actual::Unsupported(_)) {
            return status;
        }
    }
    Actual::Differential {
        reference: if mode == "types" {
            canonical_variables(&expected)
        } else {
            expected
        },
        actual: if mode == "types" {
            canonical_variables(report)
        } else {
            report.into()
        },
    }
}

pub fn format_result(report: &str) -> Actual {
    if report == "error\n" {
        Actual::Unsupported(
            "formatter output is ambiguous between formatted source and an unclassified failure"
                .into(),
        )
    } else if report.starts_with("cannot read: ") {
        Actual::HarnessFailure("formatter could not read its input".into())
    } else {
        Actual::Value(Value::Text(report.into()))
    }
}

#[cfg(test)]
mod reference_tests {
    #[test]
    fn a_reference_panic_is_not_a_language_diagnostic() {
        assert!(matches!(
            super::guarded_reference(|| panic!("oracle failed")),
            Err(tauto_test_suite::selfhost::Actual::HarnessFailure(_))
        ));
    }
}
/// A transport failure or unknown report cannot masquerade as checker success.
pub fn checker_status(mode: &str, report: &str) -> Actual {
    if !["types", "rows", "lin"].contains(&mode) {
        return Actual::HarnessFailure("unknown checker mode".into());
    }
    if report == "error\n" {
        return Actual::HarnessFailure("component rejected before a stage-specific diagnostic; cannot satisfy an expected checker error".into());
    }
    if !report.is_empty() && !report.ends_with('\n') {
        return Actual::HarnessFailure("unterminated checker report".into());
    }
    let mut first_error = None;
    for line in report.lines() {
        if let Some(rest) = line.strip_prefix("error ") {
            let mut parts = rest.splitn(3, ' ');
            let start = parts.next().and_then(|x| x.parse::<u32>().ok());
            let end = parts.next().and_then(|x| x.parse::<u32>().ok());
            let message = parts.next();
            match (start, end, message) {
                (Some(a), Some(b), Some(m)) if a <= b && !m.is_empty() => {
                    if first_error.is_none() {
                        first_error = Some(m.to_string());
                    }
                }
                _ => return Actual::HarnessFailure("malformed checker diagnostic".into()),
            }
        } else {
            let allowed: &[&str] = match mode {
                "types" => &[
                    "let ", "local ", "term ", "width ", "quant ", "data ", "ctor ",
                ],
                "rows" => &["function ", "call ", "quant "],
                "lin" => &[],
                _ => return Actual::HarnessFailure("unknown checker mode".into()),
            };
            if !allowed.iter().any(|prefix| {
                line.strip_prefix(prefix)
                    .is_some_and(|r| !r.trim().is_empty())
            }) {
                return Actual::HarnessFailure(format!("unknown checker report line: {line:?}"));
            }
        }
    }
    first_error
        .map(Actual::Rejected)
        .unwrap_or(Actual::Accepted)
}

pub fn parse_result(report: &str) -> Actual {
    if report == "error\n" {
        return Actual::Value(Value::Bool(false));
    }
    if report.is_empty() || !report.ends_with('\n') {
        return Actual::HarnessFailure("missing or truncated syntax report".into());
    }
    let mut previous_depth = 0u32;
    for (index, line) in report.lines().enumerate() {
        let fields = line.split(' ').collect::<Vec<_>>();
        if fields.len() != 4 {
            return Actual::HarnessFailure("malformed syntax report".into());
        }
        let depth = fields[0].parse::<u32>();
        let start = fields[2].parse::<u32>();
        let end = fields[3].parse::<u32>();
        match (depth, start, end) {
            (Ok(d), Ok(a), Ok(b))
                if a <= b
                    && !fields[1].is_empty()
                    && ((index == 0 && d == 0 && fields[1] == "Program")
                        || (index > 0 && d > 0 && d <= previous_depth.saturating_add(1))) =>
            {
                previous_depth = d
            }
            _ => return Actual::HarnessFailure("malformed syntax tree record".into()),
        }
    }
    Actual::Value(Value::Bool(true))
}

fn wants(case: &Contract, backend: Backend, mode: &str) -> bool {
    case.requirements(backend)
        .iter()
        .any(|r| match (mode, r.name.as_str()) {
            ("syntax", "parses")
            | ("fmt", "format" | "format_error")
            | ("types", "types" | "inferred_types")
            | ("rows", "rows" | "inferred_rows")
            | ("lin", "lin") => true,
            (_, "differential") => r.expected.text() == Some(mode),
            _ => false,
        })
}
fn observation(requirement: &str, stage: &str, backend: Backend, actual: Actual) -> Observation {
    Observation {
        requirement: requirement.into(),
        stage: stage.into(),
        implementation: Implementation::Tauto,
        compiler_backend: backend,
        target_backend: None,
        actual,
    }
}

/// The explicit root prevents a cached dependency with a compiled-in old
/// manifest directory from quietly validating another checkout's inputs.
/// Only the selected cases are run, but every requirement of each selected case
/// remains in the final verdict; selecting a component never hides other stages.
pub fn run(
    case_root: &Path,
    backend: Backend,
    target: Backend,
    filter: &str,
    modes: &[String],
) -> Result<Vec<CaseExecution>, String> {
    let root = case_root.canonicalize().map_err(|e| e.to_string())?;
    let compiler_root = crate::root().canonicalize().map_err(|e| e.to_string())?;
    if root != compiler_root.join("cases") {
        return Err(format!(
            "case root {} differs from compiled harness root {}; rebuild the path-sensitive harness",
            root.display(),
            compiler_root.display()
        ));
    }
    let configured = std::env::var("TAUTO_SELFHOST_BACKEND").unwrap_or_else(|_| "rust".into());
    if configured != backend.name() {
        return Err(format!(
            "requested {} but TAUTO_SELFHOST_BACKEND selects {configured}",
            backend.name()
        ));
    }
    if modes.iter().collect::<BTreeSet<_>>().len() != modes.len() {
        return Err("duplicate component selection".into());
    }
    if modes
        .iter()
        .any(|s| !["syntax", "fmt", "types", "rows", "lin", "rustgen"].contains(&s.as_str()))
    {
        return Err("unknown component adapter".into());
    }
    let cases = selfhost::contracts(&root)?
        .into_iter()
        .filter(|c| c.name.contains(filter))
        .collect::<Vec<_>>();
    if cases.is_empty() {
        return Err("case filter selected no contracts".into());
    }
    let mut observations: Vec<Vec<Observation>> = vec![Vec::new(); cases.len()];
    let mut artifacts = vec![BTreeMap::new(); cases.len()];
    for mode in modes {
        if mode == "rustgen" {
            let mut adapter = crate::shared_rustgen::Adapter::new()?;
            for ((case, observed), artifact) in
                cases.iter().zip(&mut observations).zip(&mut artifacts)
            {
                if (case.text("selfhost_entry").is_some()
                    || case.text("load_error").is_some()
                    || case.text("macro_error").is_some())
                    && !case.excluded(target)
                {
                    observed.extend(adapter.observe(case, backend, target));
                    *artifact = adapter.artifacts();
                }
            }
            continue;
        }
        let mut inputs = Vec::new();
        let mut selected = Vec::new();
        for (index, case) in cases.iter().enumerate() {
            if !wants(case, target, mode) {
                continue;
            }
            match case.single_source() {
                Ok(Some(source)) => {
                    selected.push(index);
                    inputs.push((case.name.clone(), source));
                }
                Ok(None) => {} // All unsupplied requirements remain Incomplete below.
                Err(error) => {
                    for r in case.requirements(target) {
                        observations[index].push(observation(
                            &r.name,
                            &r.stage,
                            backend,
                            Actual::HarnessFailure(format!("reading input: {error}")),
                        ));
                    }
                }
            }
        }
        if selected.is_empty() {
            continue;
        }
        let prelude = ["types", "rows", "lin"].contains(&mode.as_str());
        let mut material = Vec::new();
        if prelude {
            material.push(("prelude".into(), tauto::nibstd::PRELUDE.into()));
        }
        material.extend(inputs.iter().cloned());
        let files = crate::materialize(&format!("shared-{mode}-{}", backend.name()), &material);
        let mut args = Vec::new();
        if prelude {
            args.push(format!("--{mode}"));
        }
        args.extend(files.paths.iter().cloned());
        let tote = if prelude { "nibcheck" } else { mode.as_str() };
        let output = crate::run_tote_native(tote, &args, 200_000_000_000);
        let reports = component_reports(tote, &output, &files.paths[usize::from(prelude)..]);
        for ((index, (_, source)), position) in selected.iter().zip(&inputs).zip(0..) {
            for r in cases[*index].requirements(target) {
                let actual = match &reports {
                    Err(error) if r.name == "differential" && r.expected.text() == Some(mode) => {
                        Some(Actual::HarnessFailure(error.clone()))
                    }
                    Err(error)
                        if r.stage == *mode
                            || (mode == "syntax" && r.name == "parses")
                            || (mode == "fmt" && r.stage == "format") =>
                    {
                        Some(
                            if error.contains("safety limit") || error.contains("timed out") {
                                Actual::Timeout(error.clone())
                            } else {
                                Actual::HarnessFailure(error.clone())
                            },
                        )
                    }
                    Err(_) => None,
                    Ok(reports) => {
                        let report = &reports[position];
                        if r.name == "differential" && r.expected.text() == Some(mode) {
                            Some(differential_report(mode, reference(mode, source), report))
                        } else {
                            match (mode.as_str(),r.name.as_str()){
                            ("syntax","parses")=>Some(parse_result(report)),
                            ("fmt","format")=>Some(format_result(report)),
                            ("fmt","format_error")=>Some(Actual::Unsupported("formatter command does not expose its error message; bare error is insufficient".into())),
                            ("types","types")|("rows","rows")|("lin","lin")=>Some(checker_status(mode, report)),
                            ("types", "inferred_types") | ("rows", "inferred_rows") => Some(inferred_values(mode, report, &r.expected)),
                            _=>None,
                        }
                        }
                    }
                };
                if let Some(actual) = actual {
                    observations[*index].push(observation(&r.name, &r.stage, backend, actual));
                }
            }
        }
        let _ = std::fs::remove_dir_all(files.dir);
    }
    Ok(cases
        .into_iter()
        .zip(observations)
        .zip(artifacts)
        .map(|((case, observations), artifacts)| CaseExecution {
            name: case.name.clone(),
            verdict: selfhost::assess_route(&case, backend, target, &observations),
            observations,
            artifacts,
        })
        .collect())
}

/// File-content identity accompanies the actual run, not a commit label inferred
/// from a mutable checkout. The caller compares it again after execution.
pub fn input_identity(case_root: &Path, filter: &str) -> Result<serde_json::Value, String> {
    fn files(dir: &Path, out: &mut Vec<std::path::PathBuf>) -> Result<(), String> {
        for entry in std::fs::read_dir(dir).map_err(|e| e.to_string())? {
            let path = entry.map_err(|e| e.to_string())?.path();
            if path.is_symlink() {
                return Err(format!("identity input is a symlink: {}", path.display()));
            }
            if path.is_dir() {
                if !["target", "build", ".git", ".tauto-native", ".tools"]
                    .contains(&path.file_name().unwrap().to_str().unwrap_or(""))
                {
                    files(&path, out)?;
                }
            } else if path
                .file_name()
                .is_some_and(|n| n == "Cargo.toml" || n == "Cargo.lock")
                || path.extension().is_some_and(|e| {
                    [
                        "taut", "tauto", "nib", "eure", "rs", "js", "mjs", "par", "tables", "txt",
                    ]
                    .iter()
                    .any(|x| e == *x)
                })
            {
                out.push(path);
            }
        }
        Ok(())
    }
    fn digest(path: &Path) -> Result<String, String> {
        std::fs::read(path)
            .map(|b| tauto_syntax::sha256_hex(&b))
            .map_err(|e| format!("{}: {e}", path.display()))
    }
    let root = crate::root().canonicalize().map_err(|e| e.to_string())?;
    let mut paths = vec![root.join("Cargo.toml"), root.join("Cargo.lock")];
    for dir in ["crates", "tools/selfhost-harness", "std", "meta", "totes"] {
        files(&root.join(dir), &mut paths)?;
    }
    paths.sort();
    paths.dedup();
    let compiler = paths
        .iter()
        .map(|p| {
            Ok((
                p.strip_prefix(&root)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned(),
                digest(p)?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    let mut combined = tauto_syntax::Sha256::new();
    for (path, hash) in &compiler {
        combined.update(&(path.len() as u64).to_le_bytes());
        combined.update(path.as_bytes());
        combined.update(hash.as_bytes());
    }
    let mut selected = BTreeMap::new();
    for case in selfhost::contracts(case_root)?
        .into_iter()
        .filter(|c| c.name.contains(filter))
    {
        let raw_source = case
            .single_source()
            .ok()
            .flatten()
            .map(|s| tauto_syntax::sha256_hex(s.as_bytes()));
        let prepared = match crate::shared_rustgen::prepare_case(&case) {
            Ok(input) => serde_json::json!({"artifacts":input.artifacts()?}),
            Err(Actual::Unsupported(reason)) => serde_json::json!({"incomplete":reason}),
            Err(Actual::HarnessFailure(reason)) => serde_json::json!({"input_error":reason}),
            Err(other) => {
                return Err(format!(
                    "unexpected input materialization result: {other:?}"
                ));
            }
        };
        selected.insert(case.name, serde_json::json!({"case_file_sha256":digest(&case.file)?,"single_source_sha256":raw_source,"raw_input":prepared}));
    }
    let executable = std::env::current_exe().map_err(|e| e.to_string())?;
    Ok(
        serde_json::json!({"compiler_source_tree_sha256":combined.finish_hex(),"compiler_input_files":compiler,"selected_cases":selected,"runner_executable_sha256":digest(&executable)?}),
    )
}

/// Project values emitted by the Tauto checker. The expected map supplies only
/// selectors; neither its values nor bootstrap inference supply observations.
pub fn inferred_values(mode: &str, report: &str, requested: &Value) -> Actual {
    if let failure @ Actual::HarnessFailure(_) = checker_status(mode, report) {
        return failure;
    }
    let Value::Map(names) = requested else {
        return Actual::HarnessFailure("inferred contract is not a map".into());
    };
    let prefix = match mode {
        "types" => "let ",
        "rows" => "function ",
        _ => return Actual::HarnessFailure("unknown inference mode".into()),
    };
    let mut found = BTreeMap::new();
    for name in names.keys() {
        let matches = report
            .lines()
            .filter_map(|line| line.strip_prefix(prefix)?.split_once(' '))
            .filter(|(n, _)| *n == name)
            .map(|(_, v)| v)
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Actual::HarnessFailure(format!(
                "inferred {name}: expected one reported binding/function, got {}",
                matches.len()
            ));
        }
        let value = if mode == "types" {
            Value::Text(matches[0].into())
        } else {
            let Some(row) = matches[0]
                .strip_prefix('{')
                .and_then(|s| s.strip_suffix('}'))
            else {
                return Actual::HarnessFailure("malformed inferred row".into());
            };
            Value::Array(if row.is_empty() {
                Vec::new()
            } else {
                row.split(", ").map(|s| Value::Text(s.into())).collect()
            })
        };
        found.insert(name.clone(), value);
    }
    Actual::Value(Value::Map(found))
}
