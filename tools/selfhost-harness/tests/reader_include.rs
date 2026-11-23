//! Source-reader substitution is not user macro evaluation or compiler completion.
use selfhost_harness::{RunOutput, root, run_tote_native, source_bundle::BundlePlan};
use std::{collections::BTreeMap, fs, path::PathBuf};
use tauto::surface::{SurfaceTerm, TermKind, dump::dump_program, walk};
use tauto_parse::{parse_program_unresolved_at};

const CASES: &str = "selfhost-reader-include.eure";
const DATA: &str = "日本語\r\n\0\"\\\nlast";
struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let path = std::env::temp_dir().canonicalize().unwrap().join(format!(
            "tauto-reader-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn run(&self, plan: &BundlePlan, reader: bool) -> RunOutput {
        let path = self.0.join("input.bundle");
        fs::write(&path, plan.encode().unwrap()).unwrap();
        let mut args = vec![
            if reader {
                "--contract-reader".into()
            } else {
                "--contract-bundle".into()
            },
            path.to_string_lossy().into_owned(),
        ];
        if !reader {
            args.push("answer".into());
        }
        run_tote_native("rustgen", &args, 200_000_000_000)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn plan(source: String) -> BundlePlan {
    BundlePlan {
        roots: vec!["main.taut".into()],
        files: BTreeMap::from([
            ("main.taut".into(), source),
            ("data.txt".into(), DATA.into()),
        ]),
    }
}
fn status(out: &RunOutput, stage: &str, success: bool) {
    assert_eq!(out.error, None, "{out:?}");
    assert_eq!(out.exit, Some(if success { 0 } else { 1 }), "{out:?}");
    let header = format!("TAUTO-RUSTGEN-CONTRACT/2 {stage}\n");
    assert!(out.stderr.starts_with(&header), "{out:?}");
    if success {
        assert_eq!(out.stderr, header);
    } else {
        assert!(out.stdout.is_empty(), "partial output: {out:?}");
    }
}

/// The existing host structural walk supplies an independent traversal oracle.
/// It neither expands user macros nor constructs the tested compiler input.
fn expected(source: &str, base: u32) -> (String, Vec<(u32, u32)>) {
    let mut program = parse_program_unresolved_at(source, base)
        .unwrap_or_else(|error| panic!("reader fixture must parse: {error}\n{source}"));
    let mut spans = Vec::new();
    for statement in &mut program.stmts {
        walk::stmt(statement, &mut |term| {
            if let TermKind::MacroCall { name, arg } = &*term.kind
                && name == "include_text"
                // The host walk also visits `where` constraints, which the
                // reader leaves unread (`signature_constraints_stay_unread`).
                && !matches!(&*arg.kind, TermKind::Text(path) if path == "untouched.txt")
            {
                assert!(
                    matches!(&*arg.kind, TermKind::Text(path) if path == "data.txt"),
                    "{:?}",
                    arg.kind
                );
                spans.push((term.span.start - base, term.span.end - base));
                *term = SurfaceTerm::new(TermKind::Text(DATA.into()), term.span);
            }
        });
    }
    (dump_program(&program), spans)
}

#[test]
fn reader_traverses_preserved_surface_and_keeps_resource_bytes_and_spans() {
    let s = Scratch::new();
    for name in [
        "literal_forms",
        "declaration_positions",
        "expression_positions",
        "quote_and_opaque_literal",
        "step_positions",
        "signature_constraints_stay_unread",
    ] {
        let source = case_inputs::fixture(CASES, name);
        let input = plan(source.clone());
        let wire = input.encode().unwrap();
        let (want, spans) = expected(&source, 0);
        let reads = match name {
            "quote_and_opaque_literal" => 3,
            "signature_constraints_stay_unread" => 1,
            _ => source.matches("include_text!(").count(),
        };
        assert_eq!(
            spans.len(),
            reads,
            "oracle must visit every written fixture child: {name}"
        );
        let output = s.run(&input, true);
        status(&output, "reader-complete", true);
        let (report, surface) = output
            .stdout
            .split_once("TAUTO-READER-SURFACE/1\n")
            .unwrap();
        assert_eq!(surface, want, "{name}");
        let resources = report
            .lines()
            .filter(|l| l.starts_with("R\t"))
            .collect::<Vec<_>>();
        assert_eq!(resources.len(), spans.len(), "{name}");
        for (record, (start, end)) in resources.into_iter().zip(spans) {
            assert_eq!(
                record,
                format!("R\tdata.txt\tmain.taut\t{start}\t{end}\t{}", DATA.len())
            );
        }
        assert_eq!(fs::read(s.0.join("input.bundle")).unwrap(), wire.as_bytes());
    }
}

#[test]
fn reader_rejects_metadata_missing_from_surface_instead_of_erasing_it() {
    let s = Scratch::new();
    for name in [
        "attribute_metadata",
        "law_metadata",
        "generated_metadata",
        "decreasing_metadata",
    ] {
        let source = case_inputs::fixture(CASES, name);
        parse_program_unresolved_at(&source, 0)
            .unwrap_or_else(|error| panic!("{name} must parse before metadata rejection: {error}"));
        let output = s.run(&plan(source), true);
        status(&output, "reader-unsupported", false);
        assert!(
            output.stderr.contains("reader.concrete"),
            "{name}: {output:?}"
        );
    }
}

#[test]
fn reader_visits_multiple_original_roots_and_imports_once_without_rebasing_resource_spans() {
    let s = Scratch::new();
    let source = case_inputs::fixture(CASES, "literal_forms");
    let input = BundlePlan {
        roots: vec![
            "prefix.taut".into(),
            "main.taut".into(),
            "prefix.taut".into(),
        ],
        files: BTreeMap::from([
            (
                "prefix.taut".into(),
                r#"fn prefix(): i64 { 7 }
"#
                .into(),
            ),
            ("main.taut".into(), source.clone()),
            ("data.txt".into(), DATA.into()),
        ]),
    };
    let base = input.files["prefix.taut"].len() + 1;
    let output = s.run(&input, true);
    status(&output, "reader-complete", true);
    let (report, surface) = output
        .stdout
        .split_once("TAUTO-READER-SURFACE/1\n")
        .unwrap();
    let sources = report
        .lines()
        .filter(|l| l.starts_with("S\t"))
        .collect::<Vec<_>>();
    assert_eq!(sources.len(), 2);
    assert_eq!(sources[0], format!("S\tprefix.taut\t0\t{}", base - 1));
    assert_eq!(
        sources[1],
        format!("S\tmain.taut\t{base}\t{}", base + source.len())
    );
    let (_, spans) = expected(&source, base as u32);
    for (record, (start, end)) in report.lines().filter(|l| l.starts_with("R\t")).zip(spans) {
        assert_eq!(
            record,
            format!("R\tdata.txt\tmain.taut\t{start}\t{end}\t{}", DATA.len())
        );
    }
    assert!(!surface.contains("MacroCall"));
}

#[test]
fn include_reader_shared_negative_contracts_and_runtime_routes_are_real_observations() {
    use tauto_test_suite::selfhost::{Actual, Backend, Verdict};
    let results = selfhost_harness::shared_cases::run(
        &root().join("cases"),
        Backend::Rust,
        Backend::Rust,
        "selfhost-reader-include",
        &["rustgen".into()],
    )
    .unwrap();
    assert_eq!(results.len(), 10);
    for result in results {
        assert_eq!(
            result.verdict,
            Verdict::Passed,
            "{}: {:?}",
            result.name,
            result.verdict
        );
        if result
            .observations
            .iter()
            .any(|o| o.requirement == "macro_error")
        {
            assert!(result.observations.iter().any(|o| o.stage == "macro"
                && matches!(&o.actual, Actual::Rejected(message) if message.contains("include."))));
            assert_eq!(
                result
                    .artifacts
                    .get("reader_implementation")
                    .map(String::as_str),
                Some("tauto-source-reader/include_text; no macro evaluator")
            );
        }
    }
}

#[test]
fn generated_resource_value_runs_after_its_only_input_bundle_is_removed() {
    let s = Scratch::new();
    let source = case_inputs::fixture(CASES, "literal_forms");
    let output = s.run(&plan(source), false);
    status(&output, "generated", true);
    fs::create_dir_all(s.0.join("generated/src")).unwrap();
    fs::write(s.0.join("generated/src/main.rs"), output.stdout).unwrap();
    fs::write(s.0.join("generated/Cargo.toml"), format!("[package]\nname=\"reader-output\"\nversion=\"0.0.0\"\nedition=\"2024\"\n[dependencies]\ntauto-rt={{path={:?}}}\n[workspace]\n", root().join("crates/tauto-rt"))).unwrap();
    fs::remove_file(s.0.join("input.bundle")).unwrap();
    let executed = std::process::Command::new(env!("CARGO"))
        .current_dir(s.0.join("generated"))
        .env("CARGO_TARGET_DIR", s.0.join("target"))
        .env("CARGO_BUILD_BUILD_DIR", s.0.join("build"))
        .args(["run", "--offline", "--quiet"])
        .output()
        .unwrap();
    assert!(
        executed.status.success(),
        "{}",
        String::from_utf8_lossy(&executed.stderr)
    );
    assert_eq!(executed.stdout, format!("{}\n", DATA.repeat(5)).as_bytes());
    let artifact =
        s.0.join("target/debug")
            .join(format!("reader-output{}", std::env::consts::EXE_SUFFIX));
    eprintln!(
        "reader disposable Cargo.lock:\n{}reader emitted source SHA-256: {}\nreader runtime artifact SHA-256: {}\nreader runtime dependency: {}",
        fs::read_to_string(s.0.join("generated/Cargo.lock")).unwrap(),
        tauto_syntax::sha256_hex(&fs::read(s.0.join("generated/src/main.rs")).unwrap()),
        tauto_syntax::sha256_hex(&fs::read(&artifact).unwrap()),
        root().join("crates/tauto-rt").display(),
    );
}

#[test]
fn exhausted_reader_traversal_is_not_success() {
    use tauto::check::{Verdict, check_file};
    let entries = check_file(&root().join("totes/rustgen/tests/reader.taut")).unwrap();
    let equation = entries
        .iter()
        .find(|entry| entry.entry.name.as_str() == "reader_zero_fuel_is_not_success")
        .unwrap();
    assert!(
        matches!(&equation.entry.verdict, Verdict::Checked { axioms } if axioms.is_empty()),
        "{:?}",
        equation.entry.verdict
    );
}

#[test]
fn compiled_reader_reconstruction_keeps_hidden_fields_and_unread_constraints() {
    let s = Scratch::new();
    let tote = s.0.join("observer");
    fs::create_dir_all(tote.join("src")).unwrap();
    let mut manifest = "package { name=\"reader-observer\" }\ndependencies {\n".to_owned();
    for name in ["parse", "surface", "syntax", "text", "unicode"] {
        manifest.push_str(&format!(
            "  {name} {{ path={:?} }}\n",
            root().join("totes").join(name)
        ));
    }
    manifest.push_str("}\n");
    fs::write(tote.join("Tauto.eure"), manifest).unwrap();
    let driver = tote.join("src/main.taut");
    fs::write(
        &driver,
        format!(
            "import {:?}\n{}",
            root().join("totes/rustgen/tests/reader.taut"),
            case_inputs::fixture(CASES, "structural_observer")
        ),
    )
    .unwrap();
    let generated = s.0.join("observer-generated");
    let emitted = std::process::Command::new(env!("CARGO"))
        .current_dir(root())
        .args([
            "run",
            "--locked",
            "--offline",
            "--quiet",
            "-p",
            "tauto-cli",
            "--",
            "build",
            "--emit",
            "rust",
            "-o",
        ])
        .arg(&generated)
        .arg(&tote)
        .output()
        .unwrap();
    assert!(
        emitted.status.success(),
        "{}",
        String::from_utf8_lossy(&emitted.stderr)
    );
    let built = std::process::Command::new(env!("CARGO"))
        .current_dir(&generated)
        .env("CARGO_TARGET_DIR", s.0.join("observer-target"))
        .env("CARGO_BUILD_BUILD_DIR", s.0.join("observer-build"))
        .args(["build", "--offline", "--quiet", "--message-format=json"])
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let artifacts: Vec<_> = String::from_utf8(built.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter_map(|record| {
            record
                .get("executable")
                .and_then(|v| v.as_str())
                .map(PathBuf::from)
        })
        .collect();
    assert_eq!(artifacts.len(), 1);
    let artifact = &artifacts[0];
    let executed = std::process::Command::new(artifact).output().unwrap();
    assert!(
        executed.status.success(),
        "{}",
        String::from_utf8_lossy(&executed.stderr)
    );
    assert!(executed.stderr.is_empty());
    assert_eq!(executed.stdout, b"class\ninstance\nextern\nfunction\n");
    eprintln!(
        "reader observer Cargo.lock:\n{}reader observer source SHA-256: {}\nreader observer executable SHA-256: {}",
        fs::read_to_string(generated.join("Cargo.lock")).unwrap(),
        tauto_syntax::sha256_hex(&fs::read(driver).unwrap()),
        tauto_syntax::sha256_hex(&fs::read(artifact).unwrap()),
    );
}

#[test]
fn existing_include_cases_keep_unimplemented_macro_and_binary_routes_incomplete() {
    use tauto_test_suite::selfhost::{Backend, Verdict};
    for target in [Backend::Rust, Backend::Javascript] {
        let results = selfhost_harness::shared_cases::run(
            &root().join("cases"),
            Backend::Rust,
            target,
            "macro/include/",
            &["rustgen".into()],
        )
        .unwrap();
        for suffix in [
            "an-absolute-path-is-refused",
            "a-path-out-of-the-directory-is-refused",
            "a-path-out-of-the-tote-is-refused",
            "a-missing-file-is-refused",
            "the-argument-is-a-text-literal",
        ] {
            let result = results.iter().find(|r| r.name.ends_with(suffix)).unwrap();
            assert_eq!(
                result.verdict,
                Verdict::Passed,
                "{}: {:?}",
                result.name,
                result.verdict
            );
        }
        for suffix in [
            "a-file-that-is-not-utf-8-is-refused",
            "a-macro-cannot-take-the-name",
            "a-call-a-macro-makes-is-refused",
            "a-proof-sees-only-the-literal",
            "a-file-of-the-same-directory-is-read-as-a-text",
            "a-file-of-the-tote-is-read-from-a-file-below-it",
        ] {
            let result = results.iter().find(|r| r.name.ends_with(suffix)).unwrap();
            assert!(
                matches!(&result.verdict, Verdict::Incomplete(_)),
                "{}: {:?}",
                result.name,
                result.verdict
            );
        }
    }
}

#[test]
fn resource_input_limits_are_not_semantic_rejections() {
    let s = Scratch::new();
    let source = r#"fn answer(): Text { include_text!("a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a") }"#.to_string();
    let output = s.run(&plan(source), true);
    status(&output, "reader-unsupported", false);
    assert!(output.stderr.contains("reader.path"));
}

/// The inputs these tests read, kept as files under `tests/fixtures`.
mod case_inputs {
    fn read(path: &str) -> String {
        let path = format!("{}/tests/fixtures/{path}", env!("CARGO_MANIFEST_DIR"));
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"))
    }
    pub fn fixture(file: &str, name: &str) -> String {
        read(&format!("{}/{}.taut", file.trim_end_matches(".eure"), name))
    }
}
