use std::collections::BTreeMap;
use tauto_test_suite::selfhost::{
    Actual, Backend, Contract, Implementation, Observation, Value, Verdict, assess,
};
fn case(fields: &[(&str, Value)]) -> Contract {
    Contract {
        name: "test/example".into(),
        file: "test.eure".into(),
        id: "example".into(),
        fields: fields
            .iter()
            .map(|(k, v)| (k.to_string(), v.clone()))
            .collect(),
        source_is_path: false,
        input: tauto_test_suite::selfhost::RawInput::HostOnly,
        host_harness_only: false,
    }
}
fn text(s: &str) -> Value {
    Value::Text(s.into())
}
fn observation(name: &str, stage: &str, actual: Actual) -> Observation {
    Observation {
        requirement: name.into(),
        stage: stage.into(),
        implementation: Implementation::Tauto,
        compiler_backend: Backend::Rust,
        target_backend: Some(Backend::Rust),
        actual,
    }
}
#[test]
fn missing_stage_is_not_a_pass() {
    let c = case(&[("parses", Value::Bool(true)), ("types", text("ok"))]);
    let o = observation("parses", "parse", Actual::Value(Value::Bool(true)));
    assert!(matches!(
        assess(&c, Backend::Rust, &[o]),
        Verdict::Incomplete(_)
    ));
}
#[test]
fn exact_tauto_observation_passes() {
    let c = case(&[("parses", Value::Bool(false))]);
    assert_eq!(
        assess(
            &c,
            Backend::Rust,
            &[observation(
                "parses",
                "parse",
                Actual::Value(Value::Bool(false))
            )]
        ),
        Verdict::Passed
    );
}
#[test]
fn a_bootstrap_answer_is_not_a_selfhost_observation() {
    let c = case(&[("parses", Value::Bool(true))]);
    let mut o = observation("parses", "parse", Actual::Value(Value::Bool(true)));
    o.implementation = Implementation::Bootstrap;
    assert!(matches!(
        assess(&c, Backend::Rust, &[o]),
        Verdict::Failed(_)
    ));
}
#[test]
fn expected_rejection_requires_the_stage_and_the_message() {
    let c = case(&[(
        "compile_errors",
        Value::Map(BTreeMap::from([(
            "rust".into(),
            text("front: specific diagnostic"),
        )])),
    )]);
    assert_eq!(
        assess(
            &c,
            Backend::Rust,
            &[observation(
                "compile_errors",
                "front",
                Actual::Rejected("specific diagnostic at file".into())
            )]
        ),
        Verdict::Passed
    );
    for (stage, message) in [
        ("build", "specific diagnostic"),
        ("front", "unrelated failure"),
    ] {
        assert!(matches!(
            assess(
                &c,
                Backend::Rust,
                &[observation(
                    "compile_errors",
                    stage,
                    Actual::Rejected(message.into())
                )]
            ),
            Verdict::Failed(_)
        ));
    }
}
#[test]
fn unavailable_or_timed_out_rejection_is_incomplete() {
    let c = case(&[("format_error", text("expected"))]);
    for actual in [
        Actual::Unsupported("expected".into()),
        Actual::Timeout("expected".into()),
    ] {
        assert!(matches!(
            assess(
                &c,
                Backend::Rust,
                &[observation("format_error", "format", actual)]
            ),
            Verdict::Incomplete(_)
        ));
    }
}
#[test]
fn known_failure_reproduction_is_not_a_success() {
    let c = case(&[(
        "backend_known_failure",
        Value::Map(BTreeMap::from([("rust".into(), text("build: broken"))])),
    )]);
    assert!(matches!(
        assess(
            &c,
            Backend::Rust,
            &[observation(
                "backend_known_failure",
                "build",
                Actual::Rejected("broken".into())
            )]
        ),
        Verdict::Incomplete(_)
    ));
    assert!(matches!(
        assess(
            &c,
            Backend::Rust,
            &[observation(
                "backend_known_failure",
                "build",
                Actual::Accepted
            )]
        ),
        Verdict::Failed(_)
    ));
}
#[test]
fn wrong_target_is_not_hidden_by_javascript_compiler_execution() {
    let c = case(&[
        ("selfhost_entry", text("answer")),
        ("differential", text("rustgen")),
        ("selfhost_stdout", text("42\n")),
    ]);
    let mut output = observation(
        "selfhost_stdout",
        "target-runtime",
        Actual::Value(text("42\n")),
    );
    output.compiler_backend = Backend::Javascript;
    let mut exit = observation(
        "exit",
        "target-runtime",
        Actual::Value(Value::Integer("0".into())),
    );
    exit.compiler_backend = Backend::Javascript;
    assert!(matches!(
        assess(&c, Backend::Javascript, &[output, exit]),
        Verdict::Failed(_)
    ));
}
#[test]
fn duplicate_and_unknown_observations_fail() {
    let c = case(&[("parses", Value::Bool(true))]);
    let o = observation("parses", "parse", Actual::Value(Value::Bool(true)));
    assert!(matches!(
        assess(&c, Backend::Rust, &[o.clone(), o]),
        Verdict::Failed(_)
    ));
    assert!(matches!(
        assess(
            &c,
            Backend::Rust,
            &[observation("unknown", "parse", Actual::Accepted)]
        ),
        Verdict::Failed(_)
    ));
}
#[test]
fn compile_rejection_overrides_host_runtime_error_not_frontend_checks() {
    let c = case(&[
        ("types", text("error: bad")),
        ("run_error", text("bad")),
        (
            "compile_errors",
            Value::Map(BTreeMap::from([("rust".into(), text("front: bad"))])),
        ),
    ]);
    let names = c
        .requirements(Backend::Rust)
        .into_iter()
        .map(|r| r.name)
        .collect::<Vec<_>>();
    assert!(names.contains(&"types".into()));
    assert!(names.contains(&"compile_errors".into()));
    assert!(!names.contains(&"run_error".into()));
}
#[test]
fn harness_only_and_explicitly_excluded_are_separate_from_passes() {
    let mut c = case(&[("parses", Value::Bool(true))]);
    c.host_harness_only = true;
    assert_eq!(assess(&c, Backend::Rust, &[]), Verdict::HostHarness);
    c.host_harness_only = false;
    c.fields
        .insert("backends".into(), Value::Array(vec![text("javascript")]));
    assert_eq!(assess(&c, Backend::Rust, &[]), Verdict::Excluded);
}

fn document(text: &str) -> (std::path::PathBuf, Result<Vec<Contract>, String>) {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "selfhost-contract-test-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("input.eure"), text).unwrap();
    let result = tauto_test_suite::selfhost::contracts(&dir);
    (dir, result)
}
#[test]
fn explicit_selfhost_contracts_are_validated_and_do_not_select_bootstrap_runtime() {
    let (dir, result) = document(
        "@ cases.one\nsource = ''\ndifferential = 'rustgen'\nselfhost_entry = 'answer'\nselfhost_stdout = '42'\n",
    );
    let cases = result.unwrap();
    let requirements = cases[0].requirements(Backend::Rust);
    assert!(requirements.iter().any(|r| r.name == "selfhost_stdout"));
    assert!(!requirements.iter().any(|r| r.name == "differential"));
    let bootstrap = tauto_test_suite::rust_cases(&dir).unwrap();
    assert!(!bootstrap[0].selects_backend("rust"));
    assert!(!bootstrap[0].selects_backend("javascript"));
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn ambiguous_or_wrongly_scoped_selfhost_contracts_reject() {
    for extra in [
        "selfhost_stdout = 'x'",
        "selfhost_entry = 'answer'\nselfhost_stdout = 'x'\nselfhost_compile_error = 'bad'",
        "selfhost_entry = 'answer'\nselfhost_compile_error = ''",
    ] {
        let (dir, result) = document(&format!("source = ''\ndifferential = 'rustgen'\n{extra}\n"));
        assert!(result.is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }
    let (dir, result) =
        document("source = ''\nparses = true\nselfhost_entry = 'answer'\nselfhost_stdout = 'x'\n");
    assert!(result.unwrap_err().contains("differential"));
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn all_case_ids_and_fixture_boundaries_are_discovered_from_the_requested_root() {
    let (dir, result) = document(
        "@ cases.one\nsource = ''\nparses = true\n@ cases.loader\nfiles.'main.taut' = ''\nload_error = 'specific load error'\n@ fixtures.only_input\nsource = ''\nreason = 'host protocol fixture'\n",
    );
    let cases = result.unwrap();
    assert_eq!(cases.len(), 2);
    assert!(
        cases
            .iter()
            .all(|c| c.file.starts_with(dir.canonicalize().unwrap()))
    );
    assert!(cases.iter().any(|c| {
        c.requirements(Backend::Javascript)
            .iter()
            .any(|r| r.stage == "load")
    }));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn target_specific_compile_failure_requires_target_provenance() {
    let c = case(&[
        ("selfhost_entry", text("answer")),
        ("differential", text("rustgen")),
        ("selfhost_compile_error", text("unsupported record")),
    ]);
    let mut o = observation(
        "selfhost_compile_error",
        "selfhost-compile",
        Actual::Rejected("unsupported record".into()),
    );
    o.compiler_backend = Backend::Javascript;
    assert!(matches!(
        assess(&c, Backend::Javascript, &[o]),
        Verdict::Failed(_)
    ));
}
#[test]
fn unsupported_target_is_incomplete_before_a_result_exists() {
    let c = case(&[
        ("selfhost_entry", text("answer")),
        ("differential", text("rustgen")),
        ("selfhost_compile_error", text("unsupported record")),
    ]);
    let mut o = observation(
        "selfhost_compile_error",
        "selfhost-compile",
        Actual::Unsupported("no Tauto JavaScript target emitter".into()),
    );
    o.compiler_backend = Backend::Javascript;
    o.target_backend = None;
    assert!(matches!(
        assess(&c, Backend::Javascript, &[o]),
        Verdict::Incomplete(_)
    ));
}

#[test]
fn javascript_compiler_host_may_prove_rust_target_only_when_explicit() {
    let c = case(&[
        ("differential", text("rustgen")),
        ("selfhost_entry", text("answer")),
        ("selfhost_compile_error", text("specific rejection")),
    ]);
    let mut o = observation(
        "selfhost_compile_error",
        "selfhost-compile",
        Actual::Rejected("specific rejection".into()),
    );
    o.compiler_backend = Backend::Javascript;
    assert_eq!(
        tauto_test_suite::selfhost::assess_route(
            &c,
            Backend::Javascript,
            Backend::Rust,
            &[o.clone()]
        ),
        Verdict::Passed
    );
    assert!(matches!(
        assess(&c, Backend::Javascript, &[o]),
        Verdict::Failed(_)
    ));
}

#[test]
fn backend_error_overrides_common_shows_but_not_explicit_pre_error_shows() {
    let mut c = case(&[
        ("shows", Value::Array(vec![text("host result")])),
        ("rust_error", text("native error")),
    ]);
    assert!(
        !c.requirements(Backend::Rust)
            .iter()
            .any(|r| r.name == "shows")
    );
    c.fields.insert(
        "rust_shows".into(),
        Value::Array(vec![text("before failure")]),
    );
    assert!(
        c.requirements(Backend::Rust)
            .iter()
            .any(|r| r.name == "shows" && r.expected == Value::Array(vec![text("before failure")]))
    );
    c.fields.insert(
        "javascript_shows".into(),
        Value::Array(vec![text("JS result")]),
    );
    assert!(
        !c.requirements(Backend::Javascript)
            .iter()
            .any(|r| r.name == "run_error")
    );
}

#[test]
fn explicit_compile_only_backend_requires_actual_target_acceptance() {
    let c = case(&[
        ("parses", Value::Bool(true)),
        ("backends", Value::Array(vec![text("rust")])),
    ]);
    let parsed = observation("parses", "parse", Actual::Value(Value::Bool(true)));
    assert!(matches!(
        assess(&c, Backend::Rust, &[parsed.clone()]),
        Verdict::Incomplete(_)
    ));
    assert_eq!(
        assess(
            &c,
            Backend::Rust,
            &[
                parsed,
                observation("target_build", "build", Actual::Accepted)
            ]
        ),
        Verdict::Passed
    );
}

#[test]
fn rust_skip_applies_to_its_target_but_unimplemented_applies_to_all() {
    // These observations exercise classification only, not a compiler execution.
    let mut c = case(&[
        ("parses", Value::Bool(true)),
        ("rust", text("skip: eval-only")),
    ]);
    let rust = observation("parses", "parse", Actual::Value(Value::Bool(true)));
    let mut javascript = rust.clone();
    javascript.compiler_backend = Backend::Javascript;
    javascript.target_backend = Some(Backend::Javascript);
    assert!(matches!(
        assess(&c, Backend::Rust, &[rust.clone()]),
        Verdict::Incomplete(_)
    ));
    assert_eq!(
        assess(&c, Backend::Javascript, &[javascript.clone()]),
        Verdict::Passed
    );
    c.fields
        .insert("unimplemented".into(), text("missing language capability"));
    assert!(matches!(
        assess(&c, Backend::Rust, &[rust]),
        Verdict::Incomplete(_)
    ));
    assert!(matches!(
        assess(&c, Backend::Javascript, &[javascript]),
        Verdict::Incomplete(_)
    ));
}

#[test]
fn malformed_sibling_envelopes_cannot_disappear_from_discovery() {
    let (dir, valid) = document("source = ''\nparses = true\n");
    assert_eq!(valid.unwrap().len(), 1);
    for malformed in [
        "@ casess.hidden\nsource = ''\nparses = true\n",
        "description = 'no cases here'\n",
        "cases = true\n",
        "fixtures = {}\n",
    ] {
        std::fs::write(dir.join("malformed.eure"), malformed).unwrap();
        assert!(tauto_test_suite::selfhost::contracts(&dir).is_err());
        assert!(tauto_test_suite::capabilities(&dir).is_err());
        assert!(tauto_test_suite::rust_cases(&dir).is_err());
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn a_fixture_only_sibling_is_valid_but_not_a_semantic_case() {
    let (dir, valid) = document("source = ''\nparses = true\n");
    assert_eq!(valid.unwrap().len(), 1);
    std::fs::write(
        dir.join("fixtures.eure"),
        "@ fixtures.protocol\nsource = ''\nreason = 'host transport input'\n",
    )
    .unwrap();
    assert_eq!(
        tauto_test_suite::selfhost::contracts(&dir).unwrap().len(),
        1
    );
    assert_eq!(tauto_test_suite::capabilities(&dir).unwrap().len(), 1);
    assert_eq!(tauto_test_suite::rust_cases(&dir).unwrap().len(), 1);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn unrelated_expected_error_cannot_suppress_runtime_exit_validation() {
    let (dir, parsed) = document(
        "source = ''\ndifferential = 'rustgen'\nselfhost_entry = 'answer'\nselfhost_stdout = '42'\nformat_error = 'specific formatter error'\n",
    );
    let cases = parsed.unwrap();
    let c = &cases[0];
    assert!(
        c.requirements(Backend::Rust)
            .iter()
            .any(|r| { r.name == "exit" && r.expected == Value::Integer("0".into()) })
    );
    let output = observation(
        "selfhost_stdout",
        "target-runtime",
        Actual::Value(text("42")),
    );
    let error = observation(
        "format_error",
        "format",
        Actual::Rejected("specific formatter error".into()),
    );
    for exit in ["1", "2"] {
        assert!(matches!(
            assess(
                c,
                Backend::Rust,
                &[
                    output.clone(),
                    error.clone(),
                    observation(
                        "exit",
                        "target-runtime",
                        Actual::Value(Value::Integer(exit.into()))
                    )
                ]
            ),
            Verdict::Failed(_)
        ));
    }
    assert_eq!(
        assess(
            c,
            Backend::Rust,
            &[
                output,
                error,
                observation(
                    "exit",
                    "target-runtime",
                    Actual::Value(Value::Integer("0".into()))
                )
            ]
        ),
        Verdict::Passed
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn unspecified_diagnostic_substrings_are_incomplete_not_vacuous_matches() {
    use tauto_test_suite::selfhost::Matcher;
    for (name, stage, expected) in [
        ("types", "types", "error: "),
        ("rows", "rows", "error: "),
        ("rows_javascript", "rows-javascript", "error: "),
        ("lin", "lin", "error: "),
        ("build", "build", "error: "),
        ("load_error", "load", ""),
        ("macro_error", "macro", ""),
        ("run_error", "target-runtime", ""),
    ] {
        let c = case(&[(name, text(expected))]);
        let requirements = c.requirements(Backend::Rust);
        assert_eq!(requirements.len(), 1);
        assert_eq!(requirements[0].matcher, Matcher::Pending);
        for actual in [Actual::Rejected("any diagnostic".into()), Actual::Accepted] {
            let verdict = assess(&c, Backend::Rust, &[observation(name, stage, actual)]);
            let Verdict::Incomplete(reasons) = verdict else {
                panic!("{name} did not remain incomplete: {verdict:?}");
            };
            assert!(
                reasons
                    .iter()
                    .any(|reason| reason.contains("diagnostic message is unspecified"))
            );
        }
        assert!(matches!(
            assess(
                &c,
                Backend::Rust,
                &[observation(
                    name,
                    "wrong-stage",
                    Actual::Rejected("any diagnostic".into())
                )]
            ),
            Verdict::Failed(_)
        ));
    }
}

#[test]
fn nonempty_checker_rejection_requires_its_exact_stage_and_message() {
    let c = case(&[("types", text("error: expected number"))]);
    assert_eq!(
        assess(
            &c,
            Backend::Rust,
            &[observation(
                "types",
                "types",
                Actual::Rejected("expected number at byte 2".into())
            )]
        ),
        Verdict::Passed
    );
    for (stage, message) in [("parse", "expected number"), ("types", "unrelated")] {
        assert!(matches!(
            assess(
                &c,
                Backend::Rust,
                &[observation(
                    "types",
                    stage,
                    Actual::Rejected(message.into())
                )]
            ),
            Verdict::Failed(_)
        ));
    }
}

#[test]
fn messageless_checker_and_proof_errors_keep_their_values() {
    let (dir, parsed) = document(
        "source = 'x'\ntypes = 'error: '\nchecks.declaration = 'error: '\ndiagnostics = [{ stage => 'types', message => '', span => '«x»' }]\n",
    );
    let cases = parsed.unwrap();
    assert_eq!(cases[0].text("types"), Some("error: "));
    assert_eq!(
        cases[0].fields.get("checks"),
        Some(&Value::Map(BTreeMap::from([(
            "declaration".into(),
            text("error: ")
        )])))
    );
    assert!(matches!(
        assess(
            &cases[0],
            Backend::Rust,
            &[
                observation("types", "types", Actual::Rejected("arbitrary".into())),
                observation("checks", "checks", Actual::Accepted),
                observation("diagnostics", "checks", Actual::Accepted)
            ]
        ),
        Verdict::Incomplete(_)
    ));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn an_earlier_timeout_preserves_its_stage_without_becoming_a_language_failure() {
    let c = case(&[("selfhost_stdout", text("42\n"))]);
    for stage in ["selfhost-compile", "build", "target-runtime"] {
        let o = observation(
            "selfhost_stdout",
            stage,
            Actual::Timeout("bounded execution expired".into()),
        );
        assert!(
            matches!(assess(&c, Backend::Rust, &[o]), Verdict::Incomplete(why) if why.iter().any(|s| s.contains(stage) && s.contains("bounded execution expired")))
        );
        let o = observation(
            "selfhost_stdout",
            stage,
            Actual::HarnessFailure("bootstrap reference panicked".into()),
        );
        assert!(
            matches!(assess(&c, Backend::Rust, &[o]), Verdict::Failed(why) if why.iter().any(|s| s.contains(stage) && s.contains("bootstrap reference panicked")))
        );
    }
}

#[test]
fn raw_inputs_keep_path_tags_before_expectation_text_is_flattened() {
    use tauto_test_suite::selfhost::{InputText, RawInput};
    let (dir, result) = document(
        "@ cases.paths\nfiles.'nested/main.nib' = path`backing.txt`\nfiles.'literal.txt' = 'backing.txt'\nentry = 'nested/main.nib'\nload_error = 'missing dependency'\n",
    );
    let cases = result.unwrap();
    let RawInput::Files { files, entry, .. } = &cases[0].input else {
        panic!("files descriptor missing")
    };
    assert_eq!(entry, "nested/main.nib");
    assert_eq!(
        files["nested/main.nib"],
        InputText::Path("backing.txt".into())
    );
    assert_eq!(
        files["literal.txt"],
        InputText::Inline("backing.txt".into())
    );
    std::fs::write(dir.join("backing.txt"), "\r\n日本語\0\n").unwrap();
    assert_eq!(
        files["nested/main.nib"].read(&cases[0].file).unwrap(),
        "\r\n日本語\0\n"
    );
    assert_eq!(
        files["literal.txt"].read(&cases[0].file).unwrap(),
        "backing.txt"
    );
    assert!(cases[0].single_source().unwrap().is_none());
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn raw_inputs_preserve_import_order_default_entry_and_extraction_request() {
    use tauto_test_suite::selfhost::{InputText, RawInput};
    let (dir, result) = document(
        "@ cases.source\nsource = 'unchanged'\nimports = [path`z.taut`, path`a.tauto`]\nextract = true\nchecks_all = 'ok'\n@ cases.files\nfiles.'main.nib' = 'unchanged'\nload_error = 'missing'\n",
    );
    let cases = result.unwrap();
    let source = cases.iter().find(|c| c.id == "source").unwrap();
    assert_eq!(
        source.input,
        RawInput::Source {
            source: InputText::Inline("unchanged".into()),
            imports: vec!["z.taut".into(), "a.tauto".into()],
            extract: true,
        }
    );
    assert!(source.single_source().unwrap().is_none());
    let files = cases.iter().find(|c| c.id == "files").unwrap();
    assert!(
        matches!(&files.input, RawInput::Files { entry, tote: None, extract: false, .. } if entry == "main.nib")
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn raw_inputs_distinguish_external_and_virtual_totes_without_loading_them() {
    use tauto_test_suite::selfhost::RawInput;
    let (dir, result) = document(
        "@ cases.external\ntote = path`does-not-exist`\nload_error = 'missing'\n@ cases.virtual\nfiles.'app/Tauto.eure' = 'raw manifest'\nfiles_tote = 'app'\nload_error = 'missing'\n",
    );
    let cases = result.unwrap();
    assert_eq!(
        cases.iter().find(|c| c.id == "external").unwrap().input,
        RawInput::Tote {
            directory: "does-not-exist".into(),
            extract: false,
        }
    );
    assert!(
        matches!(&cases.iter().find(|c| c.id == "virtual").unwrap().input,
        RawInput::Files { tote: Some(tote), .. } if tote == "app")
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn path_sources_are_read_on_demand_and_totes_keep_extraction_flags() {
    use tauto_test_suite::selfhost::RawInput;
    let (dir, result) = document(
        "@ cases.path\nsource = path`missing.taut`\ntypes = 'ok'\n@ cases.tote\ntote = path`missing-tote`\nextract = true\nchecks_all = 'ok'\n",
    );
    let cases = result.unwrap();
    std::fs::write(dir.join("missing.taut"), "unchanged\r\n").unwrap();
    let RawInput::Source { source, .. } = &cases.iter().find(|c| c.id == "path").unwrap().input
    else {
        panic!("source descriptor missing")
    };
    assert_eq!(source.read(&cases[0].file).unwrap(), "unchanged\r\n");
    assert!(
        cases
            .iter()
            .find(|c| c.id == "path")
            .unwrap()
            .single_source()
            .unwrap()
            .is_none()
    );
    assert!(matches!(
        &cases.iter().find(|c| c.id == "tote").unwrap().input,
        RawInput::Tote { extract: true, .. }
    ));
    std::fs::remove_dir_all(dir).unwrap();
}
