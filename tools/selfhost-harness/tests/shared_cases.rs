use selfhost_harness::shared_cases::split_reports;
#[test]
fn component_headers_preserve_empty_successful_reports() {
    assert_eq!(
        split_reports(
            "== first\n== second\nerror 0 1 diagnostic\n",
            &["first".into(), "second".into()]
        )
        .unwrap(),
        vec!["", "error 0 1 diagnostic\n"]
    );
}
#[test]
fn missing_duplicate_extra_and_unframed_reports_fail() {
    for output in [
        "",
        "orphan\n== first\n",
        "== first\n== first\n",
        "== first\n== other\n",
    ] {
        assert!(
            split_reports(output, &["first".into(), "second".into()]).is_err(),
            "{output:?}"
        );
    }
    assert!(split_reports("== first\n", &["first".into(), "first".into()]).is_err());
}

#[test]
fn compiler_rejection_is_not_a_transport_or_target_build_failure() {
    use selfhost_harness::{RunOutput, shared_rustgen::compiler_result};
    let mut o = RunOutput {
        stdout: String::new(),
        stderr: "TAUTO-RUSTGEN-CONTRACT/1 source-rejected\nrustgen: specific compiler rejection\n"
            .into(),
        exit: Some(1),
        error: None,
    };
    assert_eq!(
        compiler_result(&o).unwrap(),
        Err("rustgen: specific compiler rejection\n".into())
    );
    for stderr in [
        "rustgen: specific compiler rejection\n",
        "TAUTO-RUSTGEN-CONTRACT/1 input-error\nrustgen: specific compiler rejection\n",
        "TAUTO-RUSTGEN-CONTRACT/1 tables-error\nrustgen: specific compiler rejection\n",
        "TAUTO-RUSTGEN-CONTRACT/1 source-rejected\nrustgen: \n",
        "TAUTO-RUSTGEN-CONTRACT/1 target-runtime\nrustgen: specific compiler rejection\n",
        "TAUTO-RUSTGEN-CONTRACT/1 source-rejected\nrustgen: expected\nunclassified tool failure\n",
        "TAUTO-RUSTGEN-CONTRACT/1 source-rejected\nrustgen: expected\nTAUTO-RUSTGEN-CONTRACT/1 generated\n",
    ] {
        o.stderr = stderr.into();
        assert!(compiler_result(&o).is_err(), "{stderr:?}");
    }
    o.stderr =
        "TAUTO-RUSTGEN-CONTRACT/1 source-rejected\nrustgen: specific compiler rejection\n".into();
    o.stdout = "partial target output".into();
    assert!(compiler_result(&o).is_err());
    o.stdout.clear();
    o.exit = None;
    assert!(compiler_result(&o).is_err());
    o.exit = Some(1);
    o.error = Some("compiler execution timed out".into());
    assert!(compiler_result(&o).is_err());
    o.error = None;
    o.exit = Some(0);
    o.stderr = "TAUTO-RUSTGEN-CONTRACT/1 generated\n".into();
    assert!(compiler_result(&o).is_err());
    o.stdout = "target program".into();
    assert_eq!(compiler_result(&o).unwrap(), Ok(o.stdout.clone()));
    o.stderr.push_str("unexpected output\n");
    assert!(compiler_result(&o).is_err());
}

#[test]
fn unknown_or_wrong_stage_component_reports_never_pass() {
    use selfhost_harness::shared_cases::{checker_status, parse_result};
    use tauto_test_suite::selfhost::{Actual, Value};
    for report in ["cannot read: missing\n", "garbage\n", "", "0 Program 0 0"] {
        assert!(matches!(parse_result(report), Actual::HarnessFailure(_)));
    }
    assert!(matches!(
        parse_result("error\n"),
        Actual::Value(Value::Bool(false))
    ));
    assert!(matches!(
        parse_result("0 Program 0 0\n"),
        Actual::Value(Value::Bool(true))
    ));
    for report in [
        "error\n",
        "unclassified failure\n",
        "error 0 1 expected\ngarbage\n",
        "error 0 1 \n",
    ] {
        assert!(matches!(
            checker_status("types", report),
            Actual::HarnessFailure(_)
        ));
    }
    assert!(matches!(checker_status("lin", ""), Actual::Accepted));
    assert!(matches!(
        checker_status("unknown", ""),
        Actual::HarnessFailure(_)
    ));
    assert!(
        matches!(checker_status("types", "error 0 1 expected\n"), Actual::Rejected(s) if s == "expected")
    );
}

#[test]
fn inferred_reports_use_actual_unique_values_not_expected_values() {
    use selfhost_harness::shared_cases::inferred_values;
    use std::collections::BTreeMap;
    use tauto_test_suite::selfhost::{Actual, Value};
    let requested = Value::Map(BTreeMap::from([(
        "a".into(),
        Value::Text("must not be copied".into()),
    )]));
    assert!(
        matches!(inferred_values("types", "let a i32\n", &requested), Actual::Value(Value::Map(m)) if m["a"] == Value::Text("i32".into()))
    );
    for report in ["let b i32\n", "let a i32\nlet a Text\n", "error\n"] {
        assert!(matches!(
            inferred_values("types", report, &requested),
            Actual::HarnessFailure(_)
        ));
    }
    assert!(
        matches!(inferred_values("rows", "function a {Div, ask}\n", &requested), Actual::Value(Value::Map(m)) if m["a"] == Value::Array(vec![Value::Text("Div".into()), Value::Text("ask".into())]))
    );
    assert!(matches!(
        inferred_values("rows", "function a Div\n", &requested),
        Actual::HarnessFailure(_)
    ));
}

#[test]
fn completed_looking_output_cannot_hide_failed_or_interrupted_processes() {
    use selfhost_harness::{RunOutput, shared_cases::component_reports};
    let paths = vec!["input".to_string()];
    let mut output = RunOutput {
        stdout: "== input\n0 Program 0 0\n".into(),
        stderr: String::new(),
        exit: Some(0),
        error: None,
    };
    assert_eq!(
        component_reports("syntax", &output, &paths).unwrap(),
        ["0 Program 0 0\n"]
    );
    for exit in [Some(1), Some(2), None] {
        output.exit = exit;
        assert!(component_reports("syntax", &output, &paths).is_err());
    }
    output.exit = Some(0);
    output.error = Some("execution exceeded the safety limit".into());
    assert!(component_reports("syntax", &output, &paths).is_err());
    output.error = None;
    output.stderr = "unclassified failure".into();
    assert!(component_reports("syntax", &output, &paths).is_err());
}

#[test]
fn differential_equality_requires_valid_stage_specific_reports() {
    use selfhost_harness::shared_cases::{differential_report, format_result};
    use tauto_test_suite::selfhost::Actual;
    for mode in ["types", "rows", "lin", "fmt"] {
        assert!(matches!(
            differential_report(mode, Ok("error\n".into()), "error\n"),
            Actual::Unsupported(_)
        ));
    }
    assert!(matches!(
        differential_report("syntax", Ok("error\n".into()), "error\n"),
        Actual::Differential { .. }
    ));
    assert!(matches!(
        differential_report(
            "types",
            Ok("error 0 1 exact diagnostic\n".into()),
            "error 0 1 exact diagnostic\n"
        ),
        Actual::Differential { .. }
    ));
    assert!(matches!(
        differential_report(
            "types",
            Ok("error 0 1 exact diagnostic\n".into()),
            "cannot read: failed\n"
        ),
        Actual::HarnessFailure(_)
    ));
    assert!(matches!(
        differential_report(
            "syntax",
            Err(Actual::HarnessFailure("oracle panic".into())),
            "error\n"
        ),
        Actual::HarnessFailure(_)
    ));
    assert!(matches!(format_result("error\n"), Actual::Unsupported(_)));
}

#[test]
fn v2_compiler_protocol_keeps_load_rejection_and_input_inventory_distinct() {
    use selfhost_harness::{
        RunOutput,
        shared_rustgen::{BundleResult, bundle_code, bundle_result},
    };
    use tauto_test_suite::selfhost::Actual;
    let output = |status: &str, stdout: &str, exit: i32| RunOutput {
        stdout: stdout.into(),
        stderr: format!(
            "TAUTO-RUSTGEN-CONTRACT/2 {status}\n{}",
            if exit == 1 {
                "rustgen: exact diagnostic\n"
            } else {
                ""
            }
        ),
        exit: Some(exit),
        error: None,
    };
    let load = bundle_result(&output("load-rejected", "", 1)).unwrap();
    assert_eq!(
        load,
        BundleResult::LoadRejected("rustgen: exact diagnostic\n".into())
    );
    assert!(matches!(
        bundle_code(load, true),
        Err(("load", Actual::Rejected(_)))
    ));
    let source = bundle_result(&output("source-rejected", "", 1)).unwrap();
    assert!(matches!(
        bundle_code(source, true),
        Err(("selfhost-compile", Actual::Rejected(_)))
    ));
    let inventory = bundle_result(&output("input-complete", "S\tmain.taut\t0\t0\n", 0)).unwrap();
    for load_only in [false, true] {
        assert!(matches!(
            bundle_code(inventory.clone(), load_only),
            Err(("input-audit", Actual::Unsupported(_)))
        ));
    }
    let generated = bundle_result(&output("generated", "target code", 0)).unwrap();
    assert_eq!(
        bundle_code(generated.clone(), false).unwrap(),
        "target code"
    );
    assert!(matches!(
        bundle_code(generated, true),
        Err(("input-audit", Actual::HarnessFailure(_)))
    ));
    assert!(matches!(
        bundle_code(
            bundle_result(&output("input-unsupported", "", 1)).unwrap(),
            false
        ),
        Err(("input-audit", Actual::Unsupported(_)))
    ));
    for status in ["input-error", "tables-error", "unknown"] {
        assert!(bundle_result(&output(status, "", 1)).is_err());
    }
    for status in [
        "load-rejected",
        "source-rejected",
        "input-unsupported",
        "resource-rejected",
    ] {
        assert!(bundle_result(&output(status, "partial code", 1)).is_err());
        assert!(bundle_result(&output(status, "", 0)).is_err());
    }
    let valid = output("load-rejected", "", 1);
    for stderr in [
        "TAUTO-RUSTGEN-CONTRACT/1 source-rejected\nrustgen: exact diagnostic\n",
        "TAUTO-RUSTGEN-CONTRACT/2 load-rejected\nrustgen: \n",
        "TAUTO-RUSTGEN-CONTRACT/2 load-rejected\nrustgen: exact diagnostic\nextra\n",
        "TAUTO-RUSTGEN-CONTRACT/2 load-rejected\nrustgen: exact diagnostic\nTAUTO-RUSTGEN-CONTRACT/2 generated\n",
    ] {
        let bad = RunOutput {
            stderr: stderr.into(),
            ..valid.clone()
        };
        assert!(bundle_result(&bad).is_err());
    }
    for exit in [None, Some(2)] {
        assert!(
            bundle_result(&RunOutput {
                exit,
                ..valid.clone()
            })
            .is_err()
        );
    }
    assert!(
        bundle_result(&RunOutput {
            error: Some("timed out".into()),
            ..valid
        })
        .is_err()
    );
    for report in [
        "",
        "S\tmain.taut\t0\t0",
        "S\tmain.taut\t2\t1\n",
        "S\tmain.taut\t0\t1\nS\tmain.taut\t0\t1\n",
        "R\tdata.txt\tmissing.taut\t0\t1\t3\n",
    ] {
        assert!(
            bundle_result(&output("input-complete", report, 0)).is_err(),
            "{report:?}"
        );
    }
}

struct InputScratch(std::path::PathBuf);
impl InputScratch {
    fn new() -> Self {
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let dir = std::env::temp_dir().canonicalize().unwrap().join(format!(
            "shared-input-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&dir).unwrap();
        Self(dir)
    }
    fn case(&self, text: &str) -> tauto_test_suite::selfhost::Contract {
        std::fs::write(self.0.join("case.eure"), text).unwrap();
        tauto_test_suite::selfhost::contracts(&self.0)
            .unwrap()
            .remove(0)
    }
}
impl Drop for InputScratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn input_preparation_keeps_virtual_member_bytes_resources_and_path_origins() {
    use selfhost_harness::shared_rustgen::{PreparedInput, prepare_input};
    let s = InputScratch::new();
    std::fs::write(s.0.join("backing.txt"), "\r\n日本語\0\n").unwrap();
    let case = s.case("files.'nested/main.nib' = path`backing.txt`\nfiles.'resource.txt' = 'backing.txt'\nentry = 'nested/main.nib'\nload_error = 'missing dependency'\n");
    let input = prepare_input(&case, &s.0, &[]).unwrap();
    let PreparedInput::Bundle(plan) = &input else {
        panic!("missing bundle")
    };
    assert_eq!(plan.roots, ["nested/main.nib"]);
    assert_eq!(plan.files["nested/main.nib"], "\r\n日本語\0\n");
    assert_eq!(plan.files["resource.txt"], "backing.txt");
    assert_eq!(plan.files.len(), 2);
    let before = input.artifacts().unwrap();
    std::fs::write(s.0.join("backing.txt"), "changed").unwrap();
    let after = prepare_input(&case, &s.0, &[])
        .unwrap()
        .artifacts()
        .unwrap();
    assert_ne!(before["input_bundle_sha256"], after["input_bundle_sha256"]);
    assert_eq!(
        before["input_file_sha256:resource.txt"],
        after["input_file_sha256:resource.txt"]
    );
}

#[test]
fn unsupported_fixture_transformations_never_become_literal_program_inputs() {
    use selfhost_harness::shared_rustgen::prepare_input;
    use tauto_test_suite::selfhost::Actual;
    let s = InputScratch::new();
    for contents in ["{{par:example}}", "{{bytes:ff 00}}"] {
        let case = s.case(&format!(
            "files.'main.nib' = '{contents}'\nload_error = 'expected'\n"
        ));
        assert!(matches!(
            prepare_input(&case, &s.0, &[]),
            Err(Actual::Unsupported(_))
        ));
    }
    std::fs::write(s.0.join("binary.txt"), [0xff, 0x00]).unwrap();
    let case = s.case("files.'main.nib' = path`binary.txt`\nload_error = 'expected'\n");
    assert!(matches!(
        prepare_input(&case, &s.0, &[]),
        Err(Actual::Unsupported(_))
    ));
    let case = s.case("files.'main.nib' = path`missing.txt`\nload_error = 'expected'\n");
    assert!(matches!(
        prepare_input(&case, &s.0, &[]),
        Err(Actual::HarnessFailure(_))
    ));
    std::fs::create_dir(s.0.join("directory")).unwrap();
    let directory = s.case("files.'main.nib' = path`directory`\nload_error = 'expected'\n");
    assert!(
        matches!(prepare_input(&directory, &s.0, &[]), Err(Actual::HarnessFailure(message)) if message.contains("regular file"))
    );
    std::fs::File::create(s.0.join("large.txt"))
        .unwrap()
        .set_len(16 * 1024 * 1024 + 1)
        .unwrap();
    let large = s.case("files.'main.nib' = path`large.txt`\nload_error = 'expected'\n");
    assert!(
        matches!(prepare_input(&large, &s.0, &[]), Err(Actual::Unsupported(message)) if message.contains("byte limit"))
    );
    let tote = s.case("tote = path`missing-tote`\nextract = true\nchecks_all = 'ok'\n");
    assert!(matches!(
        prepare_input(&tote, &s.0, &[]),
        Err(Actual::Unsupported(_))
    ));
    let case = s.case("source = 'untouched'\nextract = true\nchecks_all = 'ok'\n");
    assert!(matches!(
        prepare_input(&case, &s.0, &[]),
        Err(Actual::Unsupported(_))
    ));
    let case =
        s.case("source = 'untouched'\nimports = [path`z.taut`, path`a.taut`]\nchecks_all = 'ok'\n");
    assert!(matches!(
        prepare_input(&case, &s.0, &[]),
        Err(Actual::Unsupported(_))
    ));
}

#[test]
fn disk_inputs_require_explicit_complete_allowlist_and_preserve_resource_bytes() {
    use selfhost_harness::shared_rustgen::{PreparedInput, prepare_input};
    use tauto_test_suite::selfhost::Actual;
    let s = InputScratch::new();
    std::fs::write(s.0.join("main.taut"), "original bytes").unwrap();
    std::fs::write(s.0.join("data.txt"), "\0\r\n").unwrap();
    let case = s.case("source = path`main.taut`\nload_error = 'expected'\n");
    assert!(matches!(
        prepare_input(&case, &s.0, &[]),
        Err(Actual::Unsupported(_))
    ));
    let PreparedInput::Bundle(plan) =
        prepare_input(&case, &s.0, &["main.taut".into(), "data.txt".into()]).unwrap()
    else {
        panic!("missing bundle")
    };
    assert_eq!(plan.roots, ["main.taut"]);
    assert_eq!(plan.files["main.taut"], "original bytes");
    assert_eq!(plan.files["data.txt"], "\0\r\n");
    assert!(matches!(
        prepare_input(
            &case,
            &s.0,
            &["main.taut".into(), "missing-member.txt".into()]
        ),
        Err(Actual::HarnessFailure(_))
    ));
    std::fs::write(s.0.join("invalid.txt"), [0xff]).unwrap();
    assert!(matches!(
        prepare_input(&case, &s.0, &["main.taut".into(), "invalid.txt".into()]),
        Err(Actual::Unsupported(_))
    ));
}

#[test]
fn tote_input_selection_preserves_all_payloads_without_dependency_entry_roots() {
    use selfhost_harness::shared_rustgen::{PreparedInput, prepare_input};
    use tauto_test_suite::selfhost::Actual;
    let s = InputScratch::new();
    let case = s.case("files.'app/Tauto.eure' = 'package { name = \"app\" version = \"0.1.0\" } dependencies.dep.path = \"../dep\"'\nfiles.'dep/Tauto.eure' = 'package { name = \"dep\" version = \"0.1.0\" }'\nfiles.'app/src/main.taut' = 'entry bytes'\nfiles.'app/src/z.tauto' = 'legacy bytes'\nfiles.'app/resource.txt' = 'resource bytes'\nfiles.'dep/src/lib.taut' = 'dependency bytes'\nfiles.'dep/src/main.taut' = 'unused dependency entry bytes'\nfiles_tote = 'app'\nload_error = 'expected'\n");
    let PreparedInput::Bundle(plan) = prepare_input(&case, &s.0, &[]).unwrap() else {
        panic!("missing bundle")
    };
    assert_eq!(
        plan.roots,
        ["dep/src/lib.taut", "app/src/z.tauto", "app/src/main.taut"]
    );
    assert_eq!(plan.files.len(), 7);
    assert_eq!(
        plan.files["dep/src/main.taut"],
        "unused dependency entry bytes"
    );
    assert_eq!(plan.files["app/resource.txt"], "resource bytes");
    let case = s.case("files.'app/Tauto.eure' = 'package { name = \"app\" } rust.types.Handle = \"HostHandle\"'\nfiles.'app/src/main.taut' = 'entry bytes'\nfiles_tote = 'app'\nload_error = 'expected'\n");
    assert!(matches!(
        prepare_input(&case, &s.0, &[]),
        Err(Actual::Unsupported(_))
    ));
}

#[test]
fn load_contract_uses_actual_stage_not_matching_text_or_inventory_success() {
    use selfhost_harness::shared_rustgen::{BundleResult, bundle_code};
    use tauto_test_suite::selfhost::{Backend, Implementation, Observation, Verdict, assess_route};
    let s = InputScratch::new();
    let case = s.case("files.'main.nib' = ''\nload_error = 'specific diagnostic'\n");
    let assess = |result| {
        let (stage, actual) = bundle_code(result, true).unwrap_err();
        assess_route(
            &case,
            Backend::Rust,
            Backend::Javascript,
            &[Observation {
                requirement: "load_error".into(),
                stage: stage.into(),
                implementation: Implementation::Tauto,
                compiler_backend: Backend::Rust,
                target_backend: Some(Backend::Javascript),
                actual,
            }],
        )
    };
    assert_eq!(
        assess(BundleResult::LoadRejected("specific diagnostic".into())),
        Verdict::Passed
    );
    assert!(matches!(
        assess(BundleResult::SourceRejected("specific diagnostic".into())),
        Verdict::Failed(_)
    ));
    assert!(matches!(
        assess(BundleResult::LoadRejected("different diagnostic".into())),
        Verdict::Failed(_)
    ));
    assert!(matches!(
        assess(BundleResult::InputComplete("S\tmain.nib\t0\t0\n".into())),
        Verdict::Incomplete(_)
    ));
    assert!(matches!(
        assess(BundleResult::Unsupported {
            stage: "input-audit",
            reason: "specific diagnostic".into()
        }),
        Verdict::Incomplete(_)
    ));
    assert!(matches!(
        assess(BundleResult::Generated("code".into())),
        Verdict::Failed(_)
    ));
}

#[cfg(unix)]
#[test]
fn explicit_disk_and_virtual_backing_symlinks_cannot_bypass_input_identity() {
    use selfhost_harness::shared_rustgen::prepare_input;
    use tauto_test_suite::selfhost::Actual;
    let s = InputScratch::new();
    std::fs::write(s.0.join("main.taut"), "original bytes").unwrap();
    let case = s.case("source = path`alias.taut`\nload_error = 'expected'\n");
    std::os::unix::fs::symlink(s.0.join("main.taut"), s.0.join("alias.taut")).unwrap();
    assert!(
        matches!(prepare_input(&case, &s.0, &["main.taut".into()]), Err(Actual::HarnessFailure(message)) if message.contains("symlink"))
    );
    std::fs::remove_file(s.0.join("alias.taut")).unwrap();
    let case = s.case("files.'main.nib' = path`alias.taut`\nload_error = 'expected'\n");
    std::os::unix::fs::symlink(s.0.join("main.taut"), s.0.join("alias.taut")).unwrap();
    assert!(
        matches!(prepare_input(&case, &s.0, &[]), Err(Actual::HarnessFailure(message)) if message.contains("symlink"))
    );
    std::fs::remove_file(s.0.join("alias.taut")).unwrap();
    std::fs::create_dir(s.0.join("app")).unwrap();
    let case = s.case("tote = path`alias-app`\nload_error = 'expected'\n");
    std::os::unix::fs::symlink(s.0.join("app"), s.0.join("alias-app")).unwrap();
    assert!(
        matches!(prepare_input(&case, &s.0, &["app/Tauto.eure".into()]), Err(Actual::HarnessFailure(message)) if message.contains("symlink"))
    );
}

#[test]
fn resource_audit_rejection_is_neither_language_load_nor_macro_acceptance() {
    use selfhost_harness::{
        RunOutput,
        shared_rustgen::{bundle_code, bundle_result},
    };
    use tauto_test_suite::selfhost::{
        Actual, Backend, Implementation, Observation, Verdict, assess_route,
    };
    let s = InputScratch::new();
    let output = RunOutput {
        stdout: String::new(),
        stderr: "TAUTO-RUSTGEN-CONTRACT/2 resource-rejected\nrustgen: include.outside\n".into(),
        exit: Some(1),
        error: None,
    };
    for requirement in ["load_error", "macro_error"] {
        let case = s.case(&format!(
            "files.'main.nib' = ''\n{requirement} = 'include.outside'\n"
        ));
        let (stage, actual) = bundle_code(bundle_result(&output).unwrap(), true).unwrap_err();
        assert_eq!(stage, "resource-audit");
        assert!(
            matches!(&actual, Actual::Unsupported(reason) if reason.contains("include.outside"))
        );
        assert!(matches!(
            assess_route(
                &case,
                Backend::Rust,
                Backend::Rust,
                &[Observation {
                    requirement: requirement.into(),
                    stage: stage.into(),
                    implementation: Implementation::Tauto,
                    compiler_backend: Backend::Rust,
                    target_backend: Some(Backend::Rust),
                    actual,
                }]
            ),
            Verdict::Incomplete(_)
        ));
    }
}

#[test]
fn reader_protocol_requires_a_structured_semantic_diagnostic() {
    use selfhost_harness::{
        RunOutput,
        shared_rustgen::{BundleResult, bundle_code, bundle_result},
    };
    use tauto_test_suite::selfhost::Actual;
    let failure = |stage: &str, diagnostic: &str| RunOutput {
        stdout: String::new(),
        stderr: format!("TAUTO-RUSTGEN-CONTRACT/2 {stage}\nrustgen: {diagnostic}\n"),
        exit: Some(1),
        error: None,
    };
    let diagnostic = "lib/part.taut:20:47: include.read: resource is not supplied";
    let result = bundle_result(&failure("reader-rejected", diagnostic)).unwrap();
    let BundleResult::ReaderRejected(ref parsed) = result else {
        panic!("{result:?}")
    };
    assert_eq!(parsed.origin, "lib/part.taut");
    assert_eq!((parsed.start, parsed.end), (20, 47));
    assert_eq!(parsed.code, "include.read");
    assert!(
        matches!(bundle_code(result.clone(), false), Err(("macro", Actual::Rejected(message))) if message == diagnostic)
    );
    assert!(matches!(
        bundle_code(result, true),
        Err(("input-audit", Actual::HarnessFailure(_)))
    ));
    for invalid in [
        "include.read: guessed from matching text",
        "../part.taut:20:47: include.read: outside ID",
        "part.taut:47:20: include.read: backwards span",
        "part.taut:0:16777217: include.read: oversized span",
        "part.taut:0:1: macro.include_text: evaluator did not run",
        "part.taut:0:1: reader.limit: exhaustion is not a rejection",
        "part.taut:0:1: include.read: ",
    ] {
        assert!(
            bundle_result(&failure("reader-rejected", invalid)).is_err(),
            "{invalid}"
        );
    }
    let mut crashed = failure("reader-rejected", diagnostic);
    crashed.exit = Some(101);
    assert!(bundle_result(&crashed).is_err());
    let mut partial = failure("reader-rejected", diagnostic);
    partial.stdout = "partial target".into();
    assert!(bundle_result(&partial).is_err());
    for stage in [
        "resource-rejected",
        "input-unsupported",
        "reader-unsupported",
    ] {
        assert!(
            matches!(
                bundle_code(bundle_result(&failure(stage, diagnostic)).unwrap(), false),
                Err((_, Actual::Unsupported(_)))
            ),
            "{stage}"
        );
    }
}

#[test]
fn reader_completion_cannot_satisfy_macro_expansion_or_compilation() {
    use selfhost_harness::{
        RunOutput,
        shared_rustgen::{bundle_code, bundle_result},
    };
    use tauto_test_suite::selfhost::Actual;
    let output = RunOutput {
        stdout: "S\tmain.taut\t0\t0\nTAUTO-READER-SURFACE/1\nProgram [0]\n".into(),
        stderr: "TAUTO-RUSTGEN-CONTRACT/2 reader-complete\n".into(),
        exit: Some(0),
        error: None,
    };
    let result = bundle_result(&output).unwrap();
    assert!(matches!(
        bundle_code(result.clone(), false),
        Err(("reader", Actual::Unsupported(_)))
    ));
    assert!(matches!(
        bundle_code(result, true),
        Err(("input-audit", Actual::HarnessFailure(_)))
    ));
    for malformed in [
        "",
        "S\tmain.taut\t0\t0\n",
        "TAUTO-READER-SURFACE/1\nProgram [0]\n",
        "S\tmain.taut\t0\t0\nTAUTO-READER-SURFACE/1\n",
    ] {
        let mut bad = output.clone();
        bad.stdout = malformed.into();
        assert!(bundle_result(&bad).is_err());
    }
}
