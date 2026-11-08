//! Owned pure callable values, fail-closed row checking, and production capture planning.
use selfhost_harness::{materialize, root, run_tote_native};
use std::path::Path;
use std::process::Command;
use tauto::eval::{RunOptions, run_program_with};
use tauto::surface::parse_program_as_written;

const CASES: &str = "selfhost-rustgen-closures.eure";
#[derive(Clone, Copy)]
enum ReferenceRoute {
    WrittenRuntime,
    WrittenText,
    Extracted,
}

const ACCEPTED: &[(&str, ReferenceRoute)] = &[
    ("annotated_identity", ReferenceRoute::WrittenRuntime),
    ("omitted_row_is_known_empty", ReferenceRoute::WrittenRuntime),
    ("direct_function_value", ReferenceRoute::WrittenRuntime),
    ("immutable_text_capture", ReferenceRoute::WrittenText),
    ("capture_is_reusable", ReferenceRoute::WrittenRuntime),
    ("nested_closures", ReferenceRoute::WrittenRuntime),
    ("conditional_closures", ReferenceRoute::WrittenRuntime),
    ("capture_callable", ReferenceRoute::WrittenRuntime),
    (
        "generic_call_infers_callable",
        ReferenceRoute::WrittenRuntime,
    ),
    ("generic_container", ReferenceRoute::Extracted),
    ("shadowed_callable_name", ReferenceRoute::WrittenRuntime),
    ("match_capture_shadowing", ReferenceRoute::Extracted),
    ("zero_arguments", ReferenceRoute::WrittenRuntime),
    ("nat_result_context", ReferenceRoute::Extracted),
    (
        "direct_recursion_remains_supported",
        ReferenceRoute::Extracted,
    ),
    ("generic_factory_integer", ReferenceRoute::WrittenRuntime),
    ("generic_factory_bool", ReferenceRoute::WrittenRuntime),
    (
        "result_erased_large_callable_argument",
        ReferenceRoute::WrittenRuntime,
    ),
    (
        "generic_record_callable_projection",
        ReferenceRoute::Extracted,
    ),
    ("multiple_arguments", ReferenceRoute::WrittenRuntime),
];
/// The cases of the file: the rejected ones are those with
/// `selfhost_compile_error`; every other one has its route in `ACCEPTED`.
fn cases() -> Vec<selfhost_harness::SelfhostCase> {
    let cases = selfhost_harness::selfhost_cases(CASES);
    for case in &cases {
        assert!(
            case.compile_error.is_some() || ACCEPTED.iter().any(|(name, _)| *name == case.name),
            "{}: an accepted case needs a reference route",
            case.name
        );
    }
    cases
}

fn rejected() -> Vec<selfhost_harness::SelfhostCase> {
    cases()
        .into_iter()
        .filter(|case| case.compile_error.is_some())
        .collect()
}

fn source(name: &str) -> String {
    cases()
        .into_iter()
        .find(|case| case.name == name)
        .unwrap_or_else(|| panic!("{CASES} has no case {name}"))
        .source
}

fn generate(path: &str) -> selfhost_harness::RunOutput {
    run_tote_native("rustgen", &[path.into(), "answer".into()], 200_000_000_000)
}

fn production_source() -> String {
    ["types", "bindings", "closure_core"]
        .into_iter()
        .map(|name| {
            std::fs::read_to_string(root().join(format!("totes/rustgen/src/{name}.taut"))).unwrap()
        })
        .chain(
            [r#"fn rustgen_probe_binding(binding: RustgenBinding): Bool {
  rustgen_type_tag(binding.ty) == 0
}
fn answer(): Bool {
  let first := RustgenBinding { name: "value", ty: RustgenInt }
  let hidden := RustgenBinding { name: "value", ty: RustgenText }
  let visible := rustgen_closure_visible(Cons(first, Cons(hidden, Nil)), Nil)
  let inspect: (RustgenBinding) -> Bool := binding => rustgen_probe_binding(binding)
  ⊢ Bool from match visible {
    Nil => false
    Cons(binding, rest) => inspect(binding) && rustgen_captures_concrete(visible)
  }
}
"#
            .to_string()],
        )
        .collect::<Vec<_>>()
        .join("\n")
}

fn expected_output(name: &str) -> String {
    if name == "production-closure-core" {
        "true\n".into()
    } else {
        cases()
            .into_iter()
            .find(|case| case.name == name)
            .and_then(|case| case.stdout)
            .unwrap_or_else(|| panic!("{name}: no selfhost_stdout"))
    }
}

fn reference_tote(path: &Path) {
    std::fs::create_dir_all(path.join("src")).unwrap();
    std::fs::write(path.join("Tauto.eure"), "package { name = \"reference\" }").unwrap();
}

fn runtime_text_library() -> String {
    // Non-mixed extraction retains the standard mapped wrappers (including
    // text_concat); loading an import-only tote prunes them as unreachable.
    tauto::extract::extract_files(&[root().join("std/Text.taut")])
        .expect("the exact standard Text library must extract")
}

fn check_reference(name: &str, source: &str, text_runtime: &str, reference: &Path) {
    let route = if name == "production-closure-core" {
        ReferenceRoute::Extracted
    } else {
        ACCEPTED
            .iter()
            .find(|(id, _)| *id == name)
            .expect("every accepted case has an explicit reference route")
            .1
    };
    let program = match route {
        ReferenceRoute::Extracted => {
            std::fs::write(
                reference.join("src/main.taut"),
                format!(
                    r#"import {}
{}
perform show("result", answer())"#,
                    format!("{:?}", root().join("std/Text.taut")),
                    source
                ),
            )
            .unwrap();
            tauto::program::load_tote(reference)
                .unwrap_or_else(|error| panic!("{name}: extracted reference: {error}"))
                .program
        }
        ReferenceRoute::WrittenRuntime | ReferenceRoute::WrittenText => {
            // Preserve the case verbatim and parse library plus case together,
            // so all source spans belong to the same parse.
            parse_program_as_written(&format!(
                r#"{}
{}
perform show("result", answer())"#,
                text_runtime, source
            ))
            .unwrap_or_else(|error| panic!("{name}: written reference: {error}"))
        }
    };
    let oracle = run_program_with(&program, 1_000_000, RunOptions::default())
        .unwrap_or_else(|error| panic!("{name}: host evaluator reference: {error:?}"));
    assert_eq!(oracle.outputs.len(), 1, "{name}: reference output count");
    let expected = expected_output(name);
    let raw = expected
        .strip_suffix('\n')
        .expect("native output ends in one newline");
    // `show` uses Value::Display: Text is quoted/escaped, unlike native stdout.
    // This exact case metadata changes only the observer representation.
    let shown = match route {
        ReferenceRoute::WrittenText => tauto::eval::Value::Text(raw.into()).to_string(),
        _ => raw.to_string(),
    };
    assert_eq!(shown, oracle.outputs[0].1, "{name}: host evaluator oracle");
}

#[test]
fn all_shared_closure_inputs_parse_before_semantic_contracts() {
    let inputs = ACCEPTED
        .iter()
        .map(|(name, _)| *name)
        .map(|name| (name.to_string(), source(name)))
        .chain(rejected().into_iter().map(|case| (case.name, case.source)))
        .chain([("production-closure-core".into(), production_source())]);
    let mut failed = Vec::new();
    for (name, source) in inputs {
        match parse_program_as_written(&source) {
            Ok(program) if program.errors.is_empty() => eprintln!("PARSE PASSED: {name}"),
            result => {
                eprintln!("PARSE FAILED: {name}: {result:?}");
                failed.push(name);
            }
        }
    }
    assert!(failed.is_empty(), "malformed semantic fixtures: {failed:?}");
}

#[test]
fn accepted_closure_references_run_without_native_compiler_setup() {
    let inputs = ACCEPTED
        .iter()
        .map(|(name, _)| (name.to_string(), source(name)))
        .chain([("production-closure-core".into(), production_source())])
        .collect::<Vec<_>>();
    let files = materialize("rustgen-closure-references", &inputs);
    let reference = files.dir.join("reference");
    reference_tote(&reference);
    let text_runtime = runtime_text_library();
    let mut failed = Vec::new();
    for (name, source) in inputs {
        // Record every independent reference outcome; a blocked extraction or
        // failed assertion remains a test failure after the other cases run.
        let result = std::panic::catch_unwind(|| {
            check_reference(&name, &source, &text_runtime, &reference);
        });
        if result.is_err() {
            eprintln!("REFERENCE FAILED: {name}");
            failed.push(name);
        } else {
            eprintln!("REFERENCE PASSED: {name}");
        }
    }
    assert!(failed.is_empty(), "failed host references: {failed:?}");
}

#[test]
fn pure_closures_preserve_owned_values_and_reject_unproved_effects() {
    let production = production_source();
    let inputs = ACCEPTED
        .iter()
        .map(|(name, _)| *name)
        .map(|name| (name.to_string(), source(name)))
        .chain(rejected().into_iter().map(|case| (case.name, case.source)))
        .chain([("production-closure-core".into(), production)])
        .collect::<Vec<_>>();
    let files = materialize("rustgen-closures", &inputs);
    let generated = files.dir.join("generated");
    std::fs::create_dir_all(generated.join("src")).unwrap();
    std::fs::write(generated.join("Cargo.toml"), format!(
        "[package]\nname=\"rustgen-closures\"\nversion=\"0.0.0\"\nedition=\"2024\"\n[dependencies]\ntauto-rt={{path={:?}}}\n[workspace]\n", root().join("crates/tauto-rt"))).unwrap();
    for (index, (name, _source)) in inputs.iter().enumerate() {
        let output = generate(&files.paths[index]);
        assert_eq!(output.error, None, "{name}: {output:?}");
        if let Some(want) = rejected()
            .into_iter()
            .find(|case| &case.name == name)
            .and_then(|case| case.compile_error)
        {
            assert_eq!(output.exit, Some(1), "{name}: {output:?}");
            assert!(
                output.stdout.is_empty(),
                "{name}: partial output on failure"
            );
            assert!(output.stderr.contains(&want), "{name}: {output:?}");
            eprintln!("NATIVE REJECTION PASSED: {name}");
            continue;
        }
        assert_eq!(output.exit, Some(0), "{name}: {output:?}");
        assert!(output.stderr.is_empty(), "{name}: {output:?}");
        if name == "production-closure-core" {
            assert_eq!(
                output,
                generate(&files.paths[index]),
                "deterministic production output"
            );
        }
        std::fs::write(generated.join("src/main.rs"), output.stdout).unwrap();
        let executed = Command::new(env!("CARGO"))
            .current_dir(&generated)
            .env("CARGO_TARGET_DIR", files.dir.join("target"))
            .env("CARGO_BUILD_BUILD_DIR", files.dir.join("build"))
            .args(["run", "--offline", "--quiet"])
            .output()
            .unwrap();
        assert!(
            executed.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&executed.stderr)
        );
        let expected = expected_output(name);
        assert_eq!(
            String::from_utf8_lossy(&executed.stdout),
            expected,
            "{name}"
        );
        eprintln!("NATIVE EXECUTION PASSED: {name}");
    }
}

#[test]
fn callable_type_and_capture_equations_are_kernel_checked() {
    let entries =
        tauto::check::check_file(&root().join("totes/rustgen/tests/closures.taut")).unwrap();
    let proofs = entries
        .iter()
        .filter(|entry| entry.entry.name.starts_with("rg_pure_"))
        .collect::<Vec<_>>();
    assert_eq!(proofs.len(), 11);
    for proof in proofs {
        assert!(
            matches!(&proof.entry.verdict,
                tauto::check::Verdict::Checked { axioms } if axioms.is_empty()),
            "{}: {:?}",
            proof.entry.name,
            proof.entry.verdict
        );
    }
    for entry in entries {
        assert!(
            !matches!(
                &entry.entry.verdict,
                tauto::check::Verdict::Failed(_) | tauto::check::Verdict::Incomplete { .. }
            ),
            "{}: {:?}",
            entry.entry.name,
            entry.entry.verdict
        );
    }
}
