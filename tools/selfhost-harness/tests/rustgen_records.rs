//! Single-constructor records and the exact production record planner.
use selfhost_harness::{materialize, root, run_tote_native};
use std::process::Command;

const CASES: &str = "selfhost-rustgen-records.eure";

fn generate(path: String) -> selfhost_harness::RunOutput {
    run_tote_native("rustgen", &[path, "answer".into()], 200_000_000_000)
}

#[test]
fn records_preserve_types_fields_and_written_evaluation_order() {
    let cases = selfhost_harness::selfhost_cases(CASES);
    let production = ["types", "bindings", "record_core"]
        .into_iter()
        .map(|name| {
            std::fs::read_to_string(root().join(format!("totes/rustgen/src/{name}.taut"))).unwrap()
        })
        .chain([r#"fn answer(): Bool {
  let fields := Cons(RustgenRecordField::Mk("second", RustgenValue::Mk(RustgenInt, "2"), "local0"),
    Cons(RustgenRecordField::Mk("first", RustgenValue::Mk(RustgenText, "text"), "local1"), Nil))
  let params := Cons(RustgenBinding::Mk("first", RustgenText),
    Cons(RustgenBinding::Mk("second", RustgenInt), Nil))
  let valid := rustgen_record_unique(fields)
  let duplicate := Cons(RustgenRecordField::Mk("first", RustgenValue::Mk(RustgenInt, "3"), "local2"), fields)
  let order := rustgen_record_bindings(fields) == "let local0 = 2; let local1 = text; "
  let arranged := match rustgen_record_arguments(params, fields): Bool {
    RustgenErr(message) => false
    RustgenOk(values) => match values: Bool {
      Nil => false
      Cons(first, rest) => match rest: Bool {
        Nil => false
        Cons(second, tail) => first.code == "local1" && second.code == "local0" && rustgen_same(first.ty, RustgenText)
      }
    }
  }
  valid && not(rustgen_record_unique(duplicate)) && order && arranged
}
"#.to_string()])
        .collect::<Vec<_>>()
        .join("\n");
    let inputs = cases
        .iter()
        .map(|case| (case.name.clone(), case.source.clone()))
        .chain([("production-record-core".into(), production)])
        .collect::<Vec<_>>();
    let files = materialize("rustgen-records", &inputs);
    let generated = files.dir.join("generated");
    std::fs::create_dir_all(generated.join("src")).unwrap();
    std::fs::write(generated.join("Cargo.toml"), format!(
        "[package]\nname=\"rustgen-records\"\nversion=\"0.0.0\"\nedition=\"2024\"\n[dependencies]\ntauto-rt={{path={:?}}}\n[workspace]\n", root().join("crates/tauto-rt"))).unwrap();
    for (index, (name, _)) in inputs.iter().enumerate() {
        let output = generate(files.paths[index].clone());
        assert_eq!(output.error, None, "{name}: {output:?}");
        let case = cases.iter().find(|case| &case.name == name);
        if let Some(want) = case.and_then(|case| case.compile_error.as_ref()) {
            assert_eq!(output.exit, Some(1), "{name}: {output:?}");
            assert!(
                output.stdout.is_empty(),
                "{name}: partial output on failure"
            );
            assert!(output.stderr.contains(want.as_str()), "{name}: {output:?}");
            continue;
        }
        assert_eq!(output.exit, Some(0), "{name}: {output:?}");
        assert!(output.stderr.is_empty(), "{name}: {output:?}");
        if name == "production-record-core" {
            assert_eq!(
                output,
                generate(files.paths[index].clone()),
                "production planner output must be deterministic"
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
        if let Some(want) = case.and_then(|case| case.run_error.as_ref()) {
            assert_eq!(executed.status.code(), Some(1));
            let stderr = String::from_utf8_lossy(&executed.stderr);
            assert!(stderr.contains(want.as_str()), "{stderr}");
            assert!(!stderr.contains("<input>:2:"), "{stderr}");
        } else {
            assert!(
                executed.status.success(),
                "{name}: {}",
                String::from_utf8_lossy(&executed.stderr)
            );
            let expected = if name == "production-record-core" {
                "true\n".into()
            } else {
                case.and_then(|case| case.stdout.clone())
                    .unwrap_or_else(|| panic!("{name}: no selfhost_stdout"))
            };
            assert_eq!(
                String::from_utf8_lossy(&executed.stdout),
                expected,
                "{name}"
            );
        }
    }
}

#[test]
fn production_record_planner_equations_are_kernel_checked() {
    let entries =
        tauto::check::check_file(&root().join("totes/rustgen/tests/records.taut")).unwrap();
    let proofs = entries
        .iter()
        .filter(|entry| {
            matches!(
                entry.entry.name.as_str(),
                "rg_record_unique"
                    | "rg_record_duplicate"
                    | "rg_record_lookup_preserves_type"
                    | "rg_record_missing_rejects"
                    | "rg_record_written_order"
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(proofs.len(), 5);
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
