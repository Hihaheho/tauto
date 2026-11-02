//! Producer-side protocol checks preserve the ordinary CLI and distinguish
//! infrastructure errors from source-language diagnostics.
use selfhost_harness::{materialize, run_tote_native, shared_rustgen::compiler_result};

#[test]
fn opt_in_contract_reports_compilation_without_changing_default_output() {
    let inputs = materialize(
        "rustgen-contract",
        &[
            (
                "accepted".into(),
                r#"fn pred(n: Nat): Nat { match n: Nat { Zero => 0
Succ(k) => k } }
fn answer(): Nat { pred(0) }"#
                    .to_string(),
            ),
            (
                "rejected".into(),
                r#"fn f(succ: Nat): Nat { succ(1) }
fn answer(): Nat { f(2) }"#
                    .to_string(),
            ),
        ],
    );
    let run = |contract: bool, path: &str| {
        let mut args = Vec::new();
        if contract {
            args.push("--contract".into());
        }
        args.extend([path.into(), "answer".into()]);
        run_tote_native("rustgen", &args, 200_000_000_000)
    };
    let ordinary = run(false, &inputs.paths[0]);
    assert_eq!(ordinary.exit, Some(0), "{ordinary:?}");
    assert!(
        ordinary.error.is_none() && ordinary.stderr.is_empty(),
        "{ordinary:?}"
    );
    let tagged = run(true, &inputs.paths[0]);
    assert_eq!(compiler_result(&tagged).unwrap(), Ok(ordinary.stdout));
    let ordinary_error = run(false, &inputs.paths[1]);
    assert_eq!(ordinary_error.exit, Some(1), "{ordinary_error:?}");
    assert!(ordinary_error.error.is_none() && ordinary_error.stdout.is_empty());
    let tagged_error = run(true, &inputs.paths[1]);
    assert_eq!(
        compiler_result(&tagged_error).unwrap(),
        Err(ordinary_error.stderr)
    );
    let missing = run(
        true,
        inputs.dir.join("does-not-exist.taut").to_str().unwrap(),
    );
    assert_eq!(missing.exit, Some(1), "{missing:?}");
    assert!(
        missing
            .stderr
            .starts_with("TAUTO-RUSTGEN-CONTRACT/1 input-error\n")
    );
    assert!(compiler_result(&missing).is_err());
    std::fs::remove_dir_all(inputs.dir).unwrap();
}
