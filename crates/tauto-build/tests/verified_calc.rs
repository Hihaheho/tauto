//! The existing calc parser and compiler are checked and called from Rust.
use std::path::{Path, PathBuf};
use std::process::Command;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}
fn write(dir: &Path, path: &str, text: &str) {
    let file = dir.join(path);
    std::fs::create_dir_all(file.parent().unwrap()).unwrap();
    std::fs::write(file, text).unwrap();
}
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join("tauto-build-tests").join(name);
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}
fn copy_example(dir: &Path, name: &str) {
    let source = root().join("examples").join(name);
    write(
        dir,
        &format!("{name}/Tauto.eure"),
        &std::fs::read_to_string(source.join("Tauto.eure")).unwrap(),
    );
    for subdir in ["src", "proof", ".tauto-syntax"] {
        let path = source.join(subdir);
        if !path.exists() {
            continue;
        }
        for entry in std::fs::read_dir(path).unwrap() {
            let entry = entry.unwrap();
            let content = std::fs::read_to_string(entry.path())
                .unwrap()
                .replace("../../../std/", &format!("{}/std/", root().display()));
            write(
                dir,
                &format!("{name}/{subdir}/{}", entry.file_name().to_string_lossy()),
                &content,
            );
        }
    }
}
fn cargo(dir: &Path, args: &[&str]) -> std::process::Output {
    Command::new(std::env::var("CARGO").unwrap_or_else(|_| "cargo".into()))
        .args(args)
        .current_dir(dir)
        .env(
            "CARGO_TARGET_DIR",
            std::env::temp_dir().join("tauto-build-tests/target"),
        )
        .env("CARGO_TERM_COLOR", "never")
        .output()
        .unwrap()
}

#[test]
fn rust_calls_the_existing_calc_parser_optimizer_and_stack_machine() {
    tauto_messages::install();
    let dir = scratch("verified-calc");
    for name in ["calc", "compiler"] {
        copy_example(&dir, name);
    }
    for file in ["Cargo.lock", ".cargo/config.toml", "rust-toolchain.toml"] {
        write(
            &dir,
            file,
            &std::fs::read_to_string(root().join(file)).unwrap(),
        );
    }
    write(
        &dir,
        "Cargo.toml",
        &format!(
            "[package]\nname = \"host-verified-calc\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\ntauto-rt = {{ path = {:?} }}\n[build-dependencies]\ntauto-build = {{ path = {:?} }}\n[workspace]\n",
            root().join("crates/tauto-rt"),
            root().join("crates/tauto-build")
        ),
    );
    write(
        &dir,
        "build.rs",
        "fn main() { tauto_build::compile(\"calc/Tauto.eure\").unwrap(); }\n",
    );
    write(
        &dir,
        "src/main.rs",
        r#"
mod calc { include!(concat!(env!("OUT_DIR"), "/tauto_calc.rs")); }
fn accept<T>(value: Result<T, calc::CalcFailure>) -> T {
    match value { Ok(value) => value, Err(_) => panic!("valid bounded calculation") }
}
fn stack_top(value: Option<calc::List<tauto_rt::Nat>>) -> tauto_rt::Nat {
    match value {
        Some(calc::List::Cons(top, rest)) => {
            assert!(matches!(&*rest, calc::List::Nil)); top
        }
        _ => panic!("one result, no stack underflow"),
    }
}
fn main() {
    for (source, expected) in [("0", 0), ("12", 12), ("1 + 2 * 3", 7), ("(2 + 3) * (4 + 5)", 45), ("(7+0)*1", 7), ("12345 * 6789", 83810205)] {
        let expected = tauto_rt::Nat::from_u64(expected);
        let original = accept(calc::calc_read(tauto_rt::Text::from(source), 100000));
        let folded = accept(calc::calc_fold_bounded(original.clone(), 100000));
        assert!(matches!(&folded, calc::Expr::ELit(value) if *value == expected));
        assert_eq!(accept(calc::calc_eval_bounded(original.clone(), 100000)), expected);
        assert_eq!(accept(calc::calc_eval_bounded(folded.clone(), 100000)), expected);
        assert_eq!(stack_top(accept(calc::calc_run_bounded(original, 100000))), expected);
        assert_eq!(stack_top(accept(calc::calc_run_bounded(folded, 100000))), expected);
    }
    let ast = match calc::calc_parse(tauto_rt::Text::from("12")) { Ok(ast) => ast, Err(_) => panic!("raw AST") };
    assert_eq!(ast.span.id, 0);
    for source in ["2 + * 3", "(", "日本語", "1 trailing"] {
        let raw = match calc::calc_parse(tauto_rt::Text::from(source)) { Err(diag) => diag, Ok(_) => panic!("invalid expression") };
        let domain = match calc::calc_read(tauto_rt::Text::from(source), 100000) {
            Err(calc::CalcFailure::CalcParseFailed(diag)) => diag,
            _ => panic!("syntax error is not budget exhaustion"),
        };
        assert_eq!(&*domain.code, "macro.syntax_error");
        assert_eq!(domain.at, raw.at);
        assert_eq!(&*domain.message, &*raw.message);
    }
    for steps in [0, -1] {
        assert!(matches!(calc::calc_read(tauto_rt::Text::from("1"), steps), Err(calc::CalcFailure::CalcBudgetExceeded)));
        assert!(matches!(calc::calc_fold_bounded(calc::Expr::ELit(tauto_rt::Nat::from_u64(1)), steps), Err(calc::CalcFailure::CalcBudgetExceeded)));
        assert!(matches!(calc::calc_eval_bounded(calc::Expr::ELit(tauto_rt::Nat::from_u64(1)), steps), Err(calc::CalcFailure::CalcBudgetExceeded)));
        assert!(matches!(calc::calc_run_bounded(calc::Expr::ELit(tauto_rt::Nat::from_u64(1)), steps), Err(calc::CalcFailure::CalcBudgetExceeded)));
    }
    println!("existing calc proof-backed functions called from Rust");
}
"#,
    );
    let built = cargo(&dir, &["build", "--quiet", "--offline"]);
    assert!(
        built.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&built.stdout),
        String::from_utf8_lossy(&built.stderr)
    );
    let binary = std::env::temp_dir().join("tauto-build-tests/target/debug/host-verified-calc");
    let standalone = dir.join("standalone");
    std::fs::copy(binary, &standalone).unwrap();
    for name in ["calc", "compiler"] {
        std::fs::remove_dir_all(dir.join(name)).unwrap();
    }
    let run = Command::new(standalone).current_dir(&dir).output().unwrap();
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&run.stdout),
        "existing calc proof-backed functions called from Rust\n"
    );
}

#[test]
fn mutating_the_real_constant_folder_rejects_rust_generation() {
    tauto_messages::install();
    let dir = scratch("wrong-calc-folder");
    for name in ["calc", "compiler"] {
        copy_example(&dir, name);
    }
    let (_, module, warnings) = tauto_build::generate(&dir.join("calc/Tauto.eure"), None).unwrap();
    assert!(warnings.is_empty(), "{warnings:?}");
    let facade = module.split("pub mod api").nth(1).unwrap();
    for name in [
        "calc_parse",
        "calc_read",
        "calc_fold_bounded",
        "calc_eval_bounded",
        "calc_run_bounded",
    ] {
        assert!(facade.contains(&format!("pub fn {name}")));
    }
    assert!(!facade.contains("pub fn fold_expr"));
    let path = dir.join("compiler/src/compiler.taut");
    let source = std::fs::read_to_string(&path).unwrap();
    let before = "ELit(Nat::add(n, m))";
    assert_eq!(source.matches(before).count(), 1);
    std::fs::write(path, source.replace(before, "ELit(Nat::mul(n, m))")).unwrap();
    let error = tauto_build::generate(&dir.join("calc/Tauto.eure"), None).unwrap_err();
    assert!(error.contains("fold_add_correct"), "{error}");
    assert!(
        !error.contains("unexpected") && !error.contains("not defined"),
        "{error}"
    );
}

#[test]
fn existing_calc_proofs_are_axiom_free_and_the_evaluator_still_runs() {
    tauto_messages::install();
    std::thread::Builder::new().stack_size(256 << 20).spawn(|| {
        let example = root().join("examples/calc");
        tauto::syntax::with_search_dirs(vec![example.clone()], || {
            let entries = tauto::check::check_file(&example.join("proof/calc.taut")).unwrap();
            for required in ["lower_expr_ok", "fold_correct", "calc_run_correct", "calc_run_folded_correct"] {
                assert!(entries.iter().any(|entry| entry.entry.name == required));
            }
            for entry in entries {
                match entry.entry.verdict {
                    tauto::check::Verdict::Checked { axioms } => assert!(axioms.is_empty(), "{}: {axioms:?}", entry.entry.name),
                    tauto::check::Verdict::Skipped(_) if entry.entry.name.ends_with("::parse") || entry.entry.name.ends_with("::to_i") => {},
                    other => panic!("{}: {other:?}", entry.entry.name),
                }
            }
            let loaded = tauto::program::load_tote(&example).unwrap();
            let run = tauto::eval::run_program_with(&loaded.program, 100_000_000, Default::default()).unwrap();
            assert_eq!(run.stdout, "(2 + 3) * (4 + 5) => 45\n1 + 2 * 3 => 7\n2 + * 3 => error: macro.syntax_error: in arith: expected Num or LParen, found Star\n");
        });
    }).unwrap().join().unwrap();
}
