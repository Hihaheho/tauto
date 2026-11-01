//! Execute generated modules and compare with the reference evaluator.
use std::{
    fs,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};
static NEXT: AtomicU64 = AtomicU64::new(0);
fn directory() -> std::path::PathBuf {
    let p = std::env::temp_dir().join(format!(
        "tauto-javascript-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(&p).unwrap();
    p
}
fn compare(source: &str) {
    let program = tauto::surface::parse_program(source).unwrap();
    let reference = tauto::eval::run_program_with(&program, 1_000_000, Default::default()).unwrap();
    let expected = reference
        .outputs
        .iter()
        .map(|(n, v)| format!("{n} = {v}\n"))
        .collect::<String>();
    let pkg = tauto_nir::compile(source).unwrap();
    let js = tauto_jsgen::generate(&pkg).unwrap();
    let dir = directory();
    fs::write(dir.join("program.mjs"), js).unwrap();
    fs::write(
        dir.join("main.mjs"),
        "import {run} from './program.mjs';await run();",
    )
    .unwrap();
    let out = Command::new("node")
        .arg(dir.join("main.mjs"))
        .output()
        .expect("node is required for JavaScript backend tests");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8(out.stdout).unwrap(), expected, "{source}");
    fs::remove_dir_all(dir).unwrap();
}
#[test]
fn cli_build_run_and_errors() {
    let dir = directory();
    let input = dir.join("input.taut");
    let output = dir.join("out");
    fs::write(&input, &r#"perform show("n", 42)"#.to_string()).unwrap();
    for command in ["build", "run"] {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args([command, "--backend", "javascript", "-o"])
            .arg(&output)
            .arg(&input)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        if command == "run" {
            assert_eq!(String::from_utf8(out.stdout).unwrap(), "n = 42\n");
        }
    }
    fs::write(
        &input,
        &r#"perform show("n", 9223372036854775807 + 1)"#.to_string(),
    )
    .unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["run", "--backend", "javascript", "-o"])
        .arg(&output)
        .arg(&input)
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("the number is too large"));
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["build", "--backend", "typo"])
        .arg(&input)
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2));
    fs::remove_dir_all(dir).unwrap();
}

fn run_host(source: &str, host: &str) -> std::process::Output {
    let pkg = tauto_nir::compile(source).unwrap();
    let dir = directory();
    fs::write(
        dir.join("program.mjs"),
        tauto_jsgen::generate(&pkg).unwrap(),
    )
    .unwrap();
    fs::write(
        dir.join("main.mjs"),
        format!("import {{run}} from './program.mjs';\n{host}"),
    )
    .unwrap();
    let out = Command::new("node")
        .arg(dir.join("main.mjs"))
        .output()
        .unwrap();
    fs::remove_dir_all(dir).unwrap();
    out
}

#[test]
fn async_extern_resumes_inside_handler() {
    let out = run_host(
        r#"extern { fn delayed(n: i64): i64 }
effect ask(): i64 resume 1
let x := handle { delayed(40) + perform ask() } with { ask(), k => k(2) }
perform show("x", x)"#,
        "await run(console.log, { delayed: n => new Promise(resolve => setTimeout(() => resolve(n), 5)) });",
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "x = 42\n");
}

#[test]
fn async_extern_in_multi_shot_continuation() {
    let out = run_host(
        r#"extern { fn delayed(n: i64): i64 }
effect choose(): Bool resume ω
let x := handle { delayed(if perform choose() { 10 } else { 20 }) } with {
  choose(), k => k(true) + k(false)
}
perform show("x", x)"#,
        "let calls=0; await run(console.log, { delayed: async n => { calls++; await Promise.resolve(); return n; } }); if(calls!==2)throw new Error('expected two calls');",
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "x = 30\n");
}

#[test]
fn async_extern_rejection_propagates() {
    let out = run_host(
        r#"extern { fn delayed(n: i64): i64 }
perform show("x", delayed(1))"#,
        "const error = new Error('host failure'); try { await run(console.log,{delayed: async () => {throw error;}}); process.exitCode=2; } catch(e) { if(e!==error)throw e; console.log(e.message); }",
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "host failure\n");
}

#[test]
fn deep_recursion_uses_trampoline() {
    let out = run_host(
        &r#"fn count(n: i64): i64 ! {Div} { if n == 0 { 0 } else { count(n - 1) + 1 } }
perform show("n", count(20000))"#
            .to_string(),
        "await run();",
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "n = 20000\n");
}

#[test]
fn generation_modes_and_invalid_combinations() {
    let dir = directory();
    let input = dir.join("input.taut");
    fs::write(&input, r#"perform show("n", 42)"#).unwrap();
    for target in ["node", "browser"] {
        let output = dir.join(target);
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(["build", "--emit", "javascript", "--target", target, "-o"])
            .arg(&output)
            .arg(&input)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let entry = fs::read_to_string(output.join("main.mjs")).unwrap();
        assert_eq!(entry.contains("process."), target == "node");
        assert!(entry.contains("await run(console.log,externs,"));
        let out = Command::new("node")
            .arg(output.join("main.mjs"))
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(String::from_utf8(out.stdout).unwrap(), "n = 42\n");
    }
    for args in [
        vec!["run", "--backend", "javascript", "--target", "browser"],
        vec!["build", "--backend", "javascript", "--target", "invalid"],
        vec!["build", "--backend", "rust", "--target", "node"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(args)
            .arg(&input)
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(2));
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn direct_handler_cannot_silently_suspend() {
    let out = run_host(
        r#"extern { fn delayed(n: i64): i64 }
effect ask(): i64 direct
let n := handle { perform ask() } with { ask(), k => k(delayed(1)) }
perform show("n", n)"#,
        "try { await run(console.log,{delayed: async n=>n}); process.exitCode=2; } catch(e) { if(!e.message.includes('direct handler cannot await'))throw e; }",
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn declaration_output_is_opt_in_and_matches_esm_entry_points() {
    let dir = directory();
    let input = dir.join("input.taut");
    fs::write(&input, r#"perform show("n", 42)"#).unwrap();
    for target in ["node", "browser"] {
        for enabled in [false, true] {
            let output = dir.join(format!("{target}-{enabled}"));
            let mut command = Command::new(env!("CARGO_BIN_EXE_tauto"));
            command
                .args(["build", "--emit", "javascript", "--target", target, "-o"])
                .arg(&output);
            if enabled {
                command.arg("--declarations");
            }
            let result = command.arg(&input).output().unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            assert_eq!(output.join("program.d.mts").exists(), enabled);
            assert_eq!(output.join("main.d.mts").exists(), enabled);
            if enabled {
                let types = fs::read_to_string(output.join("program.d.mts")).unwrap();
                assert!(types.contains("export declare function run("));
                assert!(types.contains("): Promise<null>;"));
                assert_eq!(
                    fs::read_to_string(output.join("main.d.mts")).unwrap(),
                    "export {};\n"
                );
                // An opt-out rebuild cannot leave stale type signatures beside new code.
                let rebuilt = Command::new(env!("CARGO_BIN_EXE_tauto"))
                    .args(["build", "--backend", "javascript", "--target", target, "-o"])
                    .arg(&output)
                    .arg(&input)
                    .output()
                    .unwrap();
                assert!(
                    rebuilt.status.success(),
                    "{}",
                    String::from_utf8_lossy(&rebuilt.stderr)
                );
                assert!(!output.join("program.d.mts").exists());
                assert!(!output.join("main.d.mts").exists());
            }
            let result = Command::new("node")
                .arg(output.join("main.mjs"))
                .output()
                .unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            assert_eq!(String::from_utf8(result.stdout).unwrap(), "n = 42\n");
        }
    }
    for args in [
        vec!["build", "--backend", "rust", "--declarations"],
        vec!["run", "--backend", "javascript", "--declarations"],
    ] {
        let result = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(args)
            .arg(&input)
            .output()
            .unwrap();
        assert_eq!(result.status.code(), Some(2));
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn declarations_describe_async_host_and_adapted_callback_values() {
    let source = r#"extern { fn host(n: i64, callback: (i64) -> i64): i64 }
fn increment(n: i64): i64 { n + 1 }
perform show("answer", host(40, increment))"#;
    let pkg = tauto_nir::compile_javascript(source).unwrap();
    let declarations = tauto_jsgen::generate_declarations(&pkg).unwrap();
    assert!(declarations.contains("\"host\": (arg0: bigint, arg1: ((arg0: bigint) => bigint | Promise<bigint>)) => bigint | PromiseLike<bigint>"));
    let out = run_host(
        source,
        "await run(console.log, {host: async (n, callback) => (await callback(n)) + 1n});",
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "answer = 42\n");
}
