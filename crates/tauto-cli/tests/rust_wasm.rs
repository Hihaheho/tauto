//! `tauto build --backend rust --target wasm32-*` (`docs/design/rust-backend.md`,
//! `docs/design/host-effects.md`): the generated crate and tauto-rt built for
//! wasm32. Needs the `wasm32-wasip1` and `wasm32-unknown-unknown` Rust targets
//! and node (whose `node:wasi` is the WASI host of the test).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn temp(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tauto-rust-wasm-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    d
}

fn build(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .arg("build")
        .args(args)
        .current_dir(dir)
        .env("TAUTO_TARGET_DIR", dir.join("target"))
        .output()
        .unwrap()
}

const PROGRAM: &str = r#"import std::prelude::Os

print("hello\n")
let c := read_file("data.txt")
perform show("c", c)
perform show("a", perform argv())
eprint("err")
perform exit(3)
"#;

/// Runs a WASI module with node, the directory of the test as its `.`.
const WASI_RUNNER: &str = r#"
import { WASI } from 'node:wasi';
import fs from 'node:fs';
const wasi = new WASI({ version: 'preview1', args: ['main', ...process.argv.slice(3)], preopens: { '.': '.' }, returnOnExit: true });
const module = await WebAssembly.compile(fs.readFileSync(process.argv[2]));
const instance = await WebAssembly.instantiate(module, wasi.getImportObject());
process.exitCode = wasi.start(instance);
"#;

#[test]
fn a_wasip1_module_asks_the_wasi_host_within_its_permissions() {
    let d = temp("wasip1");
    fs::write(d.join("main.taut"), PROGRAM).unwrap();
    fs::write(d.join("data.txt"), "inside").unwrap();
    fs::write(d.join("run.mjs"), WASI_RUNNER).unwrap();
    let out = build(
        &d,
        &[
            "--backend",
            "rust",
            "--target",
            "wasm32-wasip1",
            "main.taut",
        ],
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let wasm = String::from_utf8(out.stdout).unwrap().trim().to_string();
    assert!(wasm.ends_with("wasm32-wasip1/debug/main.wasm"), "{wasm}");
    let run = |args: &[&str]| {
        Command::new("node")
            .args(["--no-warnings", "run.mjs", &wasm])
            .args(args)
            .current_dir(&d)
            .output()
            .unwrap()
    };
    let granted = run(&["--allow-read", "--", "x"]);
    assert_eq!(
        String::from_utf8_lossy(&granted.stdout),
        "hello\nc = Ok(\"inside\")\na = Cons(\"x\", Nil)\n"
    );
    assert_eq!(String::from_utf8_lossy(&granted.stderr), "err");
    assert_eq!(granted.status.code(), Some(3));
    // The WASI host could read the file; the permission still decides.
    let denied = run(&[]);
    assert!(
        String::from_utf8_lossy(&denied.stderr)
            .starts_with("the program needs --allow-read to run; the host denies it by default\n"),
        "{}",
        String::from_utf8_lossy(&denied.stderr)
    );
    assert!(denied.stdout.is_empty());
    assert_ne!(denied.status.code(), Some(0));
}

#[test]
fn an_unknown_unknown_module_imports_nothing() {
    let d = temp("unknown");
    fs::write(d.join("main.taut"), PROGRAM).unwrap();
    let out = build(
        &d,
        &[
            "--backend",
            "rust",
            "--target",
            "wasm32-unknown-unknown",
            "main.taut",
        ],
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let wasm = String::from_utf8(out.stdout).unwrap().trim().to_string();
    // Every standard effect goes through `tauto_rt::host`: without an
    // embedder's host the module has no way out.
    let imports = Command::new("node")
        .args([
            "-e",
            "const m = new WebAssembly.Module(require('fs').readFileSync(process.argv[1])); console.log(WebAssembly.Module.imports(m).length)",
            &wasm,
        ])
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&imports.stdout).trim(), "0");
}

#[test]
fn what_wasm32_lacks_is_refused_before_cargo_runs() {
    let d = temp("refused");
    fs::write(
        d.join("main.taut"),
        "import std::prelude::Os\n\nperform show(\"r\", http_get(\"https://example.com/\"))\n",
    )
    .unwrap();
    let out = build(
        &d,
        &[
            "--backend",
            "rust",
            "--target",
            "wasm32-wasip1",
            "main.taut",
        ],
    );
    assert!(!out.status.success());
    assert!(
        String::from_utf8_lossy(&out.stderr)
            .contains("the wasm32-wasip1 target does not support the net effect"),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    for args in [
        &["--backend", "rust", "--target", "node", "main.taut"][..],
        &[
            "--backend",
            "javascript",
            "--target",
            "wasm32-wasip1",
            "main.taut",
        ][..],
    ] {
        let out = build(&d, args);
        assert_eq!(out.status.code(), Some(2), "{args:?}");
    }
}
