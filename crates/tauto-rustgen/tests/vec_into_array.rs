use std::path::Path;
use std::process::Command;
use tauto_rustgen::{Bindings, Options, Sources, workspace};

/// Builds `name` as an example of the generated package with Cargo, so the
/// runtime gets the dependencies its generated manifest declares.
fn build_example(dir: &Path, name: &str, release: bool) -> std::path::PathBuf {
    let mut cmd = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()));
    cmd.args(["build", "--quiet", "--example", name, "--manifest-path"])
        .arg(dir.join("Cargo.toml"))
        .env("CARGO_TARGET_DIR", dir.join("target"))
        .env("CARGO_BUILD_BUILD_DIR", dir.join("target"));
    if release {
        cmd.arg("--release");
    }
    let output = cmd.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let profile = if release { "release" } else { "debug" };
    dir.join("target").join(profile).join("examples").join(name)
}

#[test]
fn conversion_checks_and_lowers_without_a_list() {
    let source = &r#"
fn freeze(values: Vec(u64)): Array(u64) { Vec::into_array(values) }
var values := Vec::new()
Vec::push(&mut values, "日本語")
Vec::push(&mut values, "two")
let array := Vec::into_array(values)
perform show("length", Array::len(array))
perform show("first", Array::get(array, 0))
perform show("second", Array::get(array, 1))
perform show("missing", Array::get(array, 2))
let empty: Array(i64) := Vec::into_array(Vec::new())
perform show("empty", Array::len(empty))
"#
    .to_string();
    let pkg = tauto_nir::compile_with(source, true).unwrap();
    let output = tauto::eval::run(source).unwrap().outputs;
    assert_eq!(output.len(), 5);
    assert_eq!(output[0].1, "2");
    assert_eq!(output[1].1, "Some(\"日本語\")");
    assert_eq!(output[2].1, "Some(\"two\")");
    assert_eq!(output[3].1, "None");
    assert_eq!(output[4].1, "0");
    let ws = workspace(
        "vec-array",
        &pkg,
        &Sources {
            file: "main.taut",
            text: source,
        },
        &Bindings::default(),
        &Options::default(),
    );
    // The native call is to the flat runtime conversion, not a generated List helper.
    let (_, native) = ws
        .files
        .iter()
        .find(|(name, _)| name == "src/lib.rs")
        .unwrap();
    let compact: String = native.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(compact.contains("tauto_rt::stdlib::vec_into_array"));
    let dir = std::env::temp_dir().join(format!("tauto-vec-array-{}", std::process::id()));
    ws.write(&dir).unwrap();
    std::fs::create_dir_all(dir.join("examples")).unwrap();
    std::fs::write(
        dir.join("examples/caller.rs"),
        r#"
use vec_array as generated;
fn main() {
    generated::run();
    std::thread::Builder::new().stack_size(2 * 1024 * 1024).spawn(|| {
        let a = generated::api::freeze((0..100_000_u64).collect());
        assert_eq!(a.len(), 100_000);
        assert_eq!(a[99_999], 99_999);
        let shared = a.clone();
        drop(a);
        assert_eq!(shared[0], 0);
        drop(shared);
    }).unwrap().join().unwrap();
}
"#,
    )
    .unwrap();
    let caller = build_example(&dir, "caller", false);
    let output = Command::new(caller).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout.clone()).unwrap(),
        "length = 2\nfirst = Some(\"日本語\")\nsecond = Some(\"two\")\nmissing = None\nempty = 0\n"
    );
    let javascript = tauto_jsgen::generate(&pkg).unwrap();
    std::fs::write(
        dir.join("program.mjs"),
        format!("{javascript}\nawait run();\n"),
    )
    .unwrap();
    let js = Command::new("node")
        .arg(dir.join("program.mjs"))
        .output()
        .unwrap();
    assert!(
        js.status.success(),
        "{}",
        String::from_utf8_lossy(&js.stderr)
    );
    assert_eq!(js.stdout, output.stdout);
    std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn conversion_consumes_the_vec_and_requires_shared_elements() {
    for source in [
        &r#"var v := Vec::new()
Vec::push(&mut v, 1)
let &slice := Vec::as_slice(&v)
let a := Vec::into_array(v)
perform show("length", Slice::len(&slice))"#
            .to_string(),
        &r#"var v := Vec::new()
Vec::push(&mut v, 1)
let a := Vec::into_array(v)
perform show("length", Vec::len(&v))"#
            .to_string(),
        &r#"var v := Vec::new()
Vec::push(&mut v, Buf::of("x"))
let a := Vec::into_array(v)"#
            .to_string(),
    ] {
        for result in [
            tauto_nir::compile(source),
            tauto_nir::compile_javascript(source),
        ] {
            let error = result
                .err()
                .expect("invalid ownership or element kind must be rejected");
            assert!(!error.to_string().contains("syntax error"), "{error}");
            assert!(!error.to_string().contains("unknown"), "{error}");
        }
    }
}
