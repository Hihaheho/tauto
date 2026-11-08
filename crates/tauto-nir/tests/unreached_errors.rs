//! A build generates only what its roots reach, so the checks of generating
//! answer only for that: a function nothing reaches does not stop the build,
//! and the same function stops it once something calls it.

use tauto_nir::compile_with;

const SPIN: &str = r#"struct Holder { call: () -> i64 ! {} }
fn spin(): i64 ! {} {
  let holder := Holder { call: spin }
  holder.call()
}
"#;

const MESSAGE: &str = "a function value may perform Div but its type permits {}";

#[test]
fn an_unreached_function_does_not_stop_the_build() {
    let source = format!("{SPIN}let r := 1\n");
    let package = compile_with(&source, false).unwrap_or_else(|e| panic!("{e:?}"));
    assert!(package.fns.iter().all(|f| f.source.as_str() != "spin"));
}

#[test]
fn a_reached_function_keeps_its_error() {
    let source = format!("{SPIN}let r := spin()\n");
    let error = format!("{:?}", compile_with(&source, false).unwrap_err());
    assert!(error.contains(MESSAGE), "{error}");
}

#[test]
fn a_library_exports_reach_every_function() {
    let error = format!("{:?}", compile_with(SPIN, true).unwrap_err());
    assert!(error.contains(MESSAGE), "{error}");
}
