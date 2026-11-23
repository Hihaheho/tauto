//! A build answers to the same checks as `tauto check`: a function whose row
//! does not hold stops the build whether or not anything reaches it.

use tauto::nir::compile_with;

const SPIN: &str = r#"struct Holder { call: () -> i64 ! {} }
fn spin(): i64 ! {} {
  let holder := Holder { call: spin }
  holder.call()
}
"#;

const MESSAGE: &str = "a function value may perform div but its type permits {}";

#[test]
fn an_unreached_function_keeps_its_error() {
    tauto_messages::install();
    let source = format!("{SPIN}let r := 1\n");
    let error = format!("{:?}", compile_with(&source, false).unwrap_err());
    assert!(error.contains(MESSAGE), "{error}");
}

#[test]
fn a_reached_function_keeps_its_error() {
    tauto_messages::install();
    let source = format!("{SPIN}let r := spin()\n");
    let error = format!("{:?}", compile_with(&source, false).unwrap_err());
    assert!(error.contains(MESSAGE), "{error}");
}

#[test]
fn a_library_exports_reach_every_function() {
    tauto_messages::install();
    let error = format!("{:?}", compile_with(SPIN, true).unwrap_err());
    assert!(error.contains(MESSAGE), "{error}");
}
