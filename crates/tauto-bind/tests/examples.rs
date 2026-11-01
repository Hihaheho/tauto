//! The committed bindings of the examples are what `tauto bind` generates now
//! (`tauto bind --check`, `docs/design/rust-backend.md`).

use std::path::PathBuf;

fn example(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/rust")
        .join(name)
}

#[test]
fn regex_bindings_are_up_to_date() {
    tauto_messages::install();
    assert_eq!(
        tauto_bind::bind(&example("regex_demo"), "regex", None, true),
        Ok(true)
    );
}

#[test]
fn serde_json_bindings_are_up_to_date() {
    tauto_messages::install();
    assert_eq!(
        tauto_bind::bind(&example("json_demo"), "serde_json", None, true),
        Ok(true)
    );
}

#[test]
fn a_config_with_an_unknown_key_is_an_error() {
    tauto_messages::install();
    let e = tauto_bind::Config::parse("crate = \"x\"\nbogus = 1\n", "c.eure").unwrap_err();
    assert!(e.contains("unknown key `bogus`"), "{e}");
}

#[test]
fn a_config_needs_a_crate() {
    tauto_messages::install();
    let e = tauto_bind::Config::parse("items = []\n", "c.eure").unwrap_err();
    assert!(e.contains("`crate` is missing"), "{e}");
}
