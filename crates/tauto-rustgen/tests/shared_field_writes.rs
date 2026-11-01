//! A write through a field the Rust backend keeps behind an `Rc` unshares
//! the field first: it compiles, and a value that shared the field before
//! the write keeps what it had, as the evaluator says.
use std::process::Command;
use tauto_rustgen::{Bindings, Options, Sources, workspace};

#[test]
fn a_write_through_a_shared_field_reaches_only_its_own_value() {
    tauto_messages::install();
    let source = r#"struct Big { a: Text, b: Text, c: Text, d: Text }
struct State { origin: Text, big: Big }
fn set_to<A>(&mut slot: A, value: A): Unit { slot := value }
fn rename(&mut state: State, name: Text): Unit {
  set_to(&mut state.big.a, name)
}
var state := State { origin: "o", big: Big { a: "a", b: "b", c: "c", d: "d" } }
let kept := state
rename(&mut state, "z")
perform show("kept", kept.big.a)
perform show("state", state.big.a)
"#;
    let expected = "kept = \"a\"\nstate = \"z\"\n";
    let evaluated = tauto::eval::run(source)
        .unwrap()
        .outputs
        .into_iter()
        .map(|(name, value)| format!("{name} = {value}\n"))
        .collect::<String>();
    assert_eq!(evaluated, expected, "evaluator");
    let package = tauto_nir::compile(source).unwrap();
    let st = package.datas.iter().find(|d| d.name == "State").unwrap();
    assert!(
        st.ctors[0]
            .fields
            .iter()
            .any(|f| f.indirect == tauto_nir::Indirect::Shared),
        "the fixture no longer has a shared field"
    );
    let ws = workspace(
        "shared-field-writes",
        &package,
        &Sources {
            file: "main.taut",
            text: source,
        },
        &Bindings::default(),
        &Options::default(),
    );
    let root =
        std::env::temp_dir().join(format!("tauto-shared-field-writes-{}", std::process::id()));
    let binary = ws
        .build(
            "shared-field-writes",
            &root.join("generated"),
            &root.join("target"),
            false,
        )
        .unwrap();
    let output = Command::new(binary).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
    std::fs::remove_dir_all(root).unwrap();
}
