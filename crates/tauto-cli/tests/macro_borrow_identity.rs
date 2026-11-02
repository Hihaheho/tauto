//! Imported quoted calls retain the ownership mode of their own arguments.
use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!("tauto-macro-borrow-{}", std::process::id()));
        fs::create_dir_all(root.join("support/src")).unwrap();
        fs::create_dir_all(root.join("app/src")).unwrap();
        Self(root)
    }
    fn write(&self, name: &str, text: &str) {
        fs::write(self.0.join(name), text).unwrap();
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn successful(output: Output) -> String {
    assert!(
        output.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn nested_repeated_and_generic_quoted_borrows_agree_in_all_backends() {
    let f = Fixture::new();
    f.write("support/Tauto.eure", "package { name = \"support\" }\n");
    f.write(
        "app/Tauto.eure",
        "package { name = \"consumer\" }\ndependencies { support { path = \"../support\" } }\n",
    );
    f.write(
        "support/src/lib.tauto",
        &r#"
import std::prelude::Classes
import std::prelude::Macro

pub(open) enum Item { Item(Text) }
pub fn inspect(item: Item): u64 { match item { Item(text) => Text::len(text) } }
pub fn forward(item: Item, read: () -> Text): u64 { inspect(item) + Text::len(read()) }
pub macro fn example(expr: SynExpr): SynExpr {
    let read := quote { { let value := $expr; ToText::to_text(&value) } }
    quote { forward(Item("hello"), () => $read) }
}
pub macro fn named(expr: SynExpr): SynExpr {
    let read := quote { { let value := $expr; ToText::to_text(&value) } }
    quote { { let item := Item("hello"); forward(item, () => $read) } }
}
pub macro fn twice(expr: SynExpr): SynExpr { quote { Pair { fst: $expr, snd: $expr } } }
pub fn identity<A: Shared>(&value: A): A { value }
pub macro fn generic_example(expr: SynExpr): SynExpr {
    let read := quote { { let value := $expr; let r#copy := identity(&value); ToText::to_text(&r#copy) } }
    quote { forward(Item("hello"), () => $read) }
}
pub macro fn keep(code: Judgement): SynExpr { Judgement::term(code) }
"#.to_string(),
    );
    f.write(
        "app/src/main.tauto",
        &r#"
import std::prelude::Classes
import support::lib

perform show("direct", example!("hello"))
perform show("repeated", example!("world"))
perform show("nested", example!(example!("hello")))
let pair := twice!(example!("hello"))
perform show("duplicated", pair.fst + pair.snd)
perform show("integer", example!(7))
perform show("generic", generic_example!("hello"))
perform show("named", named!("hello"))
perform show("typed", keep!(example!("hello")))
let typed_pair := twice!(keep!(example!("hello")))
perform show("typed_duplicated", typed_pair.fst + typed_pair.snd)
"#
        .to_string(),
    );
    let expected = "direct = 10\nrepeated = 10\nnested = 7\nduplicated = 20\ninteger = 6\ngeneric = 10\nnamed = 10\ntyped = 10\ntyped_duplicated = 20\n";
    let loaded = tauto_build::tote_program(&f.0.join("app")).unwrap();
    let reference =
        tauto::eval::run_program_with(&loaded.program, 1_000_000, Default::default()).unwrap();
    let reference = reference
        .outputs
        .iter()
        .map(|(name, value)| format!("{name} = {value}\n"))
        .collect::<String>();
    assert_eq!(reference, expected);
    for javascript in [false, true] {
        let package =
            tauto_nir::compile_loaded_with_observer(&loaded, false, javascript, |_| {}).unwrap();
        let mut forward = 0;
        for function in &package.fns {
            function.body.walk(&mut |expr| {
                if let tauto_nir::ExprKind::Call(call) = &expr.kind
                    && let tauto_nir::Callee::Inst(inst) = call.callee
                    && package.fns[inst].source == "forward"
                {
                    assert!(!matches!(
                        call.args[0].kind,
                        tauto_nir::ExprKind::TempRef(_)
                    ));
                    forward += 1;
                }
            });
        }
        assert!(forward >= 7);
    }
    successful(
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(["build", "--emit", "javascript", "-o"])
            .arg(f.0.join("javascript"))
            .arg(f.0.join("app"))
            .output()
            .unwrap(),
    );
    assert_eq!(
        successful(
            Command::new("node")
                .arg(f.0.join("javascript/main.mjs"))
                .output()
                .unwrap()
        ),
        expected
    );
    let native = successful(
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(["build", "-o"])
            .arg(f.0.join("rust"))
            .arg(f.0.join("app"))
            .env("CARGO_NET_OFFLINE", "true")
            .output()
            .unwrap(),
    );
    assert_eq!(
        successful(Command::new(native.trim()).output().unwrap()),
        expected
    );
}
