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
import std::builtin::classes
import std::builtin::macro

pub(open) enum Item { Entry(Text) }
pub fn inspect(item: Item): u64 { match item { Entry(text) => Text::len(text) } }
pub fn forward(item: Item, read: () -> Text): u64 { inspect(item) + Text::len(read()) }
pub macro fn example(expr: SynExpr): SynExpr {
    let read := quote { { let value := $expr; ToText::to_text(&value) } }
    quote { forward(Entry("hello"), () => $read) }
}
pub macro fn named(expr: SynExpr): SynExpr {
    let read := quote { { let value := $expr; ToText::to_text(&value) } }
    quote { { let item := Entry("hello"); forward(item, () => $read) } }
}
pub macro fn twice(expr: SynExpr): SynExpr { quote { #($expr, $expr) } }
pub fn identity<A: Shared>(value: &A): A { value }
pub macro fn generic_example(expr: SynExpr): SynExpr {
    let read := quote { { let value := $expr; let r#copy := identity(&value); ToText::to_text(&r#copy) } }
    quote { forward(Entry("hello"), () => $read) }
}
pub macro fn keep(code: Judgement): SynExpr { Judgement::term(code) }
"#.to_string(),
    );
    f.write(
        "app/src/main.tauto",
        &r#"
import std::builtin::classes
import support::lib

show(&(example!("hello")))
show(&(example!("world")))
show(&(example!(example!("hello"))))
let pair := twice!(example!("hello"))
show(&(pair.fst + pair.snd))
show(&(example!(7)))
show(&(generic_example!("hello")))
show(&(named!("hello")))
show(&(keep!(example!("hello"))))
let typed_pair := twice!(keep!(example!("hello")))
show(&(typed_pair.fst + typed_pair.snd))
"#
        .to_string(),
    );
    let expected = "10\n10\n7\n20\n6\n10\n10\n10\n20\n";
    let loaded = tauto_build::tote_program(&f.0.join("app")).unwrap();
    let reference =
        tauto::exec::run_loaded_with(&loaded, 1_000_000, Default::default()).unwrap();
    let reference = reference
        .outputs
        .iter()
        .map(|(name, value)| format!("{name} = {value}\n"))
        .collect::<String>();
    assert_eq!(reference, expected);
    for target in [tauto_nir::Target::Rust, tauto_nir::Target::JavaScript] {
        let package =
            tauto_nibcheck::lower::compile_loaded_with_observer(&loaded, false, target, |_| {}).unwrap();
        let mut forward = 0;
        for function in &package.fns {
            function.body.walk(&mut |expr| {
                if let tauto_nir::ExprKind::Call(call) = &expr.kind
                    && let tauto_nir::Callee::Inst(inst) = call.callee
                    && package.fns[inst].source.as_str() == "forward"
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
