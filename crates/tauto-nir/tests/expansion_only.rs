//! A library leaves out what belongs to the expansion of macros, and a program
//! that runs cannot call what only the expander answers.

use tauto_nir::{CompileError, Package, compile_loaded_with_observer};

const MACRO: &str = r#"import std::Base
import std::prelude::Macro
import std::List

fn gvar(name: Text): SynExpr { ExVar(Syn::global(name)) }

fn helper(): SynExpr { gvar("Nil") }

pub macro fn keep(e: SynExpr, s: SynStmt): List(SynStmt) ! {macro_error, Div} {
  let _ := helper()
  Cons(s, Nil)
}
"#;

const USE: &str = r#"import std::Base

@keep!(1) => replace fn one
fn one(): u64 { 1 }

fn two(): u64 { one() + 1 }
"#;

fn compile(main: &str, lib: bool) -> Result<Package, CompileError> {
    let dir = std::env::temp_dir().join(format!(
        "tauto-nir-expansion-only-{}-{lib}-{}",
        std::process::id(),
        main.len()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("mac.taut"), MACRO).unwrap();
    std::fs::write(
        dir.join("main.taut"),
        format!("import \"mac.taut\"\n{main}"),
    )
    .unwrap();
    let loaded = tauto::program::load_extracted(&dir.join("main.taut")).expect("the program loads");
    let compiled = compile_loaded_with_observer(&loaded, lib, false, |_| {});
    std::fs::remove_dir_all(&dir).ok();
    compiled
}

#[test]
fn a_library_does_not_export_the_helpers_of_a_macro() {
    let package = compile(USE, true).expect("the library compiles");
    let exports: Vec<&str> = package.exports.iter().map(|e| e.name.as_str()).collect();
    assert!(
        exports.contains(&"one") && exports.contains(&"two"),
        "{exports:?}"
    );
    for helper in ["gvar", "helper", "keep"] {
        assert!(!exports.contains(&helper), "{helper} exported: {exports:?}");
    }
}

#[test]
fn a_program_that_runs_cannot_call_syn_global() {
    let main = format!("{USE}\nlet _ := gvar(\"Nil\")\n");
    match compile(&main, false) {
        Err(CompileError::Unsupported(u)) => {
            assert_eq!(u.what.id, "nir-expansion-only-extern", "{:?}", u.what)
        }
        Err(e) => panic!("another error: {e}"),
        Ok(_) => panic!("compiled"),
    }
}
